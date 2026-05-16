/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2026 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "mcsat/na/mccormick.h"

#include <assert.h>
#include <gmp.h>
#include <stdint.h>

#include <poly/rational.h>

#include "api/yices_api_lock_free.h"
#include "context/context.h"
#include "mcsat/na/na_plugin_internal.h"
#include "mcsat/tracing.h"
#include "mcsat/value.h"
#include "terms/rba_buffer_terms.h"
#include "terms/term_manager.h"
#include "utils/int_hash_map.h"
#include "utils/memalloc.h"

#include "yices.h"

#define MCCORMICK_NO_CHECK UINT32_MAX

typedef enum {
  MCCORMICK_BOUND_LOWER,
  MCCORMICK_BOUND_UPPER,
  MCCORMICK_BOUND_EQUAL
} mccormick_bound_kind_t;

typedef struct {
  term_t term;
  bool has_lb;
  bool has_ub;
  rational_t lb;
  rational_t ub;
  term_t lb_assump;
  term_t ub_assump;
} mccormick_bound_t;

typedef struct {
  mccormick_t* mc;
  context_t* ctx;

  int_hmap_t product_to_lift;
  int_hmap_t assumption_to_literal;

  ivector_t assumptions;
  ivector_t active_products;

  int_hmap_t term_to_bound;
  mccormick_bound_t* bounds;
  uint32_t bounds_size;
  uint32_t bounds_capacity;
} mccormick_check_t;

static void mccormick_check_construct(mccormick_check_t* check, mccormick_t* mc) {
  ctx_config_t* config;

  check->mc = mc;

  config = yices_new_config();
  yices_set_config(config, "mode", "multi-checks");
  check->ctx = _o_yices_new_context(config);
  yices_free_config(config);

  init_int_hmap(&check->product_to_lift, 0);
  init_int_hmap(&check->assumption_to_literal, 0);
  init_ivector(&check->assumptions, 0);
  init_ivector(&check->active_products, 0);

  init_int_hmap(&check->term_to_bound, 0);
  check->bounds = NULL;
  check->bounds_size = 0;
  check->bounds_capacity = 0;
}

static void mccormick_bound_destruct(mccormick_bound_t* bound) {
  if (bound->has_lb) {
    q_clear(&bound->lb);
  }
  if (bound->has_ub) {
    q_clear(&bound->ub);
  }
}

static void mccormick_check_destruct(mccormick_check_t* check) {
  uint32_t i;

  for (i = 0; i < check->bounds_size; ++ i) {
    mccormick_bound_destruct(check->bounds + i);
  }
  safe_free(check->bounds);

  delete_int_hmap(&check->term_to_bound);
  delete_ivector(&check->active_products);
  delete_ivector(&check->assumptions);
  delete_int_hmap(&check->assumption_to_literal);
  delete_int_hmap(&check->product_to_lift);

  _o_yices_free_context(check->ctx);
}

static bool mccormick_is_degree2_product(term_table_t* terms, term_t product, term_t* x, term_t* y) {
  pprod_t* pprod;

  if (term_kind(terms, product) != POWER_PRODUCT) {
    return false;
  }

  pprod = pprod_term_desc(terms, product);
  if (pprod_degree(pprod) != 2) {
    return false;
  }

  if (pprod->len == 1 && pprod->prod[0].exp == 2) {
    *x = pprod->prod[0].var;
    *y = pprod->prod[0].var;
    return true;
  }

  if (pprod->len == 2 && pprod->prod[0].exp == 1 && pprod->prod[1].exp == 1) {
    *x = pprod->prod[0].var;
    *y = pprod->prod[1].var;
    return true;
  }

  return false;
}

static bool mccormick_factor_supported(term_table_t* terms, term_t t) {
  return is_arithmetic_term(terms, t) && term_degree(terms, t) <= 1;
}

static bool mccormick_product_supported(term_table_t* terms, term_t product) {
  term_t x, y;

  return mccormick_is_degree2_product(terms, product, &x, &y)
      && mccormick_factor_supported(terms, x)
      && mccormick_factor_supported(terms, y);
}

static term_t mccormick_get_lift(mccormick_check_t* check, term_t product) {
  int_hmap_pair_t* find;
  term_t lift;
  term_table_t* terms;

  find = int_hmap_find(&check->product_to_lift, product);
  if (find != NULL) {
    return find->val;
  }

  terms = check->mc->na->ctx->terms;
  lift = new_uninterpreted_term(terms, real_type(terms->types));
  int_hmap_add(&check->product_to_lift, product, lift);
  ivector_push(&check->active_products, product);

  if (ctx_trace_enabled(check->mc->na->ctx, "mcsat::na::mccormick")) {
    ctx_trace_printf(check->mc->na->ctx, "mccormick lift: ");
    ctx_trace_term(check->mc->na->ctx, product);
    ctx_trace_printf(check->mc->na->ctx, "  ->  ");
    ctx_trace_term(check->mc->na->ctx, lift);
  }

  return lift;
}

static term_t mccormick_mk_linear_term(mccormick_t* mc) {
  return mk_arith_term(mc->na->ctx->tm, &mc->buffer);
}

static term_t mccormick_mk_geq0(mccormick_t* mc) {
  return mk_arith_term_geq0(mc->na->ctx->tm, mccormick_mk_linear_term(mc));
}

static term_t mccormick_mk_eq0(mccormick_t* mc) {
  return mk_arith_term_eq0(mc->na->ctx->tm, mccormick_mk_linear_term(mc));
}

static bool mccormick_linearize_term(mccormick_check_t* check, term_t t, term_t* out) {
  mccormick_t* mc;
  term_table_t* terms;
  term_kind_t kind;
  uint32_t i;

  mc = check->mc;
  terms = mc->na->ctx->terms;
  kind = term_kind(terms, t);

  switch (kind) {
  case ARITH_CONSTANT:
    *out = t;
    return true;

  case POWER_PRODUCT:
    if (!mccormick_product_supported(terms, t)) {
      return false;
    }
    *out = mccormick_get_lift(check, t);
    return true;

  case ARITH_POLY: {
    polynomial_t* polynomial = poly_term_desc(terms, t);

    reset_rba_buffer(&mc->buffer);
    for (i = 0; i < polynomial->nterms; ++ i) {
      term_t mono_term = polynomial->mono[i].var;
      if (mono_term == const_idx) {
        rba_buffer_add_const(&mc->buffer, &polynomial->mono[i].coeff);
      } else if (term_kind(terms, mono_term) == POWER_PRODUCT) {
        term_t lift;
        if (!mccormick_product_supported(terms, mono_term)) {
          reset_rba_buffer(&mc->buffer);
          return false;
        }
        lift = mccormick_get_lift(check, mono_term);
        rba_buffer_add_const_times_term(&mc->buffer, terms, &polynomial->mono[i].coeff, lift);
      } else {
        if (!mccormick_factor_supported(terms, mono_term)) {
          reset_rba_buffer(&mc->buffer);
          return false;
        }
        rba_buffer_add_const_times_term(&mc->buffer, terms, &polynomial->mono[i].coeff, mono_term);
      }
    }
    *out = mccormick_mk_linear_term(mc);
    return true;
  }

  default:
    if (mccormick_factor_supported(terms, t)) {
      *out = t;
      return true;
    }
    return false;
  }
}

static bool mccormick_linearize_literal(mccormick_check_t* check, term_t literal, term_t* out) {
  mccormick_t* mc;
  term_table_t* terms;
  term_t atom, lhs, rhs, lin, lin_lhs, lin_rhs;
  bool negated;

  mc = check->mc;
  terms = mc->na->ctx->terms;
  atom = unsigned_term(literal);
  negated = atom != literal;

  switch (term_kind(terms, atom)) {
  case ARITH_GE_ATOM:
    if (!mccormick_linearize_term(check, arith_atom_arg(terms, atom), &lin)) {
      return false;
    }
    *out = mk_arith_term_geq0(mc->na->ctx->tm, lin);
    break;

  case ARITH_EQ_ATOM:
    if (!mccormick_linearize_term(check, arith_atom_arg(terms, atom), &lin)) {
      return false;
    }
    *out = mk_arith_term_eq0(mc->na->ctx->tm, lin);
    break;

  case ARITH_BINEQ_ATOM:
  case EQ_TERM:
    lhs = composite_term_arg(terms, atom, 0);
    rhs = composite_term_arg(terms, atom, 1);
    if (!is_arithmetic_term(terms, lhs) || !is_arithmetic_term(terms, rhs)) {
      return false;
    }
    if (!mccormick_linearize_term(check, lhs, &lin_lhs) ||
        !mccormick_linearize_term(check, rhs, &lin_rhs)) {
      return false;
    }
    reset_rba_buffer(&mc->buffer);
    rba_buffer_add_term(&mc->buffer, terms, lin_lhs);
    rba_buffer_sub_term(&mc->buffer, terms, lin_rhs);
    *out = mccormick_mk_eq0(mc);
    break;

  default:
    return false;
  }

  if (negated) {
    *out = opposite_term(*out);
  }
  return true;
}

static bool mccormick_extract_linear_bound_term(mccormick_t* mc, term_t t, term_t* var, rational_t* coeff, rational_t* constant) {
  term_table_t* terms;
  term_kind_t kind;

  terms = mc->na->ctx->terms;
  kind = term_kind(terms, t);

  q_init(coeff);
  q_init(constant);

  switch (kind) {
  case ARITH_CONSTANT:
    q_clear(coeff);
    q_clear(constant);
    return false;

  case ARITH_POLY: {
    polynomial_t* p = poly_term_desc(terms, t);
    uint32_t i;
    *var = NULL_TERM;
    for (i = 0; i < p->nterms; ++ i) {
      term_t mono = p->mono[i].var;
      if (mono == const_idx) {
        q_set(constant, &p->mono[i].coeff);
      } else {
        if (*var != NULL_TERM || !mccormick_factor_supported(terms, mono)) {
          q_clear(coeff);
          q_clear(constant);
          return false;
        }
        *var = mono;
        q_set(coeff, &p->mono[i].coeff);
      }
    }
    if (*var != NULL_TERM && q_is_nonzero(coeff)) {
      return true;
    }
    q_clear(coeff);
    q_clear(constant);
    return false;
  }

  default:
    if (mccormick_factor_supported(terms, t)) {
      *var = t;
      q_set_one(coeff);
      return true;
    }
    q_clear(coeff);
    q_clear(constant);
    return false;
  }
}

static bool mccormick_extract_bound(mccormick_t* mc, term_t literal, term_t* var, rational_t* value, mccormick_bound_kind_t* kind) {
  term_table_t* terms;
  term_t atom, arg, lhs, rhs;
  bool negated;
  rational_t coeff, constant;

  terms = mc->na->ctx->terms;
  atom = unsigned_term(literal);
  negated = atom != literal;

  q_init(value);

  switch (term_kind(terms, atom)) {
  case ARITH_GE_ATOM:
    arg = arith_atom_arg(terms, atom);
    if (!mccormick_extract_linear_bound_term(mc, arg, var, &coeff, &constant)) {
      q_clear(value);
      return false;
    }
    q_set_neg(value, &constant);
    q_div(value, &coeff);
    if (!negated) {
      *kind = q_is_pos(&coeff) ? MCCORMICK_BOUND_LOWER : MCCORMICK_BOUND_UPPER;
    } else {
      *kind = q_is_pos(&coeff) ? MCCORMICK_BOUND_UPPER : MCCORMICK_BOUND_LOWER;
    }
    q_clear(&coeff);
    q_clear(&constant);
    return true;

  case ARITH_EQ_ATOM:
    if (negated) {
      q_clear(value);
      return false;
    }
    arg = arith_atom_arg(terms, atom);
    if (!mccormick_extract_linear_bound_term(mc, arg, var, &coeff, &constant)) {
      q_clear(value);
      return false;
    }
    q_set_neg(value, &constant);
    q_div(value, &coeff);
    *kind = MCCORMICK_BOUND_EQUAL;
    q_clear(&coeff);
    q_clear(&constant);
    return true;

  case ARITH_BINEQ_ATOM:
  case EQ_TERM:
    if (negated) {
      q_clear(value);
      return false;
    }
    lhs = composite_term_arg(terms, atom, 0);
    rhs = composite_term_arg(terms, atom, 1);
    if (!is_arithmetic_term(terms, lhs) || !is_arithmetic_term(terms, rhs)) {
      q_clear(value);
      return false;
    }
    reset_rba_buffer(&mc->buffer);
    rba_buffer_add_term(&mc->buffer, terms, lhs);
    rba_buffer_sub_term(&mc->buffer, terms, rhs);
    arg = mccormick_mk_linear_term(mc);
    if (!mccormick_extract_linear_bound_term(mc, arg, var, &coeff, &constant)) {
      q_clear(value);
      return false;
    }
    q_set_neg(value, &constant);
    q_div(value, &coeff);
    *kind = MCCORMICK_BOUND_EQUAL;
    q_clear(&coeff);
    q_clear(&constant);
    return true;

  default:
    q_clear(value);
    return false;
  }
}

static mccormick_bound_t* mccormick_get_bound_slot(mccormick_check_t* check, term_t term) {
  int_hmap_pair_t* find;
  mccormick_bound_t* bound;
  uint32_t new_capacity;

  find = int_hmap_find(&check->term_to_bound, term);
  if (find != NULL) {
    return check->bounds + find->val;
  }

  if (check->bounds_size == check->bounds_capacity) {
    new_capacity = check->bounds_capacity == 0 ? 16 : check->bounds_capacity + check->bounds_capacity / 2;
    check->bounds = safe_realloc(check->bounds, new_capacity * sizeof(mccormick_bound_t));
    check->bounds_capacity = new_capacity;
  }

  bound = check->bounds + check->bounds_size;
  bound->term = term;
  bound->has_lb = false;
  bound->has_ub = false;
  bound->lb_assump = NULL_TERM;
  bound->ub_assump = NULL_TERM;

  int_hmap_add(&check->term_to_bound, term, check->bounds_size);
  check->bounds_size ++;

  return bound;
}

static void mccormick_add_bound(mccormick_check_t* check, term_t term, const rational_t* value, mccormick_bound_kind_t kind, term_t assump) {
  mccormick_bound_t* bound;

  bound = mccormick_get_bound_slot(check, term);

  if (kind == MCCORMICK_BOUND_LOWER || kind == MCCORMICK_BOUND_EQUAL) {
    if (!bound->has_lb) {
      q_init(&bound->lb);
      q_set(&bound->lb, value);
      bound->has_lb = true;
      bound->lb_assump = assump;
    } else if (q_lt(&bound->lb, value)) {
      q_set(&bound->lb, value);
      bound->lb_assump = assump;
    }
  }

  if (kind == MCCORMICK_BOUND_UPPER || kind == MCCORMICK_BOUND_EQUAL) {
    if (!bound->has_ub) {
      q_init(&bound->ub);
      q_set(&bound->ub, value);
      bound->has_ub = true;
      bound->ub_assump = assump;
    } else if (q_gt(&bound->ub, value)) {
      q_set(&bound->ub, value);
      bound->ub_assump = assump;
    }
  }
}

static mccormick_bound_t* mccormick_find_bound(mccormick_check_t* check, term_t term) {
  int_hmap_pair_t* find;

  find = int_hmap_find(&check->term_to_bound, term);
  return find == NULL ? NULL : check->bounds + find->val;
}

static term_t mccormick_add_assumption(mccormick_check_t* check, term_t literal, term_t linear_literal) {
  term_t assump;
  term_table_t* terms;

  terms = check->mc->na->ctx->terms;
  assump = new_uninterpreted_term(terms, bool_type(terms->types));

  int_hmap_add(&check->assumption_to_literal, assump, literal);
  ivector_push(&check->assumptions, assump);
  _o_yices_assert_formula(check->ctx, _o_yices_implies(assump, linear_literal));

  return assump;
}

static bool mccormick_scan_trail(mccormick_check_t* check) {
  mccormick_t* mc;
  const mcsat_trail_t* trail;
  variable_db_t* var_db;
  uint32_t i;
  bool has_relaxation_terms;

  mc = check->mc;
  trail = mc->na->ctx->trail;
  var_db = mc->na->ctx->var_db;
  has_relaxation_terms = false;

  for (i = 0; i < trail_size(trail); ++ i) {
    variable_t x = trail_at(trail, i);
    term_t literal, linear_literal, bound_term, assump;
    rational_t bound_value;
    mccormick_bound_kind_t bound_kind;

    if (!variable_db_is_boolean(var_db, x)) {
      continue;
    }

    literal = variable_db_get_term(var_db, x);
    if (mcsat_value_is_false(trail_get_value(trail, x))) {
      literal = opposite_term(literal);
    }

    if (!mccormick_linearize_literal(check, literal, &linear_literal)) {
      continue;
    }

    assump = mccormick_add_assumption(check, literal, linear_literal);
    has_relaxation_terms = true;

    if (mccormick_extract_bound(mc, literal, &bound_term, &bound_value, &bound_kind)) {
      mccormick_add_bound(check, bound_term, &bound_value, bound_kind, assump);
      q_clear(&bound_value);
    }
  }

  return has_relaxation_terms;
}

static void mccormick_add_term(rba_buffer_t* buffer, term_table_t* terms, const rational_t* coeff, term_t term) {
  rational_t tmp;

  if (q_is_zero(coeff)) {
    return;
  }

  q_init(&tmp);
  q_set(&tmp, coeff);
  rba_buffer_add_const_times_term(buffer, terms, &tmp, term);
  q_clear(&tmp);
}

static void mccormick_add_constant(rba_buffer_t* buffer, const rational_t* constant) {
  if (!q_is_zero(constant)) {
    rba_buffer_add_const(buffer, (rational_t*) constant);
  }
}

static term_t mccormick_make_envelope(mccormick_check_t* check,
                                      term_t lift, term_t x, term_t y,
                                      const rational_t* w_coeff,
                                      const rational_t* x_coeff,
                                      const rational_t* y_coeff,
                                      const rational_t* constant) {
  mccormick_t* mc;
  term_table_t* terms;

  mc = check->mc;
  terms = mc->na->ctx->terms;

  reset_rba_buffer(&mc->buffer);
  mccormick_add_term(&mc->buffer, terms, w_coeff, lift);
  mccormick_add_term(&mc->buffer, terms, x_coeff, x);
  mccormick_add_term(&mc->buffer, terms, y_coeff, y);
  mccormick_add_constant(&mc->buffer, constant);
  return mccormick_mk_geq0(mc);
}

static void mccormick_assert_guarded_envelope(mccormick_check_t* check, term_t guards[4], term_t envelope) {
  term_t guard;

  guard = _o_yices_and(4, guards);
  _o_yices_assert_formula(check->ctx, _o_yices_implies(guard, envelope));
  (*check->mc->stats.envelopes) ++;
}

static void mccormick_add_product_envelopes(mccormick_check_t* check, term_t product) {
  mccormick_t* mc;
  term_table_t* terms;
  term_t x, y, lift, guards[4], envelope;
  mccormick_bound_t* xb;
  mccormick_bound_t* yb;
  rational_t one, minus_one;
  rational_t nx_l, nx_u, ny_l, ny_u;
  rational_t c;

  mc = check->mc;
  terms = mc->na->ctx->terms;

  if (!mccormick_is_degree2_product(terms, product, &x, &y)) {
    return;
  }

  xb = mccormick_find_bound(check, x);
  yb = mccormick_find_bound(check, y);
  if (xb == NULL || yb == NULL || !xb->has_lb || !xb->has_ub || !yb->has_lb || !yb->has_ub) {
    return;
  }

  lift = mccormick_get_lift(check, product);
  guards[0] = xb->lb_assump;
  guards[1] = xb->ub_assump;
  guards[2] = yb->lb_assump;
  guards[3] = yb->ub_assump;

  q_init(&one);
  q_init(&minus_one);
  q_set_one(&one);
  q_set_minus_one(&minus_one);
  q_init(&nx_l);
  q_init(&nx_u);
  q_init(&ny_l);
  q_init(&ny_u);
  q_init(&c);

  q_set_neg(&nx_l, &xb->lb);
  q_set_neg(&nx_u, &xb->ub);
  q_set_neg(&ny_l, &yb->lb);
  q_set_neg(&ny_u, &yb->ub);

  /*
   * w >= lx*y + ly*x - lx*ly
   * w - ly*x - lx*y + lx*ly >= 0
   */
  q_set(&c, &xb->lb);
  q_mul(&c, &yb->lb);
  envelope = mccormick_make_envelope(check, lift, x, y, &one, &ny_l, &nx_l, &c);
  mccormick_assert_guarded_envelope(check, guards, envelope);

  /*
   * w >= ux*y + uy*x - ux*uy
   * w - uy*x - ux*y + ux*uy >= 0
   */
  q_set(&c, &xb->ub);
  q_mul(&c, &yb->ub);
  envelope = mccormick_make_envelope(check, lift, x, y, &one, &ny_u, &nx_u, &c);
  mccormick_assert_guarded_envelope(check, guards, envelope);

  /*
   * w <= ux*y + ly*x - ux*ly
   * -w + ly*x + ux*y - ux*ly >= 0
   */
  q_set(&c, &xb->ub);
  q_mul(&c, &yb->lb);
  q_neg(&c);
  envelope = mccormick_make_envelope(check, lift, x, y, &minus_one, &yb->lb, &xb->ub, &c);
  mccormick_assert_guarded_envelope(check, guards, envelope);

  /*
   * w <= lx*y + uy*x - lx*uy
   * -w + uy*x + lx*y - lx*uy >= 0
   */
  q_set(&c, &xb->lb);
  q_mul(&c, &yb->ub);
  q_neg(&c);
  envelope = mccormick_make_envelope(check, lift, x, y, &minus_one, &yb->ub, &xb->lb, &c);
  mccormick_assert_guarded_envelope(check, guards, envelope);

  q_clear(&c);
  q_clear(&ny_u);
  q_clear(&ny_l);
  q_clear(&nx_u);
  q_clear(&nx_l);
  q_clear(&minus_one);
  q_clear(&one);
}

static void mccormick_add_envelopes(mccormick_check_t* check) {
  uint32_t i;

  for (i = 0; i < check->active_products.size; ++ i) {
    mccormick_add_product_envelopes(check, check->active_products.data[i]);
  }
}

static void mccormick_hint_from_model(mccormick_check_t* check) {
  mccormick_t* mc;
  model_t* model;
  term_table_t* terms;
  const mcsat_trail_t* trail;
  variable_db_t* var_db;
  uint32_t i;

  mc = check->mc;
  terms = mc->na->ctx->terms;
  trail = mc->na->ctx->trail;
  var_db = mc->na->ctx->var_db;

  model = _o_yices_get_model(check->ctx, true);
  if (model == NULL) {
    return;
  }

  for (i = 0; i < check->active_products.size; ++ i) {
    term_t factors[2];
    uint32_t j;

    if (!mccormick_is_degree2_product(terms, check->active_products.data[i], factors, factors + 1)) {
      continue;
    }

    for (j = 0; j < 2; ++ j) {
      variable_t x;
      mpq_t q;
      lp_rational_t rat_value;
      lp_value_t lp_value;
      mcsat_value_t value;

      x = variable_db_get_variable_if_exists(var_db, factors[j]);
      if (x == variable_null || trail_has_value(trail, x)) {
        continue;
      }

      mc->na->ctx->hint_next_decision(mc->na->ctx, x);
      (*mc->stats.hints) ++;

      if (!trail_is_at_base_level(trail)) {
        continue;
      }

      mpq_init(q);
      if (_o_yices_get_mpq_value(model, factors[j], q) == 0) {
        lp_rational_construct(&rat_value);
        mpq_set(&rat_value, q);
        lp_value_construct(&lp_value, LP_VALUE_RATIONAL, &rat_value);
        mcsat_value_construct_lp_value(&value, &lp_value);
        mc->na->ctx->hint_value(mc->na->ctx, x, &value);
        mcsat_value_destruct(&value);
        lp_value_destruct(&lp_value);
        lp_rational_destruct(&rat_value);
      }
      mpq_clear(q);
    }
  }

  _o_yices_free_model(model);
}

void mccormick_construct(mccormick_t* mc, na_plugin_t* na) {
  mc->na = na;
  init_int_hset(&mc->registered_products, 0);
  init_ivector(&mc->conflict, 0);
  mc->checked_trail_size = MCCORMICK_NO_CHECK;
  mc->checked_decision_level = MCCORMICK_NO_CHECK;
  init_rba_buffer(&mc->buffer, na->ctx->terms->pprods);

  mc->stats.products = statistics_new_int(na->ctx->stats, "mcsat::na::mccormick::products");
  mc->stats.checks = statistics_new_int(na->ctx->stats, "mcsat::na::mccormick::checks");
  mc->stats.conflicts = statistics_new_int(na->ctx->stats, "mcsat::na::mccormick::conflicts");
  mc->stats.envelopes = statistics_new_int(na->ctx->stats, "mcsat::na::mccormick::envelopes");
  mc->stats.hints = statistics_new_int(na->ctx->stats, "mcsat::na::mccormick::hints");
}

void mccormick_destruct(mccormick_t* mc) {
  delete_rba_buffer(&mc->buffer);
  delete_ivector(&mc->conflict);
  delete_int_hset(&mc->registered_products);
}

void mccormick_register_term(mccormick_t* mc, term_t t) {
  term_table_t* terms;
  term_kind_t kind;
  uint32_t i;

  if (!mc->na->ctx->options->na_mccormick || !is_pos_term(t)) {
    return;
  }

  terms = mc->na->ctx->terms;
  kind = term_kind(terms, t);

  if (kind == POWER_PRODUCT) {
    if (mccormick_product_supported(terms, t) && int_hset_add(&mc->registered_products, (uint32_t) t)) {
      (*mc->stats.products) ++;
    }
  } else if (kind == ARITH_POLY) {
    polynomial_t* p = poly_term_desc(terms, t);
    for (i = 0; i < p->nterms; ++ i) {
      term_t mono = p->mono[i].var;
      if (mono != const_idx && term_kind(terms, mono) == POWER_PRODUCT &&
          mccormick_product_supported(terms, mono) &&
          int_hset_add(&mc->registered_products, (uint32_t) mono)) {
        (*mc->stats.products) ++;
      }
    }
  }
}

void mccormick_push(mccormick_t* mc) {
  mc->checked_trail_size = MCCORMICK_NO_CHECK;
  mc->checked_decision_level = MCCORMICK_NO_CHECK;
}

void mccormick_pop(mccormick_t* mc) {
  ivector_reset(&mc->conflict);
  mc->checked_trail_size = MCCORMICK_NO_CHECK;
  mc->checked_decision_level = MCCORMICK_NO_CHECK;
}

void mccormick_event_notify(mccormick_t* mc) {
  ivector_reset(&mc->conflict);
  mc->checked_trail_size = MCCORMICK_NO_CHECK;
  mc->checked_decision_level = MCCORMICK_NO_CHECK;
}

bool mccormick_check(mccormick_t* mc, trail_token_t* prop) {
  const mcsat_trail_t* trail;
  mccormick_check_t check;
  smt_status_t result;

  if (!mc->na->ctx->options->na_mccormick || mc->registered_products.nelems == 0) {
    return false;
  }

  trail = mc->na->ctx->trail;
  if (!trail_is_consistent(trail)) {
    return false;
  }

  if (mc->checked_trail_size == trail_size(trail) &&
      mc->checked_decision_level == trail->decision_level) {
    return false;
  }

  ivector_reset(&mc->conflict);

  mccormick_check_construct(&check, mc);
  if (!mccormick_scan_trail(&check) || check.active_products.size == 0) {
    mc->checked_trail_size = trail_size(trail);
    mc->checked_decision_level = trail->decision_level;
    mccormick_check_destruct(&check);
    return false;
  }

  mccormick_add_envelopes(&check);

  (*mc->stats.checks) ++;
  result = _o_yices_check_context_with_assumptions(check.ctx, NULL, check.assumptions.size, check.assumptions.data);

  mc->checked_trail_size = trail_size(trail);
  mc->checked_decision_level = trail->decision_level;

  if (result == YICES_STATUS_UNSAT) {
    uint32_t i;
    ivector_t core;
    init_ivector(&core, 0);
    context_build_unsat_core(check.ctx, &core);
    for (i = 0; i < core.size; ++ i) {
      int_hmap_pair_t* mapped = int_hmap_find(&check.assumption_to_literal, core.data[i]);
      if (mapped != NULL) {
        ivector_push(&mc->conflict, mapped->val);
      }
    }
    delete_ivector(&core);

    if (mc->conflict.size > 0) {
      if (ctx_trace_enabled(mc->na->ctx, "mcsat::na::mccormick")) {
        ctx_trace_printf(mc->na->ctx, "mccormick conflict:\n");
        for (i = 0; i < mc->conflict.size; ++ i) {
          ctx_trace_term(mc->na->ctx, mc->conflict.data[i]);
        }
      }
      prop->conflict(prop);
      (*mc->stats.conflicts) ++;
      mccormick_check_destruct(&check);
      return true;
    }
  } else if (result == YICES_STATUS_SAT) {
    mccormick_hint_from_model(&check);
  }

  mccormick_check_destruct(&check);
  return false;
}

bool mccormick_has_conflict(const mccormick_t* mc) {
  return mc->conflict.size > 0;
}

void mccormick_get_conflict(mccormick_t* mc, ivector_t* conflict) {
  ivector_swap(conflict, &mc->conflict);
  ivector_reset(&mc->conflict);
}
