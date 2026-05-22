/*
 * Native MCSAT floating-point plugin.
 */

#include "mcsat/fp/fp_plugin.h"

#include "mcsat/fp/fp_dyadic.h"
#include "mcsat/fp/fp_explain.h"
#include "mcsat/fp/fp_round.h"
#include "mcsat/fp/fp_value.h"
#include "mcsat/trail.h"
#include "mcsat/tracing.h"
#include "mcsat/value.h"

#include "terms/terms.h"
#include "utils/memalloc.h"

#include <assert.h>

typedef struct {
  plugin_t plugin_interface;
  plugin_context_t *ctx;
  term_manager_t *tm;
  ivector_t watched_terms;
  term_t conflict_literal;
} fp_plugin_t;

static void fp_plugin_construct(plugin_t *plugin, plugin_context_t *ctx) {
  fp_plugin_t *fp;

  fp = (fp_plugin_t *) plugin;
  fp->ctx = ctx;
  fp->tm = ctx->tm;
  fp->conflict_literal = NULL_TERM;
  init_ivector(&fp->watched_terms, 0);

  ctx->request_term_notification_by_kind(ctx, ROUNDING_MODE_CONSTANT, false);
  ctx->request_term_notification_by_kind(ctx, FP_CONSTANT, false);
  ctx->request_term_notification_by_kind(ctx, FP_ADD, false);
  ctx->request_term_notification_by_kind(ctx, FP_SUB, false);
  ctx->request_term_notification_by_kind(ctx, FP_MUL, false);
  ctx->request_term_notification_by_kind(ctx, FP_EQ_ATOM, false);
  ctx->request_term_notification_by_kind(ctx, FP_LT_ATOM, false);
  ctx->request_term_notification_by_kind(ctx, FP_LEQ_ATOM, false);
  ctx->request_term_notification_by_kind(ctx, FP_GT_ATOM, false);
  ctx->request_term_notification_by_kind(ctx, FP_GEQ_ATOM, false);
  ctx->request_term_notification_by_kind(ctx, FP_ISNAN_ATOM, false);
  ctx->request_term_notification_by_kind(ctx, FP_ISINF_ATOM, false);
  ctx->request_term_notification_by_kind(ctx, FP_ISZERO_ATOM, false);
  ctx->request_term_notification_by_kind(ctx, FP_ISSUBNORMAL_ATOM, false);
  ctx->request_term_notification_by_kind(ctx, FP_ISNORMAL_ATOM, false);

  ctx->request_term_notification_by_type(ctx, ROUNDING_MODE_TYPE);
  ctx->request_term_notification_by_type(ctx, FP_TYPE);
  ctx->request_decision_calls(ctx, ROUNDING_MODE_TYPE);
  ctx->request_decision_calls(ctx, FP_TYPE);
}

static void fp_plugin_destruct(plugin_t *plugin) {
  fp_plugin_t *fp;

  fp = (fp_plugin_t *) plugin;
  delete_ivector(&fp->watched_terms);
}

static bool fp_get_value(fp_plugin_t *fp, term_t t, const mcsat_value_t **v) {
  variable_t x;

  x = variable_db_get_variable_if_exists(fp->ctx->var_db, t);
  if (x == variable_null || !trail_has_value(fp->ctx->trail, x)) {
    return false;
  }

  *v = trail_get_value(fp->ctx->trail, x);
  return true;
}

static bool fp_get_fp_value(fp_plugin_t *fp, term_t t, fp_const_t *v) {
  const mcsat_value_t *value;

  if (!fp_get_value(fp, t, &value) || value->type != VALUE_FP) {
    return false;
  }
  *v = value->fp_value;
  return true;
}

static bool fp_get_rm_value(fp_plugin_t *fp, term_t t, fp_rounding_mode_t *mode) {
  const mcsat_value_t *value;

  if (!fp_get_value(fp, t, &value) || value->type != VALUE_ROUNDING_MODE) {
    return false;
  }
  *mode = value->rm_value;
  return true;
}

static void fp_register_composite_children(fp_plugin_t *fp, composite_term_t *d) {
  uint32_t i;

  for (i = 0; i < d->arity; ++ i) {
    variable_db_get_variable(fp->ctx->var_db, d->arg[i]);
  }
}

static bool fp_eval_inf_add(term_kind_t kind, const fp_const_t *a, const fp_const_t *b, fp_const_t *out) {
  bool sign_b;

  sign_b = kind == FP_SUB ? !b->sign : b->sign;
  if (fp_value_is_infinite(a) && fp_value_is_infinite(b)) {
    if (a->sign == sign_b) {
      fp_value_make_inf(out, a->ebits, a->sbits, a->sign);
    } else {
      fp_value_make_nan(out, a->ebits, a->sbits);
    }
    return true;
  }
  if (fp_value_is_infinite(a)) {
    fp_value_make_inf(out, a->ebits, a->sbits, a->sign);
    return true;
  }
  if (fp_value_is_infinite(b)) {
    fp_value_make_inf(out, a->ebits, a->sbits, sign_b);
    return true;
  }
  return false;
}

static bool fp_eval_binary(fp_plugin_t *fp, term_t t, fp_const_t *out) {
  composite_term_t *d;
  fp_const_t a;
  fp_const_t b;
  fp_rounding_mode_t mode;
  fp_dyadic_t da;
  fp_dyadic_t db;
  fp_dyadic_t dr;
  term_kind_t kind;
  bool ok;

  kind = term_kind(fp->ctx->terms, t);
  d = composite_term_desc(fp->ctx->terms, t);
  if (!fp_get_rm_value(fp, d->arg[0], &mode) ||
      !fp_get_fp_value(fp, d->arg[1], &a) ||
      !fp_get_fp_value(fp, d->arg[2], &b)) {
    return false;
  }

  if (!fp_rounding_mode_is_directed(mode)) {
    return false;
  }

  if (fp_value_is_nan(&a) || fp_value_is_nan(&b)) {
    fp_value_make_nan(out, a.ebits, a.sbits);
    return true;
  }

  if (kind == FP_ADD || kind == FP_SUB) {
    if (fp_eval_inf_add(kind, &a, &b, out)) {
      return true;
    }
  } else {
    assert(kind == FP_MUL);
    if ((fp_value_is_zero(&a) && fp_value_is_infinite(&b)) ||
        (fp_value_is_infinite(&a) && fp_value_is_zero(&b))) {
      fp_value_make_nan(out, a.ebits, a.sbits);
      return true;
    }
    if (fp_value_is_infinite(&a) || fp_value_is_infinite(&b)) {
      fp_value_make_inf(out, a.ebits, a.sbits, a.sign ^ b.sign);
      return true;
    }
  }

  fp_dyadic_init(&da);
  fp_dyadic_init(&db);
  fp_dyadic_init(&dr);
  ok = fp_value_to_dyadic(&a, &da) && fp_value_to_dyadic(&b, &db);
  if (ok) {
    if (kind == FP_ADD) {
      fp_dyadic_add(&dr, &da, &db);
    } else if (kind == FP_SUB) {
      fp_dyadic_sub(&dr, &da, &db);
    } else {
      fp_dyadic_mul(&dr, &da, &db);
    }
    ok = fp_round_dyadic(out, a.ebits, a.sbits, mode, &dr);
  }
  fp_dyadic_destruct(&dr);
  fp_dyadic_destruct(&db);
  fp_dyadic_destruct(&da);
  return ok;
}

static bool fp_eval_predicate(fp_plugin_t *fp, term_t t, bool *out) {
  fp_const_t a;
  term_kind_t kind;

  kind = term_kind(fp->ctx->terms, t);
  if (!fp_get_fp_value(fp, unary_term_arg(fp->ctx->terms, t), &a)) {
    return false;
  }

  switch (kind) {
  case FP_ISNAN_ATOM:
    *out = fp_value_is_nan(&a);
    return true;
  case FP_ISINF_ATOM:
    *out = fp_value_is_infinite(&a);
    return true;
  case FP_ISZERO_ATOM:
    *out = fp_value_is_zero(&a);
    return true;
  case FP_ISSUBNORMAL_ATOM:
    *out = fp_value_is_subnormal(&a);
    return true;
  case FP_ISNORMAL_ATOM:
    *out = fp_value_is_normal(&a);
    return true;
  default:
    assert(false);
    return false;
  }
}

static bool fp_eval_comparison(fp_plugin_t *fp, term_t t, bool *out) {
  composite_term_t *d;
  fp_const_t a;
  fp_const_t b;
  int cmp;

  d = composite_term_desc(fp->ctx->terms, t);
  if (!fp_get_fp_value(fp, d->arg[0], &a) || !fp_get_fp_value(fp, d->arg[1], &b)) {
    return false;
  }

  if (fp_value_is_nan(&a) || fp_value_is_nan(&b)) {
    *out = false;
    return true;
  }

  cmp = fp_value_cmp(&a, &b);
  switch (term_kind(fp->ctx->terms, t)) {
  case FP_EQ_ATOM:
    *out = cmp == 0;
    return true;
  case FP_LT_ATOM:
    *out = cmp < 0;
    return true;
  case FP_LEQ_ATOM:
    *out = cmp <= 0;
    return true;
  case FP_GT_ATOM:
    *out = cmp > 0;
    return true;
  case FP_GEQ_ATOM:
    *out = cmp >= 0;
    return true;
  default:
    assert(false);
    return false;
  }
}

static bool fp_plugin_eval_bool(fp_plugin_t *fp, term_t t, bool *out) {
  term_kind_t kind;

  kind = term_kind(fp->ctx->terms, t);
  if (FP_EQ_ATOM <= kind && kind <= FP_GEQ_ATOM) {
    return fp_eval_comparison(fp, t, out);
  }
  if (FP_ISNAN_ATOM <= kind && kind <= FP_ISNORMAL_ATOM) {
    return fp_eval_predicate(fp, t, out);
  }
  return false;
}

static void fp_plugin_new_term_notify(plugin_t *plugin, term_t t, trail_token_t *prop) {
  fp_plugin_t *fp;
  term_kind_t kind;
  variable_t x;
  mcsat_value_t value;

  fp = (fp_plugin_t *) plugin;
  kind = term_kind(fp->ctx->terms, t);
  x = variable_db_get_variable(fp->ctx->var_db, t);

  if (kind == ROUNDING_MODE_CONSTANT) {
    mcsat_value_construct_rounding_mode(&value, rounding_mode_term_desc(fp->ctx->terms, t));
    prop->add(prop, x, &value);
    return;
  }
  if (kind == FP_CONSTANT) {
    mcsat_value_construct_fp_value(&value, fp_const_term_desc(fp->ctx->terms, t));
    prop->add(prop, x, &value);
    return;
  }

  if (FP_ADD <= kind && kind <= FP_GEQ_ATOM) {
    fp_register_composite_children(fp, composite_term_desc(fp->ctx->terms, t));
  } else {
    assert(FP_ISNAN_ATOM <= kind && kind <= FP_ISNORMAL_ATOM);
    variable_db_get_variable(fp->ctx->var_db, unary_term_arg(fp->ctx->terms, t));
  }
  ivector_push(&fp->watched_terms, t);
}

static void fp_plugin_propagate_term(fp_plugin_t *fp, term_t t, trail_token_t *prop) {
  variable_t x;
  term_kind_t kind;
  mcsat_value_t value;
  fp_const_t fp_value;
  bool bool_value;

  x = variable_db_get_variable_if_exists(fp->ctx->var_db, t);
  if (x == variable_null) {
    return;
  }

  kind = term_kind(fp->ctx->terms, t);
  if (FP_ADD <= kind && kind <= FP_MUL) {
    if (trail_has_value(fp->ctx->trail, x)) {
      return;
    }
    if (fp_eval_binary(fp, t, &fp_value)) {
      mcsat_value_construct_fp_value(&value, &fp_value);
      prop->add(prop, x, &value);
    }
    return;
  }

  if (fp_plugin_eval_bool(fp, t, &bool_value)) {
    if (trail_has_value(fp->ctx->trail, x)) {
      const mcsat_value_t *assigned = trail_get_value(fp->ctx->trail, x);
      if (assigned->type == VALUE_BOOLEAN && assigned->b != bool_value) {
        fp->conflict_literal = fp_explain_conflict_literal(t, assigned->b);
        prop->conflict(prop);
      }
    } else {
      mcsat_value_construct_bool(&value, bool_value);
      prop->add(prop, x, &value);
    }
  }
}

static void fp_plugin_propagate(plugin_t *plugin, trail_token_t *prop) {
  fp_plugin_t *fp;
  uint32_t i;

  fp = (fp_plugin_t *) plugin;
  for (i = 0; i < fp->watched_terms.size && trail_is_consistent(fp->ctx->trail); ++ i) {
    fp_plugin_propagate_term(fp, fp->watched_terms.data[i], prop);
  }
}

static void fp_plugin_decide(plugin_t *plugin, variable_t x, trail_token_t *decide, bool must) {
  fp_plugin_t *fp;
  type_t tau;
  fp_const_t zero;
  mcsat_value_t value;

  (void) must;
  fp = (fp_plugin_t *) plugin;
  tau = variable_db_get_type(fp->ctx->var_db, x);

  if (type_kind(fp->ctx->types, tau) == ROUNDING_MODE_TYPE) {
    mcsat_value_construct_rounding_mode(&value, FP_RTZ);
    decide->add(decide, x, &value);
  } else {
    assert(type_kind(fp->ctx->types, tau) == FP_TYPE);
    fp_value_make_zero(&zero, fp_type_ebits(fp->ctx->types, tau), fp_type_sbits(fp->ctx->types, tau), false);
    mcsat_value_construct_fp_value(&value, &zero);
    decide->add(decide, x, &value);
  }
}

static void fp_plugin_decide_assignment(plugin_t *plugin, variable_t x, const mcsat_value_t *value, trail_token_t *decide) {
  (void) plugin;
  decide->add(decide, x, value);
}

static void fp_plugin_get_conflict(plugin_t *plugin, ivector_t *conflict) {
  fp_plugin_t *fp;

  fp = (fp_plugin_t *) plugin;
  if (fp->conflict_literal != NULL_TERM) {
    ivector_push(conflict, fp->conflict_literal);
  }
}

static term_t fp_plugin_explain_propagation(plugin_t *plugin, variable_t var, ivector_t *reasons) {
  fp_plugin_t *fp;

  (void) reasons;
  fp = (fp_plugin_t *) plugin;
  return variable_db_get_term(fp->ctx->var_db, var);
}

static void fp_plugin_gc_mark(plugin_t *plugin, gc_info_t *gc) {
  fp_plugin_t *fp;
  uint32_t i;
  variable_t x;

  fp = (fp_plugin_t *) plugin;
  for (i = 0; i < fp->watched_terms.size; ++ i) {
    x = variable_db_get_variable_if_exists(fp->ctx->var_db, fp->watched_terms.data[i]);
    if (x != variable_null) {
      gc_info_mark(gc, x);
    }
  }
}

static void fp_plugin_gc_sweep(plugin_t *plugin, const gc_info_t *gc) {
  fp_plugin_t *fp;
  uint32_t i, j;
  variable_t x;

  fp = (fp_plugin_t *) plugin;
  j = 0;
  for (i = 0; i < fp->watched_terms.size; ++ i) {
    x = variable_db_get_variable_if_exists(fp->ctx->var_db, fp->watched_terms.data[i]);
    if (x != variable_null && gc_info_is_marked(gc, x)) {
      fp->watched_terms.data[j] = fp->watched_terms.data[i];
      j ++;
    }
  }
  fp->watched_terms.size = j;
}

plugin_t* fp_plugin_allocator(void) {
  fp_plugin_t *plugin;

  plugin = safe_malloc(sizeof(fp_plugin_t));
  plugin_construct((plugin_t *) plugin);
  plugin->plugin_interface.construct = fp_plugin_construct;
  plugin->plugin_interface.destruct = fp_plugin_destruct;
  plugin->plugin_interface.new_term_notify = fp_plugin_new_term_notify;
  plugin->plugin_interface.propagate = fp_plugin_propagate;
  plugin->plugin_interface.decide = fp_plugin_decide;
  plugin->plugin_interface.decide_assignment = fp_plugin_decide_assignment;
  plugin->plugin_interface.get_conflict = fp_plugin_get_conflict;
  plugin->plugin_interface.explain_propagation = fp_plugin_explain_propagation;
  plugin->plugin_interface.gc_mark = fp_plugin_gc_mark;
  plugin->plugin_interface.gc_sweep = fp_plugin_gc_sweep;

  return (plugin_t *) plugin;
}
