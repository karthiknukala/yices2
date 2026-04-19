/*
 * Concrete SAT-kernel adapter for smt_core.
 */

#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

#include "solvers/egraph/smt_core_sat.h"

static tracer_t *smt_core_sat_trace(void *backend) {
  return ((smt_core_t *) backend)->trace;
}

static gate_table_t *smt_core_sat_gate_table(void *backend) {
  return get_gate_table((smt_core_t *) backend);
}

static smt_status_t smt_core_sat_status(void *backend) {
  return smt_status((smt_core_t *) backend);
}

static uint32_t smt_core_sat_decision_level(void *backend) {
  return smt_decision_level((smt_core_t *) backend);
}

static uint32_t smt_core_sat_base_level(void *backend) {
  return smt_base_level((smt_core_t *) backend);
}

static uint64_t smt_core_sat_num_decisions(void *backend) {
  return num_decisions((smt_core_t *) backend);
}

static uint64_t smt_core_sat_num_random_decisions(void *backend) {
  return num_random_decisions((smt_core_t *) backend);
}

static uint64_t smt_core_sat_num_conflicts(void *backend) {
  return num_conflicts((smt_core_t *) backend);
}

static uint32_t smt_core_sat_num_vars(void *backend) {
  return num_vars((smt_core_t *) backend);
}

static uint32_t smt_core_sat_num_unit_clauses(void *backend) {
  return num_unit_clauses((smt_core_t *) backend);
}

static uint32_t smt_core_sat_num_binary_clauses(void *backend) {
  return num_binary_clauses((smt_core_t *) backend);
}

static uint32_t smt_core_sat_num_prob_clauses(void *backend) {
  return num_prob_clauses((smt_core_t *) backend);
}

static uint64_t smt_core_sat_num_prob_literals(void *backend) {
  return num_prob_literals((smt_core_t *) backend);
}

static uint32_t smt_core_sat_num_learned_clauses(void *backend) {
  return num_learned_clauses((smt_core_t *) backend);
}

static uint64_t smt_core_sat_num_learned_literals(void *backend) {
  return num_learned_literals((smt_core_t *) backend);
}

static double smt_core_sat_avg_learned_clause_size(void *backend) {
  return avg_learned_clause_size((smt_core_t *) backend);
}

static uint64_t smt_core_sat_num_learned_clauses_deleted(void *backend) {
  return ((smt_core_t *) backend)->stats.learned_clauses_deleted;
}

static bool smt_core_sat_has_assumptions(void *backend) {
  return ((smt_core_t *) backend)->has_assumptions;
}

static literal_t smt_core_sat_get_next_assumption(void *backend) {
  return get_next_assumption((smt_core_t *) backend);
}

static void smt_core_sat_save_conflicting_assumption(void *backend, literal_t l) {
  save_conflicting_assumption((smt_core_t *) backend, l);
}

static bool smt_core_sat_inconsistent(void *backend) {
  return ((smt_core_t *) backend)->inconsistent;
}

static literal_t *smt_core_sat_trail_literals(void *backend) {
  return ((smt_core_t *) backend)->stack.lit;
}

static uint32_t smt_core_sat_trail_top(void *backend) {
  return ((smt_core_t *) backend)->stack.top;
}

static uint32_t smt_core_sat_trail_theory_ptr(void *backend) {
  return ((smt_core_t *) backend)->stack.theory_ptr;
}

static bvar_t smt_core_sat_new_boolvar(void *backend) {
  return create_boolean_variable((smt_core_t *) backend);
}

static void smt_core_sat_attach_atom(void *backend, bvar_t v, void *atom) {
  attach_atom_to_bvar((smt_core_t *) backend, v, atom);
}

static void smt_core_sat_remove_atom(void *backend, bvar_t v) {
  remove_bvar_atom((smt_core_t *) backend, v);
}

static bool smt_core_sat_bvar_has_atom(void *backend, bvar_t v) {
  return bvar_has_atom((smt_core_t *) backend, v);
}

static void *smt_core_sat_bvar_atom(void *backend, bvar_t v) {
  return bvar_atom((smt_core_t *) backend, v);
}

static antecedent_t smt_core_sat_bvar_antecedent(void *backend, bvar_t v) {
  return get_bvar_antecedent((smt_core_t *) backend, v);
}

static bval_t smt_core_sat_bvar_value(void *backend, bvar_t v) {
  return bvar_value((smt_core_t *) backend, v);
}

static bval_t smt_core_sat_bvar_base_value(void *backend, bvar_t v) {
  return bvar_base_value((smt_core_t *) backend, v);
}

static bval_t smt_core_sat_literal_value(void *backend, literal_t l) {
  return literal_value((smt_core_t *) backend, l);
}

static bval_t smt_core_sat_literal_base_value(void *backend, literal_t l) {
  return literal_base_value((smt_core_t *) backend, l);
}

static bool smt_core_sat_literal_is_assigned(void *backend, literal_t l) {
  return literal_is_assigned((smt_core_t *) backend, l);
}

static void smt_core_sat_add_clause(void *backend, uint32_t n, literal_t *a) {
  add_clause((smt_core_t *) backend, n, a);
}

static void smt_core_sat_add_empty_clause(void *backend) {
  add_empty_clause((smt_core_t *) backend);
}

static void smt_core_sat_add_unit_clause(void *backend, literal_t l) {
  add_unit_clause((smt_core_t *) backend, l);
}

static void smt_core_sat_add_binary_clause(void *backend, literal_t l1, literal_t l2) {
  add_binary_clause((smt_core_t *) backend, l1, l2);
}

static void smt_core_sat_add_ternary_clause(void *backend, literal_t l1, literal_t l2, literal_t l3) {
  add_ternary_clause((smt_core_t *) backend, l1, l2, l3);
}

static void smt_core_sat_implied_literal(void *backend, literal_t l, antecedent_t a) {
  implied_literal((smt_core_t *) backend, l, a);
}

static void smt_core_sat_propagate_literal(void *backend, literal_t l, void *expl) {
  propagate_literal((smt_core_t *) backend, l, expl);
}

static void smt_core_sat_record_empty_conflict(void *backend) {
  record_empty_theory_conflict((smt_core_t *) backend);
}

static void smt_core_sat_record_unit_conflict(void *backend, literal_t l) {
  record_unit_theory_conflict((smt_core_t *) backend, l);
}

static void smt_core_sat_record_binary_conflict(void *backend, literal_t l1, literal_t l2) {
  record_binary_theory_conflict((smt_core_t *) backend, l1, l2);
}

static void smt_core_sat_record_ternary_conflict(void *backend, literal_t l1, literal_t l2, literal_t l3) {
  record_ternary_theory_conflict((smt_core_t *) backend, l1, l2, l3);
}

static void smt_core_sat_record_conflict(void *backend, literal_t *a) {
  record_theory_conflict((smt_core_t *) backend, a);
}

static uint32_t smt_core_sat_add_quant_lemmas(void *backend, literal_t en, ivector_t *units) {
  return add_all_quant_lemmas((smt_core_t *) backend, en, units);
}

static void smt_core_sat_build_unsat_core(void *backend, ivector_t *v) {
  build_unsat_core((smt_core_t *) backend, v);
}

static void smt_core_sat_bump_conflicts(void *backend, uint64_t delta) {
  ((smt_core_t *) backend)->stats.conflicts += delta;
}

static void smt_core_sat_collect_free_bool_vars(void *backend, free_bool_vars_t *fv) {
  collect_free_bool_vars(fv, (smt_core_t *) backend);
}

static void smt_core_sat_print_literal(FILE *f, literal_t l) {
  if (l < 0) {
    if (l == null_literal) {
      fputs("nil", f);
    } else {
      fprintf(f, "LIT%"PRId32, l);
    }
  } else if (l == true_literal) {
    fputs("tt", f);
  } else if (l == false_literal) {
    fputs("ff", f);
  } else {
    if (is_neg(l)) {
      fputc('~', f);
    }
    fprintf(f, "p!%"PRId32, var_of(l));
  }
}

static void smt_core_sat_print_clause(FILE *f, clause_t *cl) {
  uint32_t i;
  literal_t l;

  if (cl->cl[0] < 0 || cl->cl[1] < 0) {
    fputc('[', f);
    smt_core_sat_print_literal(f, - cl->cl[0]);
    fputc(' ', f);
    smt_core_sat_print_literal(f, - cl->cl[1]);
    i = 2;
    l = cl->cl[i];
    while (l >= 0) {
      fputc(' ', f);
      smt_core_sat_print_literal(f, l);
      i ++;
      l = cl->cl[i];
    }
    fputc(']', f);
  } else {
    fputc('{', f);
    smt_core_sat_print_literal(f, cl->cl[0]);
    i = 1;
    l = cl->cl[i];
    while (l >= 0) {
      fputc(' ', f);
      smt_core_sat_print_literal(f, l);
      i ++;
      l = cl->cl[i];
    }
    fputc('}', f);
  }
}

static void smt_core_sat_print_unit_clause(FILE *f, literal_t l) {
  fputc('{', f);
  smt_core_sat_print_literal(f, l);
  fputc('}', f);
}

static void smt_core_sat_print_unit_clauses_impl(FILE *f, smt_core_t *core) {
  prop_stack_t *stack;
  uint32_t i, n;

  n = core->nb_unit_clauses;
  stack = &core->stack;
  for (i=0; i<n; i++) {
    smt_core_sat_print_unit_clause(f, stack->lit[i]);
    fputc('\n', f);
  }
}

static void smt_core_sat_print_litarray(FILE *f, uint32_t n, literal_t *a) {
  uint32_t i;

  fputc('{', f);
  if (n > 0) {
    smt_core_sat_print_literal(f, a[0]);
    for (i=1; i<n; i++) {
      fputc(' ', f);
      smt_core_sat_print_literal(f, a[i]);
    }
  }
  fputc('}', f);
}

static void smt_core_sat_print_binary_clause(FILE *f, literal_t l1, literal_t l2) {
  fputc('{', f);
  smt_core_sat_print_literal(f, l1);
  fputc(' ', f);
  smt_core_sat_print_literal(f, l2);
  fputc('}', f);
}

static void smt_core_sat_print_binary_clauses_impl(FILE *f, smt_core_t *core) {
  int32_t n;
  literal_t l1, l2;
  literal_t *bin;

  n = core->nlits;
  for (l1=0; l1<n; l1++) {
    bin = core->bin[l1];
    if (bin != NULL) {
      for (;;) {
        l2 = *bin ++;
        if (l2 < 0) {
          break;
        }
        if (l1 <= l2) {
          smt_core_sat_print_binary_clause(f, l1, l2);
          fputc('\n', f);
        }
      }
    }
  }
}

static void smt_core_sat_print_clause_vector(FILE *f, clause_t **vector) {
  uint32_t i, n;

  if (vector != NULL) {
    n = get_cv_size(vector);
    for (i=0; i<n; i++) {
      smt_core_sat_print_clause(f, vector[i]);
      fputc('\n', f);
    }
  }
}

static void smt_core_sat_print_problem_clauses_impl(FILE *f, smt_core_t *core) {
  smt_core_sat_print_clause_vector(f, core->problem_clauses);
}

static void smt_core_sat_print_learned_clauses_impl(FILE *f, smt_core_t *core) {
  smt_core_sat_print_clause_vector(f, core->learned_clauses);
}

static uint32_t smt_core_sat_lemma_length(literal_t *a) {
  uint32_t n;

  n = 0;
  while (*a >= 0) {
    a ++;
    n ++;
  }
  return n;
}

static void smt_core_sat_print_clauses_impl(FILE *f, smt_core_t *core) {
  smt_core_sat_print_unit_clauses_impl(f, core);
  smt_core_sat_print_binary_clauses_impl(f, core);
  smt_core_sat_print_problem_clauses_impl(f, core);
  fputc('\n', f);
}

static void smt_core_sat_print_lemmas_impl(FILE *f, smt_core_t *core) {
  lemma_block_t *tmp;
  literal_t *lemma;
  uint32_t i, j, n;

  for (i=0; i<core->lemmas.free_block; i++) {
    tmp = core->lemmas.block[i];
    lemma = tmp->data;
    j = 0;
    while (j < tmp->ptr) {
      n = smt_core_sat_lemma_length(lemma);
      smt_core_sat_print_litarray(f, n, lemma);
      fputc('\n', f);
      n ++;
      j += n;
      lemma += n;
    }
  }
}

static void smt_core_sat_print_boolean_assignment_impl(FILE *f, smt_core_t *core) {
  prop_stack_t *stack;
  uint32_t i, n;
  literal_t l;

  stack = &core->stack;
  n = stack->top;
  for (i=0; i<n; i++) {
    l = stack->lit[i];
    fputc(' ', f);
    if (is_pos(l)) {
      fputc(' ', f);
    }
    smt_core_sat_print_literal(f, l);
    fprintf(f, " level = %"PRIu32"\n", core->level[var_of(l)]);
  }
}

static void smt_core_sat_print_binary_clauses(FILE *f, void *backend) {
  smt_core_sat_print_binary_clauses_impl(f, (smt_core_t *) backend);
}

static void smt_core_sat_print_problem_clauses(FILE *f, void *backend) {
  smt_core_sat_print_problem_clauses_impl(f, (smt_core_t *) backend);
}

static void smt_core_sat_print_learned_clauses(FILE *f, void *backend) {
  smt_core_sat_print_learned_clauses_impl(f, (smt_core_t *) backend);
}

static void smt_core_sat_print_lemmas(FILE *f, void *backend) {
  smt_core_sat_print_lemmas_impl(f, (smt_core_t *) backend);
}

static void smt_core_sat_print_clauses(FILE *f, void *backend) {
  smt_core_sat_print_clauses_impl(f, (smt_core_t *) backend);
}

static void smt_core_sat_print_boolean_assignment(FILE *f, void *backend) {
  smt_core_sat_print_boolean_assignment_impl(f, (smt_core_t *) backend);
}

static void smt_core_sat_start_search(void *backend, uint32_t n, const literal_t *a) {
  start_search((smt_core_t *) backend, n, a);
}

static bool smt_core_sat_boolean_propagate(void *backend) {
  return smt_boolean_propagate((smt_core_t *) backend);
}

static bool smt_core_sat_resolve_conflict(void *backend) {
  return smt_resolve_conflict((smt_core_t *) backend);
}

static bool smt_core_sat_has_pending_lemmas(void *backend) {
  return smt_has_pending_lemmas((smt_core_t *) backend);
}

static void smt_core_sat_integrate_pending_lemmas(void *backend) {
  smt_integrate_pending_lemmas((smt_core_t *) backend);
}

static bool smt_core_sat_has_pending_gc(void *backend) {
  return smt_has_pending_gc((smt_core_t *) backend);
}

static void smt_core_sat_collect_pending_gc(void *backend) {
  smt_collect_pending_gc((smt_core_t *) backend);
}

static void smt_core_sat_maybe_simplify_clause_database(void *backend) {
  smt_maybe_simplify_clause_database((smt_core_t *) backend);
}

static void smt_core_sat_set_status(void *backend, smt_status_t status) {
  smt_set_status((smt_core_t *) backend, status);
}

static void smt_core_sat_restart(void *backend) {
  smt_restart((smt_core_t *) backend);
}

static void smt_core_sat_decide_literal(void *backend, literal_t l) {
  decide_literal((smt_core_t *) backend, l);
}

static literal_t smt_core_sat_select_unassigned_literal(void *backend) {
  return select_unassigned_literal((smt_core_t *) backend);
}

static void smt_core_sat_reduce_clause_database(void *backend) {
  reduce_clause_database((smt_core_t *) backend);
}

static th_sat_interface_t smt_core_sat_interface = {
  smt_core_sat_trace,
  smt_core_sat_gate_table,
  smt_core_sat_status,
  smt_core_sat_decision_level,
  smt_core_sat_base_level,
  smt_core_sat_num_decisions,
  smt_core_sat_num_random_decisions,
  smt_core_sat_num_conflicts,
  smt_core_sat_num_vars,
  smt_core_sat_num_unit_clauses,
  smt_core_sat_num_binary_clauses,
  smt_core_sat_num_prob_clauses,
  smt_core_sat_num_prob_literals,
  smt_core_sat_num_learned_clauses,
  smt_core_sat_num_learned_literals,
  smt_core_sat_avg_learned_clause_size,
  smt_core_sat_num_learned_clauses_deleted,
  smt_core_sat_has_assumptions,
  smt_core_sat_get_next_assumption,
  smt_core_sat_save_conflicting_assumption,
  smt_core_sat_inconsistent,
  smt_core_sat_trail_literals,
  smt_core_sat_trail_top,
  smt_core_sat_trail_theory_ptr,
  smt_core_sat_new_boolvar,
  smt_core_sat_attach_atom,
  smt_core_sat_remove_atom,
  smt_core_sat_bvar_has_atom,
  smt_core_sat_bvar_atom,
  smt_core_sat_bvar_antecedent,
  smt_core_sat_bvar_value,
  smt_core_sat_bvar_base_value,
  smt_core_sat_literal_value,
  smt_core_sat_literal_base_value,
  smt_core_sat_literal_is_assigned,
  smt_core_sat_add_clause,
  smt_core_sat_add_empty_clause,
  smt_core_sat_add_unit_clause,
  smt_core_sat_add_binary_clause,
  smt_core_sat_add_ternary_clause,
  smt_core_sat_implied_literal,
  smt_core_sat_propagate_literal,
  smt_core_sat_record_empty_conflict,
  smt_core_sat_record_unit_conflict,
  smt_core_sat_record_binary_conflict,
  smt_core_sat_record_ternary_conflict,
  smt_core_sat_record_conflict,
  smt_core_sat_add_quant_lemmas,
  smt_core_sat_build_unsat_core,
  smt_core_sat_bump_conflicts,
  smt_core_sat_collect_free_bool_vars,
  smt_core_sat_print_binary_clauses,
  smt_core_sat_print_problem_clauses,
  smt_core_sat_print_learned_clauses,
  smt_core_sat_print_lemmas,
  smt_core_sat_print_clauses,
  smt_core_sat_print_boolean_assignment,
  smt_core_sat_start_search,
  smt_core_sat_boolean_propagate,
  smt_core_sat_resolve_conflict,
  smt_core_sat_has_pending_lemmas,
  smt_core_sat_integrate_pending_lemmas,
  smt_core_sat_has_pending_gc,
  smt_core_sat_collect_pending_gc,
  smt_core_sat_maybe_simplify_clause_database,
  smt_core_sat_set_status,
  smt_core_sat_restart,
  smt_core_sat_decide_literal,
  smt_core_sat_select_unassigned_literal,
  smt_core_sat_reduce_clause_database,
};

void init_smt_core_sat_kernel(sat_kernel_t *kernel, smt_core_t *core) {
  sat_kernel_bind(kernel, core, &smt_core_sat_interface);
}
