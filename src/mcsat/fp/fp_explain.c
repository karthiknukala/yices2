/*
 * Explanation hooks for the native FP plugin.
 */

#include "mcsat/fp/fp_explain.h"

term_t fp_explain_conflict_literal(term_t atom, bool assigned_value) {
  return assigned_value ? atom : opposite_term(atom);
}
