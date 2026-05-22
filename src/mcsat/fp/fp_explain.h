/*
 * Explanation hooks for the native FP plugin.
 *
 * V1 keeps the polarity explicit and returns the currently assigned literal
 * that was contradicted by dyadic evaluation. Dyadic-interpolant regions are
 * the next refinement layer.
 */

#pragma once

#include "terms/terms.h"

term_t fp_explain_conflict_literal(term_t atom, bool assigned_value);
