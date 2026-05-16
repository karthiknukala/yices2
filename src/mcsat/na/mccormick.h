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

#pragma once

#include <stdint.h>
#include <stdbool.h>

#include "mcsat/plugin.h"
#include "mcsat/utils/statistics.h"

#include "terms/balanced_arith_buffers.h"
#include "terms/terms.h"

#include "utils/int_hash_sets.h"
#include "utils/int_vectors.h"

typedef struct na_plugin_s na_plugin_t;

/*
 * Experimental McCormick relaxation owned by the nonlinear-arithmetic plugin.
 *
 * The component is an abstraction oracle: it may report a conflict when a
 * guarded linear McCormick relaxation is infeasible, but all conflict literals
 * are original trail literals and exact libpoly/NRA reasoning remains the
 * authority for models, roots, and nonlinear explanations.
 */
typedef struct mccormick_s {
  na_plugin_t* na;

  /** Products seen during NA term registration. */
  int_hset_t registered_products;

  /** Last relaxation conflict, expressed as original trail literals. */
  ivector_t conflict;

  /** Avoid repeating the same check while the trail is unchanged. */
  uint32_t checked_trail_size;
  uint32_t checked_decision_level;

  /** Local arithmetic buffer for generated linear atoms. */
  rba_buffer_t buffer;

  struct {
    statistic_int_t* products;
    statistic_int_t* checks;
    statistic_int_t* conflicts;
    statistic_int_t* envelopes;
    statistic_int_t* hints;
  } stats;
} mccormick_t;

void mccormick_construct(mccormick_t* mc, na_plugin_t* na);

void mccormick_destruct(mccormick_t* mc);

void mccormick_register_term(mccormick_t* mc, term_t t);

void mccormick_push(mccormick_t* mc);

void mccormick_pop(mccormick_t* mc);

void mccormick_event_notify(mccormick_t* mc);

bool mccormick_check(mccormick_t* mc, trail_token_t* prop);

bool mccormick_has_conflict(const mccormick_t* mc);

void mccormick_get_conflict(mccormick_t* mc, ivector_t* conflict);
