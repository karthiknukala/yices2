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

#ifndef MCSAT_SHARED_STATE_H_
#define MCSAT_SHARED_STATE_H_

#include <stdbool.h>
#include <stdint.h>

#include "terms/terms.h"
#include "terms/types.h"

typedef struct mcsat_shared_state_s mcsat_shared_state_t;

mcsat_shared_state_t* mcsat_shared_state_acquire(term_table_t* terms, type_table_t* types);
void mcsat_shared_state_release(mcsat_shared_state_t* state);
bool mcsat_shared_state_is_enabled(const mcsat_shared_state_t* state);

void mcsat_shared_state_term_lock(mcsat_shared_state_t* state);
void mcsat_shared_state_term_unlock(mcsat_shared_state_t* state);

void mcsat_shared_state_publish_term(mcsat_shared_state_t* state, term_t term);

int32_t mcsat_shared_state_lookup_variable(mcsat_shared_state_t* state, term_t term);
int32_t mcsat_shared_state_get_variable(mcsat_shared_state_t* state, term_t term, bool* created);
term_t mcsat_shared_state_get_variable_term(mcsat_shared_state_t* state, int32_t var);
uint32_t mcsat_shared_state_variable_limit(mcsat_shared_state_t* state);

uint64_t mcsat_shared_state_new_lemma_session(mcsat_shared_state_t* state);
bool mcsat_shared_state_publish_lemma(mcsat_shared_state_t* state, uint64_t session, term_t lemma, uint64_t* seq_out);
uint64_t mcsat_shared_state_latest_lemma_seq(mcsat_shared_state_t* state);
term_t mcsat_shared_state_get_lemma(mcsat_shared_state_t* state, uint64_t session, uint64_t seq);

#endif /* MCSAT_SHARED_STATE_H_ */
