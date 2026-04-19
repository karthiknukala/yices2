/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
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

/*
 * Queue for storing egraph hub facts sent to theory solvers.
 * The layout is defined in egraph_assertion_queues.h; this file keeps the
 * original module name for compatibility while implementing the wider bus.
 */


#include "solvers/egraph/egraph_assertion_queues.h"
#include "utils/memalloc.h"


/*
 * Initialize queue: nothing is allocated yet
 */
void init_eassertion_queue(eassertion_queue_t *queue) {
  queue->size = 0;
  queue->top = 0;
  queue->data = NULL;
}


/*
 * Delete
 */
void delete_eassertion_queue(eassertion_queue_t *queue) {
  safe_free(queue->data);
  queue->data = NULL;
}



/*
 * Make enough room in the queue for an object of the given size (in bytes)
 */
static void resize_eassertion_queue(eassertion_queue_t *queue, uint32_t size) {
  uint32_t d, n;

  d = queue->top + size;
  n = queue->size;
  if (d > n) {
    // make n bigger
    if (n == 0) {
      // first allocation
      n = DEF_EASSERTION_QUEUE_SIZE;
    } else {
      n += n>>1; // try to make n 50% larger
    }
    if (d > n) {
      n = d;
    }
    if (n >= MAX_EASSERTION_QUEUE_SIZE) {
      out_of_memory();
    }
    queue->data = (uint8_t* ) safe_realloc(queue->data, n);
    queue->size = n;
  }
}


/*
 * Allocate an assertion descriptor of arity n
 */
static eassertion_t *eassertion_alloc(eassertion_queue_t *queue, uint32_t n) {
  uint8_t *ptr;
  uint32_t size;

  size = sizeof_eassertion(n);
  resize_eassertion_queue(queue, size);
  ptr = queue->data + queue->top;
  queue->top += size;
  assert(queue->top <= queue->size);

  return (eassertion_t *) ptr;
}


/*
 * Generic push
 */
void egraph_fact_push(egraph_fact_queue_t *queue, const egraph_fact_desc_t *fact) {
  eassertion_t *a;
  uint32_t i;

  a = eassertion_alloc(queue, fact->arity);
  a->hint = fact->hint;
  a->payload = fact->payload;
  a->tag = mk_eassertion_tag(fact->kind, fact->arity);
  a->id = fact->id;
  for (i=0; i<fact->arity; i++) {
    a->var[i] = fact->data[i];
  }
}


/*
 * Generic push with inline integer payload
 */
void egraph_fact_push_words(egraph_fact_queue_t *queue, egraph_fact_kind_t kind, uint32_t n,
                            const int32_t *v, int32_t id, composite_t *hint, void *payload) {
  egraph_fact_desc_t fact;

  fact.kind = kind;
  fact.arity = n;
  fact.data = v;
  fact.hint = hint;
  fact.payload = payload;
  fact.id = id;
  egraph_fact_push(queue, &fact);
}


/*
 * Push a fact with a single literal payload
 */
void egraph_fact_push_literal(egraph_fact_queue_t *queue, egraph_fact_kind_t kind, literal_t l,
                              int32_t id, composite_t *hint, void *payload) {
  int32_t word[1];

  word[0] = l;
  egraph_fact_push_words(queue, kind, 1, word, id, hint, payload);
}


/*
 * Add x1 == x2 to the queue
 */
void eassertion_push_eq(eassertion_queue_t *queue, thvar_t x1, thvar_t x2, int32_t id) {
  int32_t var[2];

  var[0] = x1;
  var[1] = x2;
  egraph_fact_push_words(queue, EGRAPH_FACT_VAR_EQ, 2, var, id, NULL, NULL);
}


/*
 * Add x1 != x2 to the queue, with hint for explanations
 */
void eassertion_push_diseq(eassertion_queue_t *queue, thvar_t x1, thvar_t x2, composite_t *hint) {
  int32_t var[2];

  var[0] = x1;
  var[1] = x2;
  egraph_fact_push_words(queue, EGRAPH_FACT_VAR_DISEQ, 2, var, 0, hint, NULL);
}


/*
 * Add (distinct v[0] ... v[n-1]) to the queue with hint for explanations
 */
void eassertion_push_distinct(eassertion_queue_t *queue, uint32_t n, thvar_t *v, composite_t *hint) {
  egraph_fact_push_words(queue, EGRAPH_FACT_VAR_DISTINCT, n, v, 0, hint, NULL);
}
