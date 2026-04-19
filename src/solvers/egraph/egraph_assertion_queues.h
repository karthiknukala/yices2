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
 * Queue for storing hub facts sent by the egraph to theory solvers.
 * Solvers process these facts when the egraph scheduler asks them to run.
 *
 * The queue started as an equality-only assertion list.  It now stores a
 * wider set of fact kinds, while preserving the old APIs and type aliases
 * so existing backends can keep compiling during the migration.
 *
 * Each fact is stored as:
 * - tag: encode the fact kind and inline arity
 * - hint: optional explanation hint
 * - payload: optional opaque pointer owned by the producer
 * - id: optional integer handle (e.g., an egraph edge id)
 * - var[0 ... n-1]: inline integer payload (theory variables, literals, ...)
 */

#ifndef __EGRAPH_ASSERTION_QUEUES_H
#define __EGRAPH_ASSERTION_QUEUES_H

#include <stdint.h>
#include <stddef.h>
#include <limits.h>
#include <assert.h>

#include "solvers/egraph/egraph_types.h"


typedef egraph_fact_kind_t eassertion_kind_t;

#define EGRAPH_VAR_EQ EGRAPH_FACT_VAR_EQ
#define EGRAPH_VAR_DISEQ EGRAPH_FACT_VAR_DISEQ
#define EGRAPH_VAR_DISTINCT EGRAPH_FACT_VAR_DISTINCT

typedef struct egraph_fact_desc_s {
  egraph_fact_kind_t kind;
  uint32_t arity;
  const int32_t *data;
  composite_t *hint;
  void *payload;
  int32_t id;
} egraph_fact_desc_t;

/*
 * Assertion descriptor
 * - the tag encodes kind + arity
 */
typedef struct eassertion_s {
  composite_t *hint;
  void *payload;
  uint32_t tag;
  int32_t id;
  int32_t var[0]; // generic inline payload, real size depends on arity
} eassertion_t;

typedef eassertion_t egraph_fact_t;


/*
 * Tag constructor
 * - 4 low order bits encode the kind
 * - 28 high order bits contain the arity
 */
#define MAX_EASSERTION_ARITY (1U<<28)
#define EASSERTION_KIND_MASK ((uint32_t) 0xF)

static inline uint32_t mk_eassertion_tag(eassertion_kind_t k, uint32_t n) {
  assert (n < MAX_EASSERTION_ARITY);
  return (n << 4) | k;
}

static inline uint32_t mk_var_eq_tag(void) {
  return mk_eassertion_tag(EGRAPH_FACT_VAR_EQ, 2);
}

static inline uint32_t mk_var_diseq_tag(void) {
  return mk_eassertion_tag(EGRAPH_FACT_VAR_DISEQ, 2);
}

static inline uint32_t mk_var_distinct_tag(uint32_t n) {
  return mk_eassertion_tag(EGRAPH_FACT_VAR_DISTINCT, n);
}


/*
 * Extract kind and arity from the tag
 */
static inline eassertion_kind_t eassertion_tag_kind(uint32_t tag) {
  return (eassertion_kind_t) (tag & EASSERTION_KIND_MASK);
}

static inline uint32_t eassertion_tag_arity(uint32_t tag) {
  return tag>>4;
}


/*
 * Size of an assertion object of arity n:
 * - on 64bit machines, we round the size up to a multiple of 8
 */
static inline size_t align_size(size_t d) {
#if (ULONG_MAX == 4294967295UL)
  return (d + 3) & ~((size_t) 3); // 32 bits
#elif (ULONG_MAX == 18446744073709551615UL)
  return (d + 7) & ~((size_t) 7);  // 64 bits
#else
#error Could not find pointer alignment
#endif
}

static inline uint32_t sizeof_eassertion(uint32_t n) {
  return (uint32_t) align_size(sizeof(eassertion_t) + n * sizeof(uint32_t));
}



/*
 * Extract the kind, arity, size from an assertion a
 */
static inline eassertion_kind_t eassertion_get_kind(eassertion_t *a) {
  return eassertion_tag_kind(a->tag);
}

static inline uint32_t eassertion_get_arity(eassertion_t *a) {
  return eassertion_tag_arity(a->tag);
}

static inline size_t eassertion_get_size(eassertion_t *a) {
  return sizeof_eassertion(eassertion_get_arity(a));
}

static inline void *eassertion_get_payload(eassertion_t *a) {
  return a->payload;
}





#define DEF_EASSERTION_QUEUE_SIZE 10000
#define MAX_EASSERTION_QUEUE_SIZE UINT32_MAX


/*
 * Initialize the queue (empty)
 */
extern void init_eassertion_queue(eassertion_queue_t *queue);

/*
 * Delete the queue: free all memory
 */
extern void delete_eassertion_queue(eassertion_queue_t *queue);


/*
 * Empty the queue
 */
static inline void reset_eassertion_queue(eassertion_queue_t *queue) {
  queue->top = 0;
}


/*
 * Add facts to the queue
 */
extern void egraph_fact_push(egraph_fact_queue_t *queue, const egraph_fact_desc_t *fact);
extern void egraph_fact_push_words(egraph_fact_queue_t *queue, egraph_fact_kind_t kind, uint32_t n,
                                   const int32_t *a, int32_t id, composite_t *hint, void *payload);
extern void egraph_fact_push_literal(egraph_fact_queue_t *queue, egraph_fact_kind_t kind, literal_t l,
                                     int32_t id, composite_t *hint, void *payload);
extern void eassertion_push_eq(eassertion_queue_t *queue, thvar_t x1, thvar_t x2, int32_t id);
extern void eassertion_push_diseq(eassertion_queue_t *queue, thvar_t x1, thvar_t x2, composite_t *hint);
extern void eassertion_push_distinct(eassertion_queue_t *queue, uint32_t n, thvar_t *a, composite_t *hint);



/*
 * Operation to scan the queue: nothing can be added to the queue
 * while these operations are being used.
 */

/*
 * Check whether the queue is empty
 */
static inline bool eassertion_queue_is_empty(eassertion_queue_t *queue) {
  return queue->top == 0;
}

static inline bool eassertion_queue_is_nonempty(eassertion_queue_t *queue) {
  return queue->top > 0;
}

/*
 * First assertion in the queue
 */
static inline eassertion_t *eassertion_queue_start(eassertion_queue_t *queue) {
  return (eassertion_t *) queue->data;
}

/*
 * Get the end pointer
 */
static inline eassertion_t *eassertion_queue_end(eassertion_queue_t *queue) {
  assert(queue->data != NULL);
  return (eassertion_t *) (queue->data + queue->top);
}

/*
 * Pointer to the assertion that follows a in queue->data
 */
static inline eassertion_t *eassertion_next(eassertion_t *a) {
  return (eassertion_t *) (((uint8_t *) a) + eassertion_get_size(a));
}




#endif /* __EGRAPH_ASSERTION_QUEUES_H */
