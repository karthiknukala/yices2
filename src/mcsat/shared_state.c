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

#include "mcsat/shared_state.h"

#ifndef HAVE_LIBURCU_SHARED_MCSAT

struct mcsat_shared_state_s {
  int unused;
};

mcsat_shared_state_t* mcsat_shared_state_acquire(term_table_t* terms, type_table_t* types) {
  (void) terms;
  (void) types;
  return NULL;
}

void mcsat_shared_state_release(mcsat_shared_state_t* state) {
  (void) state;
}

bool mcsat_shared_state_is_enabled(const mcsat_shared_state_t* state) {
  return state != NULL;
}

void mcsat_shared_state_term_lock(mcsat_shared_state_t* state) {
  (void) state;
}

void mcsat_shared_state_term_unlock(mcsat_shared_state_t* state) {
  (void) state;
}

void mcsat_shared_state_publish_term(mcsat_shared_state_t* state, term_t term) {
  (void) state;
  (void) term;
}

int32_t mcsat_shared_state_lookup_variable(mcsat_shared_state_t* state, term_t term) {
  (void) state;
  (void) term;
  return 0;
}

int32_t mcsat_shared_state_get_variable(mcsat_shared_state_t* state, term_t term, bool* created) {
  (void) state;
  (void) term;
  if (created != NULL) {
    *created = false;
  }
  return 0;
}

term_t mcsat_shared_state_get_variable_term(mcsat_shared_state_t* state, int32_t var) {
  (void) state;
  (void) var;
  return NULL_TERM;
}

uint32_t mcsat_shared_state_variable_limit(mcsat_shared_state_t* state) {
  (void) state;
  return 0;
}

uint64_t mcsat_shared_state_new_lemma_session(mcsat_shared_state_t* state) {
  (void) state;
  return 0;
}

bool mcsat_shared_state_publish_lemma(mcsat_shared_state_t* state, uint64_t session, term_t lemma, uint64_t* seq_out) {
  (void) state;
  (void) session;
  (void) lemma;
  if (seq_out != NULL) {
    *seq_out = 0;
  }
  return false;
}

uint64_t mcsat_shared_state_latest_lemma_seq(mcsat_shared_state_t* state) {
  (void) state;
  return 0;
}

term_t mcsat_shared_state_get_lemma(mcsat_shared_state_t* state, uint64_t session, uint64_t seq) {
  (void) state;
  (void) session;
  (void) seq;
  return NULL_TERM;
}

#else

#define URCU_API_MAP

#include <assert.h>
#include <pthread.h>
#include <sched.h>
#include <string.h>

#include <urcu/urcu-memb.h>
#include <urcu/rculfhash.h>

#include "utils/error.h"
#include "utils/hash_functions.h"
#include "utils/memalloc.h"
#include "utils/ptr_vectors.h"

#define MCSAT_SHARED_SLOT_CHUNK 1024

typedef struct {
  term_t term;
  struct cds_lfht_node node;
} shared_term_node_t;

typedef struct {
  term_t term;
  int32_t var;
  struct cds_lfht_node node;
} shared_variable_node_t;

typedef struct {
  term_t lemma;
  uint64_t session;
  uint64_t seq;
  struct cds_lfht_node node;
} shared_lemma_node_t;

typedef struct {
  term_t lemma;
  uint64_t session;
} shared_lemma_slot_t;

typedef struct {
  term_t lemma;
  uint64_t session;
} shared_lemma_key_t;

struct mcsat_shared_state_s {
  term_table_t* terms;
  type_table_t* types;

  pthread_mutex_t storage_lock;
  pthread_mutex_t term_lock;
  uint32_t refcount;

  struct cds_lfht* shared_terms;
  struct cds_lfht* shared_variables;
  struct cds_lfht* shared_lemmas;

  pvector_t term_nodes;
  pvector_t variable_nodes;
  pvector_t lemma_nodes;

  pvector_t variable_terms;
  pvector_t lemma_terms;

  volatile uint32_t next_variable_id;
  volatile uint32_t max_variable_id;
  volatile uint64_t next_lemma_session;
  volatile uint64_t next_lemma_seq;
  volatile uint64_t max_lemma_seq;
};

static pthread_mutex_t global_shared_state_lock = PTHREAD_MUTEX_INITIALIZER;
static mcsat_shared_state_t* global_shared_state = NULL;

static pthread_once_t shared_state_key_once = PTHREAD_ONCE_INIT;
static pthread_key_t shared_state_thread_key;

static
void shared_state_thread_destructor(void* value) {
  if (value != NULL) {
    urcu_memb_unregister_thread();
  }
}

static
void shared_state_make_key(void) {
  int32_t code;

  code = pthread_key_create(&shared_state_thread_key, shared_state_thread_destructor);
  if (code != 0) {
    perror_fatal("pthread_key_create");
  }
}

static
void shared_state_register_thread(void) {
  int32_t code;

  code = pthread_once(&shared_state_key_once, shared_state_make_key);
  if (code != 0) {
    perror_fatal("pthread_once");
  }

  if (pthread_getspecific(shared_state_thread_key) == NULL) {
    urcu_memb_register_thread();
    code = pthread_setspecific(shared_state_thread_key, (void*) 1);
    if (code != 0) {
      perror_fatal("pthread_setspecific");
    }
  }
}

static inline
uint32_t shared_hash_term(term_t term) {
  return jenkins_hash_int32(term);
}

static
int shared_term_match(struct cds_lfht_node* node, const void* key) {
  const shared_term_node_t* entry = cds_lfht_entry(node, const shared_term_node_t, node);
  return entry->term == *(const term_t*) key;
}

static
int shared_variable_match(struct cds_lfht_node* node, const void* key) {
  const shared_variable_node_t* entry = cds_lfht_entry(node, const shared_variable_node_t, node);
  return entry->term == *(const term_t*) key;
}

static
int shared_lemma_match(struct cds_lfht_node* node, const void* key) {
  const shared_lemma_node_t* entry = cds_lfht_entry(node, const shared_lemma_node_t, node);
  const shared_lemma_key_t* lemma_key = (const shared_lemma_key_t*) key;
  return entry->lemma == lemma_key->lemma && entry->session == lemma_key->session;
}

static
struct cds_lfht* shared_state_new_table(void) {
  return cds_lfht_new(1, 1, 0, CDS_LFHT_AUTO_RESIZE | CDS_LFHT_ACCOUNTING, NULL);
}

static
void shared_state_init(mcsat_shared_state_t* state, term_table_t* terms, type_table_t* types) {
  int32_t code;
  pthread_mutexattr_t attr;

  state->terms = terms;
  state->types = types;
  state->refcount = 0;
  state->next_variable_id = 0;
  state->max_variable_id = 0;
  state->next_lemma_session = 0;
  state->next_lemma_seq = 0;
  state->max_lemma_seq = 0;

  code = pthread_mutex_init(&state->storage_lock, NULL);
  if (code != 0) {
    perror_fatal("pthread_mutex_init");
  }

  code = pthread_mutexattr_init(&attr);
  if (code != 0) {
    perror_fatal("pthread_mutexattr_init");
  }
  code = pthread_mutexattr_settype(&attr, PTHREAD_MUTEX_RECURSIVE);
  if (code != 0) {
    perror_fatal("pthread_mutexattr_settype");
  }
  code = pthread_mutex_init(&state->term_lock, &attr);
  if (code != 0) {
    perror_fatal("pthread_mutex_init");
  }
  pthread_mutexattr_destroy(&attr);

  init_pvector(&state->term_nodes, 0);
  init_pvector(&state->variable_nodes, 0);
  init_pvector(&state->lemma_nodes, 0);
  init_pvector(&state->variable_terms, 0);
  init_pvector(&state->lemma_terms, 0);

  state->shared_terms = shared_state_new_table();
  state->shared_variables = shared_state_new_table();
  state->shared_lemmas = shared_state_new_table();
  if (state->shared_terms == NULL || state->shared_variables == NULL || state->shared_lemmas == NULL) {
    out_of_memory();
  }
}

static
void shared_state_free_term_chunks(pvector_t* chunks) {
  uint32_t i;

  for (i = 0; i < chunks->size; ++i) {
    safe_free(chunks->data[i]);
  }
  delete_pvector(chunks);
}

static
void shared_state_free_lemma_chunks(pvector_t* chunks) {
  uint32_t i;

  for (i = 0; i < chunks->size; ++i) {
    safe_free(chunks->data[i]);
  }
  delete_pvector(chunks);
}

static
void shared_state_free_nodes(pvector_t* nodes) {
  uint32_t i;

  for (i = 0; i < nodes->size; ++i) {
    safe_free(nodes->data[i]);
  }
  delete_pvector(nodes);
}

static
void shared_state_destroy(mcsat_shared_state_t* state) {
  pthread_attr_t* attr = NULL;

  assert(state != NULL);
  shared_state_register_thread();

  if (state->shared_terms != NULL) {
    cds_lfht_destroy(state->shared_terms, &attr);
  }
  if (state->shared_variables != NULL) {
    cds_lfht_destroy(state->shared_variables, &attr);
  }
  if (state->shared_lemmas != NULL) {
    cds_lfht_destroy(state->shared_lemmas, &attr);
  }

  shared_state_free_nodes(&state->term_nodes);
  shared_state_free_nodes(&state->variable_nodes);
  shared_state_free_nodes(&state->lemma_nodes);
  shared_state_free_term_chunks(&state->variable_terms);
  shared_state_free_lemma_chunks(&state->lemma_terms);

  pthread_mutex_destroy(&state->term_lock);
  pthread_mutex_destroy(&state->storage_lock);
  safe_free(state);
}

static
void shared_state_update_u32_max(volatile uint32_t* target, uint32_t value) {
  uint32_t old;

  old = *target;
  while (old < value) {
    uint32_t prev = __sync_val_compare_and_swap(target, old, value);
    if (prev == old) {
      break;
    }
    old = prev;
  }
}

static
void shared_state_update_u64_max(volatile uint64_t* target, uint64_t value) {
  uint64_t old;

  old = *target;
  while (old < value) {
    uint64_t prev = __sync_val_compare_and_swap(target, old, value);
    if (prev == old) {
      break;
    }
    old = prev;
  }
}

static
void shared_state_ensure_term_chunk(mcsat_shared_state_t* state, pvector_t* chunks, uint64_t slot) {
  uint64_t chunk_id;

  chunk_id = (slot - 1) / MCSAT_SHARED_SLOT_CHUNK;
  pthread_mutex_lock(&state->storage_lock);
  while (chunks->size <= chunk_id) {
    term_t* chunk = (term_t*) safe_malloc(MCSAT_SHARED_SLOT_CHUNK * sizeof(term_t));
    uint32_t i;
    for (i = 0; i < MCSAT_SHARED_SLOT_CHUNK; ++i) {
      chunk[i] = NULL_TERM;
    }
    pvector_push(chunks, chunk);
  }
  pthread_mutex_unlock(&state->storage_lock);
}

static
void shared_state_ensure_lemma_chunk(mcsat_shared_state_t* state, pvector_t* chunks, uint64_t slot) {
  uint64_t chunk_id;

  chunk_id = (slot - 1) / MCSAT_SHARED_SLOT_CHUNK;
  pthread_mutex_lock(&state->storage_lock);
  while (chunks->size <= chunk_id) {
    shared_lemma_slot_t* chunk = (shared_lemma_slot_t*) safe_malloc(MCSAT_SHARED_SLOT_CHUNK * sizeof(shared_lemma_slot_t));
    uint32_t i;
    for (i = 0; i < MCSAT_SHARED_SLOT_CHUNK; ++i) {
      chunk[i].lemma = NULL_TERM;
      chunk[i].session = 0;
    }
    pvector_push(chunks, chunk);
  }
  pthread_mutex_unlock(&state->storage_lock);
}

static inline
term_t shared_state_load_term_slot(mcsat_shared_state_t* state, pvector_t* chunks, uint64_t slot) {
  uint64_t chunk_id;
  term_t* chunk;
  term_t term;

  if (slot == 0) {
    return NULL_TERM;
  }

  chunk_id = (slot - 1) / MCSAT_SHARED_SLOT_CHUNK;
  pthread_mutex_lock(&state->storage_lock);
  if (chunk_id >= chunks->size) {
    pthread_mutex_unlock(&state->storage_lock);
    return NULL_TERM;
  }

  chunk = (term_t*) chunks->data[chunk_id];
  term = chunk[(slot - 1) % MCSAT_SHARED_SLOT_CHUNK];
  pthread_mutex_unlock(&state->storage_lock);
  return term;
}

static inline
shared_lemma_slot_t shared_state_load_lemma_slot(mcsat_shared_state_t* state, pvector_t* chunks, uint64_t slot) {
  uint64_t chunk_id;
  shared_lemma_slot_t* chunk;
  shared_lemma_slot_t lemma_slot;

  lemma_slot.lemma = NULL_TERM;
  lemma_slot.session = 0;

  if (slot == 0) {
    return lemma_slot;
  }

  chunk_id = (slot - 1) / MCSAT_SHARED_SLOT_CHUNK;
  pthread_mutex_lock(&state->storage_lock);
  if (chunk_id >= chunks->size) {
    pthread_mutex_unlock(&state->storage_lock);
    return lemma_slot;
  }

  chunk = (shared_lemma_slot_t*) chunks->data[chunk_id];
  lemma_slot = chunk[(slot - 1) % MCSAT_SHARED_SLOT_CHUNK];
  pthread_mutex_unlock(&state->storage_lock);
  return lemma_slot;
}

static
void shared_state_store_term_slot(mcsat_shared_state_t* state, pvector_t* chunks, uint64_t slot, term_t term) {
  term_t* chunk;

  shared_state_ensure_term_chunk(state, chunks, slot);
  pthread_mutex_lock(&state->storage_lock);
  chunk = (term_t*) chunks->data[(slot - 1) / MCSAT_SHARED_SLOT_CHUNK];
  chunk[(slot - 1) % MCSAT_SHARED_SLOT_CHUNK] = term;
  pthread_mutex_unlock(&state->storage_lock);
  __sync_synchronize();
}

static
void shared_state_store_lemma_slot(mcsat_shared_state_t* state, pvector_t* chunks, uint64_t slot, uint64_t session, term_t lemma) {
  shared_lemma_slot_t* chunk;

  shared_state_ensure_lemma_chunk(state, chunks, slot);
  pthread_mutex_lock(&state->storage_lock);
  chunk = (shared_lemma_slot_t*) chunks->data[(slot - 1) / MCSAT_SHARED_SLOT_CHUNK];
  chunk[(slot - 1) % MCSAT_SHARED_SLOT_CHUNK].lemma = lemma;
  chunk[(slot - 1) % MCSAT_SHARED_SLOT_CHUNK].session = session;
  pthread_mutex_unlock(&state->storage_lock);
  __sync_synchronize();
}

static
term_t shared_state_wait_term_slot(mcsat_shared_state_t* state, pvector_t* chunks, uint64_t slot) {
  term_t term;

  term = shared_state_load_term_slot(state, chunks, slot);
  while (term == NULL_TERM) {
    sched_yield();
    term = shared_state_load_term_slot(state, chunks, slot);
  }
  return term;
}

static
shared_lemma_slot_t shared_state_wait_lemma_slot(mcsat_shared_state_t* state, pvector_t* chunks, uint64_t slot) {
  shared_lemma_slot_t lemma_slot;

  lemma_slot = shared_state_load_lemma_slot(state, chunks, slot);
  while (lemma_slot.lemma == NULL_TERM) {
    sched_yield();
    lemma_slot = shared_state_load_lemma_slot(state, chunks, slot);
  }
  return lemma_slot;
}

static
void shared_state_record_node(mcsat_shared_state_t* state, pvector_t* nodes, void* node) {
  pthread_mutex_lock(&state->storage_lock);
  pvector_push(nodes, node);
  pthread_mutex_unlock(&state->storage_lock);
}

mcsat_shared_state_t* mcsat_shared_state_acquire(term_table_t* terms, type_table_t* types) {
  mcsat_shared_state_t* state;

  shared_state_register_thread();

  pthread_mutex_lock(&global_shared_state_lock);
  state = global_shared_state;
  if (state == NULL) {
    state = (mcsat_shared_state_t*) safe_malloc(sizeof(mcsat_shared_state_t));
    shared_state_init(state, terms, types);
    global_shared_state = state;
  } else {
    assert(state->terms == terms);
    assert(state->types == types);
  }
  state->refcount ++;
  pthread_mutex_unlock(&global_shared_state_lock);

  return state;
}

void mcsat_shared_state_release(mcsat_shared_state_t* state) {
  bool destroy = false;

  if (state == NULL) {
    return;
  }

  pthread_mutex_lock(&global_shared_state_lock);
  assert(state->refcount > 0);
  state->refcount --;
  if (state->refcount == 0) {
    assert(global_shared_state == state);
    global_shared_state = NULL;
    destroy = true;
  }
  pthread_mutex_unlock(&global_shared_state_lock);

  if (destroy) {
    shared_state_destroy(state);
  }
}

bool mcsat_shared_state_is_enabled(const mcsat_shared_state_t* state) {
  return state != NULL;
}

void mcsat_shared_state_term_lock(mcsat_shared_state_t* state) {
  if (state == NULL) {
    return;
  }
  pthread_mutex_lock(&state->term_lock);
}

void mcsat_shared_state_term_unlock(mcsat_shared_state_t* state) {
  if (state == NULL) {
    return;
  }
  pthread_mutex_unlock(&state->term_lock);
}

void mcsat_shared_state_publish_term(mcsat_shared_state_t* state, term_t term) {
  shared_term_node_t* entry;
  struct cds_lfht_node* found;
  struct cds_lfht_node* node;
  term_t key;

  if (state == NULL || term == NULL_TERM) {
    return;
  }

  key = unsigned_term(term);
  shared_state_register_thread();

  entry = (shared_term_node_t*) safe_malloc(sizeof(shared_term_node_t));
  entry->term = key;
  cds_lfht_node_init(&entry->node);

  urcu_memb_read_lock();
  node = cds_lfht_add_unique(state->shared_terms, shared_hash_term(key), shared_term_match, &key, &entry->node);
  found = node;
  urcu_memb_read_unlock();

  if (found == &entry->node) {
    shared_state_record_node(state, &state->term_nodes, entry);
  } else {
    safe_free(entry);
  }
}

int32_t mcsat_shared_state_lookup_variable(mcsat_shared_state_t* state, term_t term) {
  struct cds_lfht_iter iter;
  struct cds_lfht_node* node;
  shared_variable_node_t* entry;
  term_t key;

  if (state == NULL || term == NULL_TERM) {
    return 0;
  }

  key = unsigned_term(term);
  shared_state_register_thread();

  urcu_memb_read_lock();
  cds_lfht_lookup(state->shared_variables, shared_hash_term(key), shared_variable_match, &key, &iter);
  node = cds_lfht_iter_get_node(&iter);
  if (node == NULL) {
    urcu_memb_read_unlock();
    return 0;
  }
  entry = cds_lfht_entry(node, shared_variable_node_t, node);
  urcu_memb_read_unlock();

  (void) shared_state_wait_term_slot(state, &state->variable_terms, entry->var);
  return entry->var;
}

int32_t mcsat_shared_state_get_variable(mcsat_shared_state_t* state, term_t term, bool* created) {
  shared_variable_node_t* entry;
  struct cds_lfht_node* found;
  struct cds_lfht_node* node;
  shared_variable_node_t* found_entry;
  term_t key;

  if (created != NULL) {
    *created = false;
  }
  if (state == NULL || term == NULL_TERM) {
    return 0;
  }

  key = unsigned_term(term);
  shared_state_register_thread();
  mcsat_shared_state_publish_term(state, key);

  entry = (shared_variable_node_t*) safe_malloc(sizeof(shared_variable_node_t));
  entry->term = key;
  entry->var = (int32_t) __sync_add_and_fetch(&state->next_variable_id, 1);
  cds_lfht_node_init(&entry->node);

  urcu_memb_read_lock();
  node = cds_lfht_add_unique(state->shared_variables, shared_hash_term(key), shared_variable_match, &key, &entry->node);
  found = node;
  urcu_memb_read_unlock();

  if (found == &entry->node) {
    shared_state_store_term_slot(state, &state->variable_terms, entry->var, key);
    shared_state_update_u32_max(&state->max_variable_id, (uint32_t) entry->var);
    shared_state_record_node(state, &state->variable_nodes, entry);
    if (created != NULL) {
      *created = true;
    }
    return entry->var;
  }

  found_entry = cds_lfht_entry(found, shared_variable_node_t, node);
  safe_free(entry);
  (void) shared_state_wait_term_slot(state, &state->variable_terms, found_entry->var);
  return found_entry->var;
}

term_t mcsat_shared_state_get_variable_term(mcsat_shared_state_t* state, int32_t var) {
  if (state == NULL || var <= 0) {
    return NULL_TERM;
  }
  return shared_state_load_term_slot(state, &state->variable_terms, (uint64_t) var);
}

uint32_t mcsat_shared_state_variable_limit(mcsat_shared_state_t* state) {
  if (state == NULL) {
    return 0;
  }
  return state->max_variable_id;
}

uint64_t mcsat_shared_state_new_lemma_session(mcsat_shared_state_t* state) {
  if (state == NULL) {
    return 0;
  }
  shared_state_register_thread();
  return __sync_add_and_fetch(&state->next_lemma_session, 1);
}

bool mcsat_shared_state_publish_lemma(mcsat_shared_state_t* state, uint64_t session, term_t lemma, uint64_t* seq_out) {
  shared_lemma_node_t* entry;
  struct cds_lfht_node* found;
  struct cds_lfht_node* node;
  shared_lemma_node_t* found_entry;
  shared_lemma_key_t key;
  shared_lemma_slot_t lemma_slot;
  uint64_t seq;

  if (seq_out != NULL) {
    *seq_out = 0;
  }
  if (state == NULL || session == 0 || lemma == NULL_TERM) {
    return false;
  }

  key.lemma = lemma;
  key.session = session;
  shared_state_register_thread();
  mcsat_shared_state_publish_term(state, key.lemma);

  entry = (shared_lemma_node_t*) safe_malloc(sizeof(shared_lemma_node_t));
  entry->lemma = key.lemma;
  entry->session = key.session;
  entry->seq = __sync_add_and_fetch(&state->next_lemma_seq, 1);
  cds_lfht_node_init(&entry->node);

  urcu_memb_read_lock();
  node = cds_lfht_add_unique(state->shared_lemmas,
                             jenkins_hash_mix2(shared_hash_term(key.lemma), jenkins_hash_uint64(key.session)),
                             shared_lemma_match,
                             &key,
                             &entry->node);
  found = node;
  urcu_memb_read_unlock();

  if (found == &entry->node) {
    shared_state_store_lemma_slot(state, &state->lemma_terms, entry->seq, entry->session, entry->lemma);
    shared_state_update_u64_max(&state->max_lemma_seq, entry->seq);
    shared_state_record_node(state, &state->lemma_nodes, entry);
    if (seq_out != NULL) {
      *seq_out = entry->seq;
    }
    return true;
  }

  found_entry = cds_lfht_entry(found, shared_lemma_node_t, node);
  safe_free(entry);
  seq = found_entry->seq;
  lemma_slot = shared_state_wait_lemma_slot(state, &state->lemma_terms, seq);
  if (lemma_slot.session != found_entry->session) {
    return false;
  }
  if (seq_out != NULL) {
    *seq_out = seq;
  }
  return false;
}

uint64_t mcsat_shared_state_latest_lemma_seq(mcsat_shared_state_t* state) {
  if (state == NULL) {
    return 0;
  }
  return state->max_lemma_seq;
}

term_t mcsat_shared_state_get_lemma(mcsat_shared_state_t* state, uint64_t session, uint64_t seq) {
  shared_lemma_slot_t lemma_slot;

  if (state == NULL || session == 0 || seq == 0 || seq > state->max_lemma_seq) {
    return NULL_TERM;
  }
  lemma_slot = shared_state_load_lemma_slot(state, &state->lemma_terms, seq);
  if (lemma_slot.session != session) {
    return NULL_TERM;
  }
  return lemma_slot.lemma;
}

#endif
