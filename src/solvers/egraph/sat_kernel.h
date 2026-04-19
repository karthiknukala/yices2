#ifndef __SAT_KERNEL_H
#define __SAT_KERNEL_H

#include <assert.h>

#include "solvers/egraph/egraph_types.h"

/*
 * Initialize/reset the SAT-kernel wrapper.
 * This does not allocate or free the concrete backend.
 */
extern void init_sat_kernel(sat_kernel_t *kernel);
extern void reset_sat_kernel(sat_kernel_t *kernel);
extern void sat_kernel_bind(sat_kernel_t *kernel, void *backend, th_sat_interface_t *api);

static inline bool sat_kernel_is_attached(const sat_kernel_t *kernel) {
  return kernel != NULL && kernel->backend != NULL && kernel->api != NULL;
}

static inline void *sat_kernel_backend(const sat_kernel_t *kernel) {
  assert(sat_kernel_is_attached(kernel));
  return kernel->backend;
}

static inline th_sat_interface_t *sat_kernel_api(const sat_kernel_t *kernel) {
  assert(sat_kernel_is_attached(kernel));
  return kernel->api;
}

#endif
