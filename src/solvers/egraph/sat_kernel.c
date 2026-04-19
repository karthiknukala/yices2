#include "solvers/egraph/sat_kernel.h"

void init_sat_kernel(sat_kernel_t *kernel) {
  kernel->backend = NULL;
  kernel->api = NULL;
}

void reset_sat_kernel(sat_kernel_t *kernel) {
  init_sat_kernel(kernel);
}

void sat_kernel_bind(sat_kernel_t *kernel, void *backend, th_sat_interface_t *api) {
  assert(kernel != NULL);
  assert(backend != NULL);
  assert(api != NULL);

  kernel->backend = backend;
  kernel->api = api;
}
