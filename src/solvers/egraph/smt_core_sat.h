#ifndef __SMT_CORE_SAT_H
#define __SMT_CORE_SAT_H

#include "solvers/cdcl/smt_core.h"
#include "solvers/egraph/sat_kernel.h"

/*
 * Initialize a SAT-kernel wrapper backed by an smt_core instance.
 */
extern void init_smt_core_sat_kernel(sat_kernel_t *kernel, smt_core_t *core);

#endif
