/*
 * Directed IEEE rounding over exact dyadics.
 */

#pragma once

#include <stdbool.h>

#include "mcsat/fp/fp_dyadic.h"
#include "terms/terms.h"

bool fp_rounding_mode_is_directed(fp_rounding_mode_t mode);
bool fp_round_dyadic(fp_const_t *out, uint32_t ebits, uint32_t sbits,
                     fp_rounding_mode_t mode, const fp_dyadic_t *value);
