/*
 * Native floating-point value helpers for MCSAT.
 */

#pragma once

#include <stdbool.h>

#include "mcsat/fp/fp_dyadic.h"
#include "terms/terms.h"

bool fp_value_is_nan(const fp_const_t *v);
bool fp_value_is_infinite(const fp_const_t *v);
bool fp_value_is_zero(const fp_const_t *v);
bool fp_value_is_finite(const fp_const_t *v);
bool fp_value_is_subnormal(const fp_const_t *v);
bool fp_value_is_normal(const fp_const_t *v);
bool fp_value_to_dyadic(const fp_const_t *v, fp_dyadic_t *d);
int fp_value_cmp(const fp_const_t *a, const fp_const_t *b);
void fp_value_make_nan(fp_const_t *v, uint32_t ebits, uint32_t sbits);
void fp_value_make_inf(fp_const_t *v, uint32_t ebits, uint32_t sbits, bool sign);
void fp_value_make_zero(fp_const_t *v, uint32_t ebits, uint32_t sbits, bool sign);
