/*
 * Exact dyadic rationals for the MCSAT floating-point plugin.
 */

#pragma once

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <gmp.h>

typedef struct fp_dyadic_s {
  mpz_t significand;
  int32_t exponent;
} fp_dyadic_t;

void fp_dyadic_init(fp_dyadic_t *d);
void fp_dyadic_destruct(fp_dyadic_t *d);
void fp_dyadic_set(fp_dyadic_t *d, const fp_dyadic_t *src);
void fp_dyadic_set_int64(fp_dyadic_t *d, int64_t x);
void fp_dyadic_set_mpz_exp(fp_dyadic_t *d, const mpz_t z, int32_t exponent);
void fp_dyadic_normalize(fp_dyadic_t *d);
bool fp_dyadic_is_zero(const fp_dyadic_t *d);
int fp_dyadic_sgn(const fp_dyadic_t *d);
void fp_dyadic_neg(fp_dyadic_t *d);
void fp_dyadic_add(fp_dyadic_t *r, const fp_dyadic_t *a, const fp_dyadic_t *b);
void fp_dyadic_sub(fp_dyadic_t *r, const fp_dyadic_t *a, const fp_dyadic_t *b);
void fp_dyadic_mul(fp_dyadic_t *r, const fp_dyadic_t *a, const fp_dyadic_t *b);
int fp_dyadic_cmp(const fp_dyadic_t *a, const fp_dyadic_t *b);
uint32_t fp_dyadic_log2_abs_floor(const fp_dyadic_t *d);
void fp_dyadic_print(FILE *out, const fp_dyadic_t *d);
