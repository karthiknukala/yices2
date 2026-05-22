/*
 * Exact dyadic rationals for the MCSAT floating-point plugin.
 */

#include "mcsat/fp/fp_dyadic.h"

#include <assert.h>
#include <inttypes.h>

void fp_dyadic_init(fp_dyadic_t *d) {
  mpz_init(d->significand);
  d->exponent = 0;
}

void fp_dyadic_destruct(fp_dyadic_t *d) {
  mpz_clear(d->significand);
}

void fp_dyadic_normalize(fp_dyadic_t *d) {
  unsigned long twos;

  if (mpz_sgn(d->significand) == 0) {
    d->exponent = 0;
    return;
  }

  twos = mpz_scan1(d->significand, 0);
  if (twos > 0) {
    mpz_fdiv_q_2exp(d->significand, d->significand, twos);
    d->exponent += (int32_t) twos;
  }
}

void fp_dyadic_set(fp_dyadic_t *d, const fp_dyadic_t *src) {
  mpz_set(d->significand, src->significand);
  d->exponent = src->exponent;
}

void fp_dyadic_set_int64(fp_dyadic_t *d, int64_t x) {
  mpz_set_si(d->significand, x);
  d->exponent = 0;
}

void fp_dyadic_set_mpz_exp(fp_dyadic_t *d, const mpz_t z, int32_t exponent) {
  mpz_set(d->significand, z);
  d->exponent = exponent;
  fp_dyadic_normalize(d);
}

bool fp_dyadic_is_zero(const fp_dyadic_t *d) {
  return mpz_sgn(d->significand) == 0;
}

int fp_dyadic_sgn(const fp_dyadic_t *d) {
  return mpz_sgn(d->significand);
}

void fp_dyadic_neg(fp_dyadic_t *d) {
  mpz_neg(d->significand, d->significand);
}

static void fp_dyadic_add_internal(fp_dyadic_t *r, const fp_dyadic_t *a, const fp_dyadic_t *b, bool subtract) {
  fp_dyadic_t tmp_a;
  fp_dyadic_t tmp_b;
  int32_t e;

  fp_dyadic_init(&tmp_a);
  fp_dyadic_init(&tmp_b);
  e = a->exponent < b->exponent ? a->exponent : b->exponent;

  mpz_set(tmp_a.significand, a->significand);
  if (a->exponent > e) {
    mpz_mul_2exp(tmp_a.significand, tmp_a.significand, (uint32_t) (a->exponent - e));
  }
  mpz_set(tmp_b.significand, b->significand);
  if (b->exponent > e) {
    mpz_mul_2exp(tmp_b.significand, tmp_b.significand, (uint32_t) (b->exponent - e));
  }

  if (subtract) {
    mpz_sub(r->significand, tmp_a.significand, tmp_b.significand);
  } else {
    mpz_add(r->significand, tmp_a.significand, tmp_b.significand);
  }
  r->exponent = e;
  fp_dyadic_normalize(r);

  fp_dyadic_destruct(&tmp_a);
  fp_dyadic_destruct(&tmp_b);
}

void fp_dyadic_add(fp_dyadic_t *r, const fp_dyadic_t *a, const fp_dyadic_t *b) {
  fp_dyadic_add_internal(r, a, b, false);
}

void fp_dyadic_sub(fp_dyadic_t *r, const fp_dyadic_t *a, const fp_dyadic_t *b) {
  fp_dyadic_add_internal(r, a, b, true);
}

void fp_dyadic_mul(fp_dyadic_t *r, const fp_dyadic_t *a, const fp_dyadic_t *b) {
  mpz_mul(r->significand, a->significand, b->significand);
  r->exponent = a->exponent + b->exponent;
  fp_dyadic_normalize(r);
}

int fp_dyadic_cmp(const fp_dyadic_t *a, const fp_dyadic_t *b) {
  fp_dyadic_t d;
  int result;

  fp_dyadic_init(&d);
  fp_dyadic_sub(&d, a, b);
  result = mpz_sgn(d.significand);
  fp_dyadic_destruct(&d);
  return result;
}

uint32_t fp_dyadic_log2_abs_floor(const fp_dyadic_t *d) {
  assert(!fp_dyadic_is_zero(d));
  return (uint32_t) mpz_sizeinbase(d->significand, 2) - 1;
}

void fp_dyadic_print(FILE *out, const fp_dyadic_t *d) {
  mpz_out_str(out, 10, d->significand);
  fprintf(out, " * 2^%"PRId32, d->exponent);
}
