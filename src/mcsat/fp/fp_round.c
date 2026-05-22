/*
 * Directed IEEE rounding over exact dyadics.
 */

#include "mcsat/fp/fp_round.h"
#include "mcsat/fp/fp_value.h"

#include <assert.h>

bool fp_rounding_mode_is_directed(fp_rounding_mode_t mode) {
  return mode == FP_RTN || mode == FP_RTP || mode == FP_RTZ;
}

static uint64_t low_mask(uint32_t n) {
  assert(n < 64);
  return ((uint64_t) 1 << n) - 1u;
}

static bool should_increment(bool negative, fp_rounding_mode_t mode, bool inexact) {
  if (!inexact) {
    return false;
  }
  switch (mode) {
  case FP_RTP:
    return !negative;
  case FP_RTN:
    return negative;
  case FP_RTZ:
    return false;
  case FP_RNE:
  case FP_RNA:
    return false;
  }
  return false;
}

static void round_scaled_integer(mpz_t q, bool *inexact, const mpz_t n, int32_t shift) {
  mpz_t rem;

  if (shift >= 0) {
    mpz_mul_2exp(q, n, (uint32_t) shift);
    *inexact = false;
  } else {
    mpz_init(rem);
    mpz_fdiv_q_2exp(q, n, (uint32_t) -shift);
    mpz_fdiv_r_2exp(rem, n, (uint32_t) -shift);
    *inexact = mpz_sgn(rem) != 0;
    mpz_clear(rem);
  }
}

static void make_max_finite(fp_const_t *out, uint32_t ebits, uint32_t sbits, bool sign) {
  out->ebits = ebits;
  out->sbits = sbits;
  out->kind = FP_VALUE_NUMERAL;
  out->sign = sign;
  out->exponent = low_mask(ebits) - 1u;
  out->significand = low_mask(sbits - 1);
}

bool fp_round_dyadic(fp_const_t *out, uint32_t ebits, uint32_t sbits,
                     fp_rounding_mode_t mode, const fp_dyadic_t *value) {
  mpz_t n;
  mpz_t q;
  bool negative;
  bool inexact;
  uint32_t bitlen;
  int32_t bias;
  int32_t emin;
  int32_t emax;
  int32_t k;
  int32_t shift;

  assert(sbits > 1 && sbits <= 64);
  assert(ebits > 1 && ebits < 32);

  if (!fp_rounding_mode_is_directed(mode)) {
    return false;
  }

  if (fp_dyadic_is_zero(value)) {
    fp_value_make_zero(out, ebits, sbits, false);
    return true;
  }

  negative = fp_dyadic_sgn(value) < 0;
  bias = ((int32_t) 1 << (ebits - 1)) - 1;
  emin = 1 - bias;
  emax = bias;

  mpz_init(n);
  mpz_init(q);
  mpz_abs(n, value->significand);

  bitlen = (uint32_t) mpz_sizeinbase(n, 2);
  k = (int32_t) bitlen - 1 + value->exponent;

  if (k < emin) {
    shift = value->exponent - (emin - ((int32_t) sbits - 1));
    round_scaled_integer(q, &inexact, n, shift);
    if (should_increment(negative, mode, inexact)) {
      mpz_add_ui(q, q, 1);
    }
    if (mpz_sgn(q) == 0) {
      fp_value_make_zero(out, ebits, sbits, negative);
    } else if (mpz_cmp_ui(q, ((uint64_t) 1) << (sbits - 1)) >= 0) {
      out->ebits = ebits;
      out->sbits = sbits;
      out->kind = FP_VALUE_NUMERAL;
      out->sign = negative;
      out->exponent = 1;
      out->significand = 0;
    } else {
      out->ebits = ebits;
      out->sbits = sbits;
      out->kind = FP_VALUE_NUMERAL;
      out->sign = negative;
      out->exponent = 0;
      out->significand = mpz_get_ui(q);
    }
    mpz_clear(q);
    mpz_clear(n);
    return true;
  }

  shift = value->exponent - (k - ((int32_t) sbits - 1));
  round_scaled_integer(q, &inexact, n, shift);
  if (should_increment(negative, mode, inexact)) {
    mpz_add_ui(q, q, 1);
  }

  if (mpz_cmp_ui(q, ((uint64_t) 1) << sbits) >= 0) {
    mpz_fdiv_q_2exp(q, q, 1);
    k ++;
  }

  if (k > emax) {
    if ((!negative && mode == FP_RTP) || (negative && mode == FP_RTN)) {
      fp_value_make_inf(out, ebits, sbits, negative);
    } else {
      make_max_finite(out, ebits, sbits, negative);
    }
    mpz_clear(q);
    mpz_clear(n);
    return true;
  }

  out->ebits = ebits;
  out->sbits = sbits;
  out->kind = FP_VALUE_NUMERAL;
  out->sign = negative;
  out->exponent = (uint64_t) (k + bias);
  out->significand = mpz_get_ui(q) & low_mask(sbits - 1);

  mpz_clear(q);
  mpz_clear(n);
  return true;
}
