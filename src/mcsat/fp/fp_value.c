/*
 * Native floating-point value helpers for MCSAT.
 */

#include "mcsat/fp/fp_value.h"

#include <assert.h>

static uint64_t fp_exponent_mask(uint32_t ebits) {
  assert(ebits < 64);
  return ((uint64_t) 1 << ebits) - 1u;
}

static uint64_t fp_significand_mask(uint32_t sbits) {
  assert(sbits > 0 && sbits <= 64);
  return sbits == 64 ? UINT64_MAX : (((uint64_t) 1 << (sbits - 1)) - 1u);
}

bool fp_value_is_nan(const fp_const_t *v) {
  return v->kind == FP_VALUE_NAN;
}

bool fp_value_is_infinite(const fp_const_t *v) {
  return v->kind == FP_VALUE_POS_INF || v->kind == FP_VALUE_NEG_INF;
}

bool fp_value_is_zero(const fp_const_t *v) {
  if (v->kind == FP_VALUE_POS_ZERO || v->kind == FP_VALUE_NEG_ZERO) {
    return true;
  }
  return v->kind == FP_VALUE_NUMERAL && v->exponent == 0 && v->significand == 0;
}

bool fp_value_is_finite(const fp_const_t *v) {
  return !fp_value_is_nan(v) && !fp_value_is_infinite(v);
}

bool fp_value_is_subnormal(const fp_const_t *v) {
  return v->kind == FP_VALUE_NUMERAL && v->exponent == 0 && v->significand != 0;
}

bool fp_value_is_normal(const fp_const_t *v) {
  uint64_t emax;

  emax = fp_exponent_mask(v->ebits);
  return v->kind == FP_VALUE_NUMERAL && v->exponent != 0 && v->exponent != emax;
}

bool fp_value_to_dyadic(const fp_const_t *v, fp_dyadic_t *d) {
  mpz_t z;
  int32_t bias;
  int32_t exponent;

  if (!fp_value_is_finite(v)) {
    return false;
  }

  if (fp_value_is_zero(v)) {
    fp_dyadic_set_int64(d, 0);
    return true;
  }

  bias = ((int32_t) 1 << (v->ebits - 1)) - 1;
  mpz_init(z);
  if (v->exponent == 0) {
    mpz_set_ui(z, v->significand);
    exponent = 1 - bias - ((int32_t) v->sbits - 1);
  } else {
    mpz_set_ui(z, v->significand | (((uint64_t) 1) << (v->sbits - 1)));
    exponent = (int32_t) v->exponent - bias - ((int32_t) v->sbits - 1);
  }
  if (v->sign) {
    mpz_neg(z, z);
  }
  fp_dyadic_set_mpz_exp(d, z, exponent);
  mpz_clear(z);

  return true;
}

int fp_value_cmp(const fp_const_t *a, const fp_const_t *b) {
  fp_dyadic_t da;
  fp_dyadic_t db;
  int result;

  if (fp_value_is_nan(a) || fp_value_is_nan(b)) {
    return 0;
  }
  if (fp_value_is_zero(a) && fp_value_is_zero(b)) {
    return 0;
  }
  if (fp_value_is_infinite(a) || fp_value_is_infinite(b)) {
    if (fp_value_is_infinite(a) && fp_value_is_infinite(b)) {
      return a->sign == b->sign ? 0 : (a->sign ? -1 : 1);
    }
    return fp_value_is_infinite(a) ? (a->sign ? -1 : 1) : (b->sign ? 1 : -1);
  }

  fp_dyadic_init(&da);
  fp_dyadic_init(&db);
  (void) fp_value_to_dyadic(a, &da);
  (void) fp_value_to_dyadic(b, &db);
  result = fp_dyadic_cmp(&da, &db);
  fp_dyadic_destruct(&da);
  fp_dyadic_destruct(&db);

  return result;
}

void fp_value_make_nan(fp_const_t *v, uint32_t ebits, uint32_t sbits) {
  v->ebits = ebits;
  v->sbits = sbits;
  v->kind = FP_VALUE_NAN;
  v->sign = false;
  v->exponent = fp_exponent_mask(ebits);
  v->significand = 1;
}

void fp_value_make_inf(fp_const_t *v, uint32_t ebits, uint32_t sbits, bool sign) {
  v->ebits = ebits;
  v->sbits = sbits;
  v->kind = sign ? FP_VALUE_NEG_INF : FP_VALUE_POS_INF;
  v->sign = sign;
  v->exponent = fp_exponent_mask(ebits);
  v->significand = 0;
}

void fp_value_make_zero(fp_const_t *v, uint32_t ebits, uint32_t sbits, bool sign) {
  v->ebits = ebits;
  v->sbits = sbits;
  v->kind = sign ? FP_VALUE_NEG_ZERO : FP_VALUE_POS_ZERO;
  v->sign = sign;
  v->exponent = 0;
  v->significand = 0;
}
