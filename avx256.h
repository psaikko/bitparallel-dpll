#include <immintrin.h>
#include <cinttypes>
#include "bitvector_helpers.h"

struct avx256i;

const uint64_t ones_64[4] = { 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF };
const uint64_t zeros_64[4] = { 0, 0, 0, 0 };

__m256i avx256_ones = _mm256_loadu_si256((__m256i *) ones_64);
__m256i avx256_zero = _mm256_loadu_si256((__m256i *) zeros_64);

inline avx256i zero();

struct avx256i {
  __m256i val;

  avx256i() : val(avx256_zero) {}

  avx256i(__m256i val) : val(val) {}

  inline avx256i operator& (const avx256i &other) {
    return _mm256_and_si256(val, other.val);
  };

  inline avx256i operator| (const avx256i &other) {
    return _mm256_or_si256(val, other.val);
  };

  inline avx256i operator^ (const avx256i &other) {
    return _mm256_xor_si256(val, other.val);
  };

  inline avx256i operator~ () {
    return _mm256_andnot_si256(val, avx256_ones);
  };

  inline avx256i operator&= (const avx256i &other) {
    val = _mm256_and_si256(val, other.val);
    return *this;
  };

  inline avx256i operator|= (const avx256i &other) {
    val = _mm256_or_si256(val, other.val);
    return *this;
  };

  inline avx256i operator^= (const avx256i &other) {
    val = _mm256_xor_si256(val, other.val);
    return *this;
  };

  inline bool operator==(const avx256i &other) {
    avx256i res = (*this) ^ other;
    return _mm256_testz_si256(res.val, avx256_ones);
  }

  inline bool operator!=(const avx256i &other) {
    avx256i res = (*this) ^ other;
    return !_mm256_testz_si256(res.val, avx256_ones);
  }

  inline avx256i operator<< (const unsigned &i) {
    __uint128_t tmp[2];
    _mm256_storeu_si256((__m256i *)tmp, val);

    if (i >= 128) {
      tmp[0] = 0;
      tmp[0] |= (tmp[1] << (i - 128));
      tmp[1] = 0;
    } else {
      tmp[0] <<= i;
      tmp[0] |= (tmp[1] >> (128 - i));
      tmp[1] <<= i;
    }

    return _mm256_loadu_si256((__m256i *) tmp);
  }

  explicit operator bool() const {
    return !_mm256_testz_si256(val, avx256_ones);
  }

  inline avx256i& operator= (avx256i other) {
    val = other.val;
    return *this;
  }

};

template<>
inline avx256i zero<avx256i>() {
  return avx256_zero;
}

template<>
inline avx256i ones<avx256i>() {
  return avx256_ones;
}

template<>
inline avx256i single_bit_mask<avx256i>(const unsigned &index) {

  uint64_t mask[4];

  for (unsigned i = 0; i < 4; ++i) 
    mask[i] = 0;

  unsigned i = index / 64;
  unsigned j = index % 64;

  mask[i] = (uint64_t(1) << j);

  __m256i avx256_mask = _mm256_loadu_si256((__m256i *) mask);  

  return avx256_mask;
}

template<>
unsigned popcount(avx256i v) {
  uint64_t tmp[4];
  _mm256_storeu_si256((__m256i *)tmp, v.val);
  return __builtin_popcountll(tmp[0]) + \
         __builtin_popcountll(tmp[1]) + \
         __builtin_popcountll(tmp[2]) + \
         __builtin_popcountll(tmp[3]);
}

template<>
avx256i* assign_alloc<avx256i>(size_t count) {
  return (avx256i*) aligned_alloc(32, count * sizeof(avx256i));
}

/*
template<>
void print_bitmask<avx256i>(avx256i m) {

  printf("print avx bitmask\n");

  __uint128_t tmp[2];
  _mm256_storeu_si256((__m256i *)tmp, m.val);

  for (int j = 0; j < 128; ++j) {
    if (tmp[0] & (__uint128_t(1) << j))
      printf("1");
    else
      printf("0");
  }

  for (int j = 0; j < 128; ++j) {
    if (tmp[1] & (__uint128_t(1) << j))
      printf("1");
    else
      printf("0");
  }

  printf("\n");
}*/