#pragma once

template<typename T> 
inline T single_bit_mask(const unsigned &i) {
  return T(1) << i;
}

template<typename T> 
inline T zero() {
  return 0;
}

template<typename T> 
inline T ones() {
  return ~0;
}

template<typename T>
void print_bitmask(T m) {
  for (size_t j = 0; j < sizeof(T)*8; ++j) {
    auto mask = single_bit_mask<T>(j);
    assert(mask);
    if (m & mask)
      printf("1");
    else
      printf("0");
  }
  printf("\n");
}