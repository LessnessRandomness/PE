#include <stdint.h>

// Sum of 1, 2, 3, ... n
uint64_t triangular(uint64_t n) {
  if (n % 2ull == 0) {
    return (n / 2ull) * (n + 1ull);
  } else {
    return ((n + 1ull) / 2ull) * n;
  }
}

// Sum of multiples of 3 or 5 less or equal to max
uint64_t solution(uint64_t n) {
  return 3ull * triangular(n / 3ull) - 15ull * triangular(n / 15ull) + 5ull * triangular(n / 5ull);
}

int main(void) {
  return solution(999ull);
}

