#include <stddef.h>

// Sum of 1, 2, 3, ... n
unsigned int triangular(unsigned int n) {
  if (n % 2 == 0) {
    return (n / 2) * (n + 1);
  } else {
    return ((n + 1) / 2) * n;
  }
}

// Sum of multiples of 3 or 5 less or equal to max
unsigned int solution(unsigned int n) {
  return 3 * triangular(n / 3) - 15 * triangular(n / 15) + 5 * triangular(n / 5);
}

int main(void) {
  return solution(999);
}

