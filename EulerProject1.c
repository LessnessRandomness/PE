#include <stddef.h>

// Sum of d, d*2, d*3, ... d*n
unsigned int aux(unsigned int n) {
  return n*(n+1)/2;
}

// Sum of multiples of 3 or 5 less or equal to max
unsigned int solution(unsigned int max) {
  return 3 * aux(max/3) + 5 * aux(max/5) - 15 * aux(max/15);
}

int main(void) {
  unsigned int result;
  result = solution(999);
  return result;
}

