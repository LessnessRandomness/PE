#include <stddef.h>

int main(void) {
  unsigned a, b, t, result;
  result = 0;
  a = 0;
  b = 2;
  while (b <= 1000000) {
    result += b;
    t = a;
    a = b;
    b = 4 * a + t;
  }
  return result;
}

