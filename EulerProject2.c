#include <stddef.h>

unsigned int result(unsigned int max) {
    unsigned int a, b, t, sum;
    sum = 0;
    a = 0;
    b = 2;
    while (b <= max) {
        sum += b;
        t = a;
        a = b;
        b = 4 * a + t;
    }
    return sum;
}

int main(void) {
    return result(1000000);
}

