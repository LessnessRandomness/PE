// https://codereview.stackexchange.com/a/74792 by Alnitak

#include <stddef.h>
#include <stdint.h>

uint64_t highest;

// checks if `f` is a factor of `n`,
// returning divided `n` accordingly
uint64_t factorize(uint64_t n, uint64_t f) {
    if (n < f) return n;
    while (n % f == 0) {
        n /= f;
        if (f > highest) {
            highest = f;
        }
    }
    return n;
}

uint64_t find(uint64_t n) {
    highest = 1;

    // check the two simplest cases
    n = factorize(n, 2);
    n = factorize(n, 3);

    // and then all numbers in the form 6x - 1 and 6x + 1
    if (n >= 5) {
        for (uint64_t i = 5; i * i <= n; i += 6) {
            n = factorize(n, i);
            n = factorize(n, i + 2);
        }
    }
    return (n == 1) ? highest : n;
}

int main(void) {
    return find(600851475143);
}
