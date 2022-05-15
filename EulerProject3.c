// https://codereview.stackexchange.com/a/74792 by Alnitak

#include <stddef.h>
#include <stdint.h>

int64_t highest;

// checks if `f` is a factor of `n`,
// returning divided `n` accordingly
int64_t factorize(int64_t n, int64_t f) {
    if (n < f) return n;
    while (n % f == 0) {
        n /= f;
        if (f > highest) {
            highest = f;
        }
    }
    return n;
}

int64_t find(int64_t n) {
    highest = 1;

    // check the two simplest cases
    n = factorize(n, 2);
    n = factorize(n, 3);

    // and then all numbers in the form 6x - 1 and 6x + 1
    if (n >= 5) {
        for (int64_t i = 5; i * i <= n; i += 6) {
            n = factorize(n, i);
            n = factorize(n, i + 2);
        }
    }
    return (n == 1) ? highest : n;
}

int main(void) {
    return find(600851475143);
}
