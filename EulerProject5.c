#include <stdio.h>
#include <stdbool.h>
#include <stdint.h>

#define N 20

static uint32_t max_prime_power(int p, int bound) {
    uint32_t power = 1;
    while (power <= bound) {
        power *= p; 
    }
    return (power / p);
}

static void sieve_primes(bool is_prime[], int n) {
    for (int i = 2; i <= n; i++) {
        is_prime[i] = true;
    }
    for (int i = 2; i * i <= n; i++) {
        if (is_prime[i]) {
            for (int j = i * i; j <= n; j += i) {
                is_prime[j] = false;
            }
        }
    }
}

uint32_t result() {
    bool is_prime[N + 1];
    sieve_primes(is_prime, N);
  
    uint32_t result = 1;
    for (int i = 2; i <= N; i++) {
        if (is_prime[i]) {
            result *= max_prime_power(i, N);
        }
    }
    return result;
}

int main(void) {

    printf("The smallest positive number evenly divisible by all numbers from 1 to %d is: %lu\n", 
           N, result());
           
    return 0;
}

