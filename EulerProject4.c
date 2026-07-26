#include <stdbool.h>
#include <stdint.h>

bool is_palindrome(uint32_t n) {
    if (n / 100000 != n % 10) {
        return false;
    }
    if (n / 10000 % 10 != n / 10 % 10) {
        return false;
    }
    if (n / 1000 % 10 != n / 100 % 10) {
        return false;
    }
    return true;
}

uint32_t find() {
    uint32_t max_value = 100000;
    for (uint16_t x = 990; max_value < x * 999; x -= 11) {
        for (uint32_t n = x * 999; max_value < n; n -= x) {
            if (is_palindrome(n)) {
                max_value = n;
            }
        }
    }
    return max_value;
}

uint32_t main() {
    return find();
}

