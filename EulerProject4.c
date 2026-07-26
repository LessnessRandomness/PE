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
    uint32_t max_value = 100000, t = 989010;
    for (uint16_t x = 990; max_value < t; x -= 11) {
        for (uint32_t n = t; max_value < n; n -= x) {
            if (is_palindrome(n)) {
                max_value = n;
            }
        }
        t -= 10989;
    }
    return max_value;
}

uint32_t main() {
    return find();
}

