/* SPDX-License-Identifier: Apache-2.0
 * Coverage-guided libFuzzer target for Apollonian-Sandpile-Markov (ISO C11, v2.0.0).
 * Build & run with:
 *   clang -std=c11 -O2 -Wall -Wextra -Werror -fsanitize=fuzzer,address,undefined \
 *     native/fuzz_libfuzzer.c -o native/fuzz_libfuzzer && ./native/fuzz_libfuzzer -max_total_time=5
 */
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

static uint64_t u64_abs_f(int64_t x) {
    return (x < 0) ? (uint64_t)(-(x + 1)) + 1ULL : (uint64_t)x;
}

static uint64_t gcd64_f(int64_t a, int64_t b) {
    uint64_t ua = u64_abs_f(a), ub = u64_abs_f(b);
    while (ub != 0ULL) { uint64_t t = ua % ub; ua = ub; ub = t; }
    return ua;
}

static int jacobi64_f(int64_t a, int64_t n) {
    if (n <= 0 || (n & 1) == 0) return 0;
    a %= n;
    if (a < 0) a += n;
    int res = 1;
    while (a != 0) {
        while ((a & 1) == 0) {
            a >>= 1;
            int64_t n8 = n & 7;
            if (n8 == 3 || n8 == 5) res = -res;
        }
        int64_t t = a; a = n; n = t;
        if ((a & 3) == 3 && (n & 3) == 3) res = -res;
        a %= n;
    }
    return (n == 1) ? res : 0;
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    if (size < 8) return 0;

    /* 1. Gauss QR & supplementary laws */
    int64_t m = ((int64_t)data[0] * 256 + (int64_t)data[1]) * 2 + 1;
    int64_t n = ((int64_t)data[2] * 256 + (int64_t)data[3]) * 2 + 1;
    if (gcd64_f(m, n) == 1ULL) {
        int expected = ((m & 3) == 3 && (n & 3) == 3) ? -1 : 1;
        if (jacobi64_f(m, n) * jacobi64_f(n, m) != expected) abort();
    }
    if (jacobi64_f(-1, n) != (((n & 3) == 1) ? 1 : -1)) abort();
    if (jacobi64_f(2, n) != (((n & 7) == 1 || (n & 7) == 7) ? 1 : -1)) abort();

    /* 2. Descartes involution & Lorentz invariance */
    int64_t d0 = (int64_t)(int8_t)data[4];
    int64_t d1 = (int64_t)(int8_t)data[5];
    int64_t d2 = (int64_t)(int8_t)data[6];
    int64_t d3 = (int64_t)(int8_t)data[7];
    int64_t q0 = (d0+d1+d2+d3)*(d0+d1+d2+d3) - 2*(d0*d0+d1*d1+d2*d2+d3*d3);
    int64_t d0p = 2*(d1+d2+d3) - d0;
    int64_t q1 = (d0p+d1+d2+d3)*(d0p+d1+d2+d3) - 2*(d0p*d0p+d1*d1+d2*d2+d3*d3);
    if (q0 != q1 || 2*(d1+d2+d3) - d0p != d0) abort();

    /* 3. SL2(Z) Fricke trace identity */
    int64_t p = (int64_t)(data[0] % 15) - 7;
    int64_t q = (int64_t)(data[1] % 15) - 7;
    int64_t r = (int64_t)(data[2] % 15) - 7;
    int64_t s = (int64_t)(data[3] % 15) - 7;
    int64_t a11 = 1 + p*q, a12 = p, a21 = q, a22 = 1;
    int64_t b11 = 1 + r*s, b12 = r, b21 = s, b22 = 1;
    int64_t ab11 = a11*b11 + a12*b21, ab12 = a11*b12 + a12*b22;
    int64_t ab21 = a21*b11 + a22*b21, ab22 = a21*b12 + a22*b22;
    int64_t c11 = ab11*a22 - ab12*a21, c12 = -ab11*a12 + ab12*a11;
    int64_t c21 = ab21*a22 - ab22*a21, c22 = -ab21*a12 + ab22*a11;
    int64_t tr_comm = (c11*b22 - c12*b21) + (-c21*b12 + c22*b11);
    int64_t trA = a11 + a22, trB = b11 + b22, trAB = ab11 + ab22;
    if (trA*trA + trB*trB + trAB*trAB != trA*trB*trAB + tr_comm + 2) abort();

    return 0;
}
