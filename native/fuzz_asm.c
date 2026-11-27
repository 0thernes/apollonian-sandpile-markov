/* SPDX-License-Identifier: Apache-2.0
 * 100,000-iteration deterministic fuzz harness for Apollonian-Sandpile-Markov (ISO C11, v2.1.0).
 * Fuzzes ALL 7 algebraic laws: Gauss QR + supplementary laws, SL2(Z) Fricke trace identity,
 * Descartes involutions, Octahedral 8-face involutions, 3D Soddy 5-sphere involutions,
 * A_2 even-Laplacian witness uA2_lap4 == 4, and 5-step Markov cluster Laurent cancellations.
 */
#include <stdint.h>
#include <stdio.h>

static uint64_t splitmix64(uint64_t *state) {
    uint64_t z = (*state += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

static uint64_t u64_abs(int64_t x) {
    return (x < 0) ? (uint64_t)(-(x + 1)) + 1ULL : (uint64_t)x;
}

static uint64_t gcd64(int64_t a, int64_t b) {
    uint64_t ua = u64_abs(a), ub = u64_abs(b);
    while (ub != 0ULL) { uint64_t t = ua % ub; ua = ub; ub = t; }
    return ua;
}

static int jacobi64(int64_t a, int64_t n) {
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

static int64_t u_a2_lap4(int64_t x, int64_t y) {
    return (x * (x - 1)) / 2 + (y * (y - 1)) / 2;
}

int main(void) {
    uint64_t rng = 20261126ULL;
    for (int iter = 0; iter < 100000; ++iter) {
        /* 1. Fuzz Gauss Quadratic Reciprocity & both Supplementary Laws */
        int64_t m = (int64_t)((splitmix64(&rng) % 50000ULL) * 2ULL + 1ULL);
        int64_t n = (int64_t)((splitmix64(&rng) % 50000ULL) * 2ULL + 1ULL);
        if (gcd64(m, n) == 1ULL) {
            int expected = ((m & 3) == 3 && (n & 3) == 3) ? -1 : 1;
            if (jacobi64(m, n) * jacobi64(n, m) != expected) {
                fprintf(stderr, "QR FAIL m=%lld n=%lld\n", (long long)m, (long long)n);
                return 1;
            }
        }
        if (jacobi64(-1, n) != (((n & 3) == 1) ? 1 : -1)) return 10;
        if (jacobi64(2, n) != (((n & 7) == 1 || (n & 7) == 7) ? 1 : -1)) return 11;

        /* 2. Fuzz SL2(Z) Fricke trace identity */
        int64_t p = (int64_t)(splitmix64(&rng) % 19ULL) - 9;
        int64_t q = (int64_t)(splitmix64(&rng) % 19ULL) - 9;
        int64_t r = (int64_t)(splitmix64(&rng) % 19ULL) - 9;
        int64_t s = (int64_t)(splitmix64(&rng) % 19ULL) - 9;
        int64_t a11 = 1 + p*q, a12 = p, a21 = q, a22 = 1;
        int64_t b11 = 1 + r*s, b12 = r, b21 = s, b22 = 1;
        int64_t ab11 = a11*b11 + a12*b21, ab12 = a11*b12 + a12*b22;
        int64_t ab21 = a21*b11 + a22*b21, ab22 = a21*b12 + a22*b22;
        int64_t c11 = ab11*a22 - ab12*a21, c12 = -ab11*a12 + ab12*a11;
        int64_t c21 = ab21*a22 - ab22*a21, c22 = -ab21*a12 + ab22*a11;
        int64_t tr_comm = (c11*b22 - c12*b21) + (-c21*b12 + c22*b11);
        int64_t trA = a11 + a22, trB = b11 + b22, trAB = ab11 + ab22;
        if (trA*trA + trB*trB + trAB*trAB != trA*trB*trAB + tr_comm + 2) return 2;

        /* 3. Fuzz Descartes involution & Lorentz form */
        int64_t d0 = (int64_t)(splitmix64(&rng) % 200ULL) - 100;
        int64_t d1 = (int64_t)(splitmix64(&rng) % 200ULL) - 100;
        int64_t d2 = (int64_t)(splitmix64(&rng) % 200ULL) - 100;
        int64_t d3 = (int64_t)(splitmix64(&rng) % 200ULL) - 100;
        int64_t q0 = (d0+d1+d2+d3)*(d0+d1+d2+d3) - 2*(d0*d0+d1*d1+d2*d2+d3*d3);
        int64_t d0p = 2*(d1+d2+d3) - d0;
        int64_t q1 = (d0p+d1+d2+d3)*(d0p+d1+d2+d3) - 2*(d0p*d0p+d1*d1+d2*d2+d3*d3);
        if (q0 != q1 || 2*(d1+d2+d3) - d0p != d0) return 3;

        /* 4. Fuzz Octahedral 8-face reflection involutions & Lorentz form invariance */
        int64_t S = (int64_t)(splitmix64(&rng) % 60ULL) - 30;
        int64_t ox[6];
        ox[0] = (int64_t)(splitmix64(&rng) % 60ULL) - 30; ox[3] = S - ox[0];
        ox[1] = (int64_t)(splitmix64(&rng) % 60ULL) - 30; ox[4] = S - ox[1];
        ox[2] = (int64_t)(splitmix64(&rng) % 60ULL) - 30; ox[5] = S - ox[2];
        int mask = (int)(splitmix64(&rng) & 7ULL);
        int s1 = (mask & 1) != 0, s2 = (mask & 2) != 0, s3 = (mask & 4) != 0;
        int64_t f1 = s1 ? ox[3] : ox[0], f2 = s2 ? ox[4] : ox[1], f3 = s3 ? ox[5] : ox[2];
        int64_t delta = 4*(f1 + f2 + f3) - 2*S;
        int64_t oy[6] = {
            s1 ? ox[0] + delta : ox[0], s2 ? ox[1] + delta : ox[1], s3 ? ox[2] + delta : ox[2],
            s1 ? ox[3] : ox[3] + delta, s2 ? ox[4] : ox[4] + delta, s3 ? ox[5] : ox[5] + delta
        };
        int64_t Sy = oy[0] + oy[3];
        int64_t oq0 = (ox[0]-ox[3])*(ox[0]-ox[3]) + (ox[1]-ox[4])*(ox[1]-ox[4]) + (ox[2]-ox[5])*(ox[2]-ox[5]) - 2*S*S;
        int64_t oq1 = (oy[0]-oy[3])*(oy[0]-oy[3]) + (oy[1]-oy[4])*(oy[1]-oy[4]) + (oy[2]-oy[5])*(oy[2]-oy[5]) - 2*Sy*Sy;
        if (oy[1] + oy[4] != Sy || oy[2] + oy[5] != Sy || oq0 != oq1) return 4;
        int64_t g1 = s1 ? oy[3] : oy[0], g2 = s2 ? oy[4] : oy[1], g3 = s3 ? oy[5] : oy[2];
        int64_t d2o = 4*(g1 + g2 + g3) - 2*Sy;
        if ((s1 ? oy[0] + d2o : oy[0]) != ox[0] || (s1 ? oy[3] : oy[3] + d2o) != ox[3]) return 5;

        /* 5. Fuzz 3D Soddy 5-sphere reflection involution & Q3 invariance */
        int64_t b0 = (int64_t)(splitmix64(&rng) % 80ULL) - 40;
        int64_t b1 = (int64_t)(splitmix64(&rng) % 80ULL) - 40;
        int64_t b2 = (int64_t)(splitmix64(&rng) % 80ULL) - 40;
        int64_t b3 = (int64_t)(splitmix64(&rng) % 80ULL) - 40;
        int64_t b4 = (int64_t)(splitmix64(&rng) % 80ULL) - 40;
        int64_t ss0 = b0+b1+b2+b3+b4;
        int64_t sq0 = ss0*ss0 - 3*(b0*b0+b1*b1+b2*b2+b3*b3+b4*b4);
        int64_t b0p = (b1+b2+b3+b4) - b0;
        int64_t ss1 = b0p+b1+b2+b3+b4;
        int64_t sq1 = ss1*ss1 - 3*(b0p*b0p+b1*b1+b2*b2+b3*b3+b4*b4);
        if (sq0 != sq1 || (b1+b2+b3+b4) - b0p != b0) return 6;

        /* 6. Fuzz A_2 triangular discrete Laplacian even witness uA2_lap4 == 4 */
        int64_t ax = (int64_t)(splitmix64(&rng) % 2000ULL) - 1000;
        int64_t ay = (int64_t)(splitmix64(&rng) % 2000ULL) - 1000;
        int64_t lap_a2 = u_a2_lap4(ax+1, ay) + u_a2_lap4(ax-1, ay) + u_a2_lap4(ax, ay+1)
                       + u_a2_lap4(ax, ay-1) + u_a2_lap4(ax+1, ay-1) + u_a2_lap4(ax-1, ay+1)
                       - 6 * u_a2_lap4(ax, ay);
        if (lap_a2 != 4) return 7;

        /* 7. Fuzz 5-step Markov cluster Laurent identities (bounded to avoid int64 overflow) */
        int64_t x1 = (int64_t)(splitmix64(&rng) % 2ULL) + 1;
        int64_t x2 = (int64_t)(splitmix64(&rng) % 2ULL) + 1;
        int64_t x3 = (int64_t)(splitmix64(&rng) % 2ULL) + 1;
        int64_t p1 = x2*x2 + x3*x3;
        int64_t v = x1*x1*x3*x3;
        int64_t w = x1*x1*x2*x2;
        int64_t p2 = p1*p1 + v;
        int64_t p3 = w*p1*p1 + p2*p2;
        int64_t r4 = p1*p1*p1 + 2*x1*x1*p1*p1 + x1*x1*v;
        int64_t p4 = w*w*p1*p1*p1 + p2*p2*r4;
        int64_t p5 = w*w*w*w*p1*p1*p1*p1 + p2*(2*w*w*w*v*p1*p1 + w*w*v*p2*p2 + 2*w*w*p1*p1*p1*r4 + p2*p2*r4*r4);
        int64_t x1_2 = x1*x1, x1_4 = x1_2*x1_2, x1_6 = x1_4*x1_2;
        int64_t x2_2 = x2*x2, x2_4 = x2_2*x2_2, x3_2 = x3*x3;
        if (p1*p4 != x1_4*x2_2*x3_2*p2*p2 + p3*p3) return 8;
        if (p2*p5 != x1_6*x2_4*x3_2*p3*p3 + p4*p4) return 9;
    }
    printf("{\"fuzz_status\":\"PASS\",\"version\":\"2.1.0\",\"laws_checked\":7,\"iterations\":100000}\n");
    return 0;
}
