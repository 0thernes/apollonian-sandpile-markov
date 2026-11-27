/* SPDX-License-Identifier: Apache-2.0
 * Independent ISO C11 verifier for Apollonian-Sandpile-Markov (v2.0.0).
 * Compiles cleanly with: gcc -std=c11 -O2 -Wall -Wextra -Werror -fsanitize=address,undefined
 */
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static uint64_t u64_abs(int64_t x) {
    return (x < 0) ? (uint64_t)(-(x + 1)) + 1ULL : (uint64_t)x;
}

static uint64_t gcd64(int64_t a, int64_t b) {
    uint64_t ua = u64_abs(a);
    uint64_t ub = u64_abs(b);
    while (ub != 0ULL) {
        uint64_t t = ua % ub;
        ua = ub;
        ub = t;
    }
    return ua;
}

static int jacobi64(int64_t a, int64_t n) {
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
        int64_t tmp = a; a = n; n = tmp;
        if ((a & 3) == 3 && (n & 3) == 3) res = -res;
        a %= n;
    }
    return (n == 1) ? res : 0;
}

static int is_square64(int64_t x) {
    if (x < 0) return 0;
    int64_t lo = 0, hi = 3037000499LL;
    while (lo <= hi) {
        int64_t mid = lo + (hi - lo) / 2;
        int64_t sq = mid * mid;
        if (sq == x) return 1;
        if (sq < x) lo = mid + 1;
        else hi = mid - 1;
    }
    return 0;
}

static int64_t signed_odd_part64(int64_t a) {
    if (a == 0) return 0;
    while ((a & 1) == 0) a /= 2;
    return a;
}

static int is_octahedral6(const int64_t x[6]) {
    int64_t s = x[0] + x[3];
    if (x[1] + x[4] != s || x[2] + x[5] != s) return 0;
    int64_t d0 = x[0] - x[3], d1 = x[1] - x[4], d2 = x[2] - x[5];
    return d0 * d0 + d1 * d1 + d2 * d2 == 2 * s * s;
}

static int64_t rem_euclid64(int64_t x, int64_t m) {
    int64_t r = x % m;
    return (r < 0) ? (r + m) : r;
}

static int check_apollonian_and_octahedral(void) {
    int64_t roots[3][4] = {{-3, 5, 8, 8}, {-7, 17, 12, 20}, {-11, 21, 24, 28}};
    for (int r = 0; r < 3; ++r) {
        int64_t q[4] = {roots[r][0], roots[r][1], roots[r][2], roots[r][3]};
        int64_t s = q[0] + q[1] + q[2] + q[3];
        int64_t s2 = q[0]*q[0] + q[1]*q[1] + q[2]*q[2] + q[3]*q[3];
        if (s * s != 2 * s2) return 1;
        uint64_t rng = 0x9e3779b97f4a7c15ULL ^ (uint64_t)(r + 1);
        for (int step = 0; step < 250; ++step) {
            for (int i = 0; i < 4; ++i) {
                if (is_square64(q[i])) return 2;
            }
            rng ^= rng >> 12; rng ^= rng << 25; rng ^= rng >> 27;
            int idx = (int)((rng * 2685821657736338717ULL) & 3ULL);
            int64_t nxt = 2 * (q[0] + q[1] + q[2] + q[3] - q[idx]) - q[idx];
            if (u64_abs(nxt) < 100000000ULL) {
                q[idx] = nxt;
                int64_t ns = q[0] + q[1] + q[2] + q[3];
                int64_t ns2 = q[0]*q[0] + q[1]*q[1] + q[2]*q[2] + q[3]*q[3];
                if (ns * ns != 2 * ns2) return 3;
            }
        }
    }
    /* Octahedral root (-6, 10, 17, 40, 24, 17): Jacobi witnesses + BFS orbit mod-8 & 2^e*m^2 audit */
    if (jacobi64(-3, 11) != -1 || jacobi64(5, 27) != -1 || jacobi64(17, 11) != -1 ||
        jacobi64(5, 57) != -1 || jacobi64(3, 41) != -1) {
        return 4;
    }
    int64_t oq[512][6];
    int head = 0, tail = 0;
    int64_t oct_root[6] = {-6, 10, 17, 40, 24, 17};
    for (int i = 0; i < 6; ++i) oq[tail][i] = oct_root[i];
    tail++;
    while (head < tail) {
        int64_t cur[6];
        for (int i = 0; i < 6; ++i) cur[i] = oq[head][i];
        head++;
        if (!is_octahedral6(cur)) return 5;
        if (rem_euclid64(cur[0], 8) != 2 || rem_euclid64(cur[1], 8) != 2 ||
            rem_euclid64(cur[2], 8) != 1 || rem_euclid64(cur[3], 8) != 0 ||
            rem_euclid64(cur[4], 8) != 0 || rem_euclid64(cur[5], 8) != 1) {
            return 6;
        }
        for (int i = 0; i < 6; ++i) {
            if (cur[i] >= 0 && is_square64(signed_odd_part64(cur[i]))) return 7;
        }
        int64_t s = cur[0] + cur[3];
        for (int mask = 0; mask < 8; ++mask) {
            int s1 = (mask & 1) != 0, s2 = (mask & 2) != 0, s3 = (mask & 4) != 0;
            int64_t f1 = s1 ? cur[3] : cur[0];
            int64_t f2 = s2 ? cur[4] : cur[1];
            int64_t f3 = s3 ? cur[5] : cur[2];
            int64_t delta = 4 * (f1 + f2 + f3) - 2 * s;
            int64_t nxt[6] = {
                s1 ? cur[0] + delta : cur[0],
                s2 ? cur[1] + delta : cur[1],
                s3 ? cur[2] + delta : cur[2],
                s1 ? cur[3] : cur[3] + delta,
                s2 ? cur[4] : cur[4] + delta,
                s3 ? cur[5] : cur[5] + delta
            };
            int64_t mx = nxt[0];
            for (int i = 1; i < 6; ++i) if (nxt[i] > mx) mx = nxt[i];
            if (mx <= 500 && tail < 512) {
                int dup = 0;
                for (int j = 0; j < tail; ++j) {
                    int same = 1;
                    for (int i = 0; i < 6; ++i) if (oq[j][i] != nxt[i]) { same = 0; break; }
                    if (same) { dup = 1; break; }
                }
                if (!dup) {
                    for (int i = 0; i < 6; ++i) oq[tail][i] = nxt[i];
                    tail++;
                }
            }
        }
    }
    return 0;
}

static int64_t exact_det_bareiss(int n, const int64_t mat[9][9]) {
    int64_t a[9][9];
    for (int i = 0; i < n; ++i)
        for (int j = 0; j < n; ++j)
            a[i][j] = mat[i][j];
    int64_t sign = 1, prev = 1;
    for (int k = 0; k < n; ++k) {
        if (a[k][k] == 0) {
            int swap_r = -1;
            for (int r = k + 1; r < n; ++r) {
                if (a[r][k] != 0) { swap_r = r; break; }
            }
            if (swap_r < 0) return 0;
            for (int c = 0; c < n; ++c) {
                int64_t tmp = a[k][c]; a[k][c] = a[swap_r][c]; a[swap_r][c] = tmp;
            }
            sign = -sign;
        }
        int64_t piv = a[k][k];
        for (int i = k + 1; i < n; ++i) {
            for (int j = k + 1; j < n; ++j) {
                a[i][j] = (a[i][j] * piv - a[i][k] * a[k][j]) / prev;
            }
        }
        prev = piv;
    }
    return sign * a[n - 1][n - 1];
}

static int64_t grid_lap_det(int k, int is_a2) {
    int n = k * k;
    int64_t mat[9][9];
    for (int i = 0; i < 9; ++i)
        for (int j = 0; j < 9; ++j)
            mat[i][j] = 0;
    for (int r = 0; r < k; ++r) {
        for (int c = 0; c < k; ++c) {
            int u = r * k + c;
            mat[u][u] = is_a2 ? 6 : 4;
            if (r > 0) mat[u][(r - 1) * k + c] = -1;
            if (r + 1 < k) mat[u][(r + 1) * k + c] = -1;
            if (c > 0) mat[u][r * k + (c - 1)] = -1;
            if (c + 1 < k) mat[u][r * k + (c + 1)] = -1;
            if (is_a2) {
                if (r > 0 && c + 1 < k) mat[u][(r - 1) * k + (c + 1)] = -1;
                if (r + 1 < k && c > 0) mat[u][(r + 1) * k + (c - 1)] = -1;
            }
        }
    }
    return exact_det_bareiss(n, mat);
}

static void stabilize_3x3(int s[9], int mode) {
    int deg = (mode == 0) ? 4 : 6;
    for (int iter = 0; iter < 5000; ++iter) {
        int moved = 0;
        for (int i = 0; i < 9; ++i) {
            if (s[i] >= deg) {
                s[i] -= deg;
                int r = i / 3, c = i % 3;
                if (r > 0) s[(r - 1) * 3 + c]++;
                if (r < 2) s[(r + 1) * 3 + c]++;
                if (c > 0) s[r * 3 + (c - 1)]++;
                if (c < 2) s[r * 3 + (c + 1)]++;
                if (mode == 1) {
                    if (r > 0 && c < 2) s[(r - 1) * 3 + (c + 1)]++;
                    if (r < 2 && c > 0) s[(r + 1) * 3 + (c - 1)]++;
                }
                moved = 1;
            }
        }
        if (!moved) break;
    }
}

static int check_sandpile_dhar_and_dets(void) {
    if (grid_lap_det(2, 0) != 192LL) return 8;
    if (grid_lap_det(3, 0) != 100352LL) return 9;
    if (grid_lap_det(2, 1) != 1092LL) return 12;
    if (grid_lap_det(3, 1) != 5393920LL) return 13;

    int expected_z2[9] = {2, 1, 2, 1, 0, 1, 2, 1, 2};
    int expected_a2[9] = {4, 2, 3, 2, 0, 2, 3, 2, 4};

    for (int mode = 0; mode < 2; ++mode) {
        int deg = (mode == 0) ? 4 : 6;
        int mu = deg - 1;
        int s[9], e[9], ee[9];
        for (int i = 0; i < 9; ++i) s[i] = 2 * mu;
        stabilize_3x3(s, mode);
        for (int i = 0; i < 9; ++i) e[i] = 2 * mu - s[i];
        stabilize_3x3(e, mode);
        const int *exp = (mode == 0) ? expected_z2 : expected_a2;
        for (int i = 0; i < 9; ++i) {
            if (e[i] != exp[i]) return (mode == 0) ? 10 : 14;
        }
        for (int i = 0; i < 9; ++i) ee[i] = e[i] + e[i];
        stabilize_3x3(ee, mode);
        for (int i = 0; i < 9; ++i) if (ee[i] != e[i]) return 11;
    }
    return 0;
}

static int check_markov_cluster_and_hurwitz(void) {
    int64_t queue[2048][3];
    int head = 0, tail = 0;
    queue[tail][0] = 1; queue[tail][1] = 1; queue[tail][2] = 1; tail++;
    int seen_mod64_2 = 0, seen_mod64_34 = 0;
    while (head < tail) {
        int64_t x = queue[head][0], y = queue[head][1], z = queue[head][2];
        head++;
        if (x*x + y*y + z*z != 3*x*y*z) return 20;
        if (gcd64(x, y) != 1ULL || gcd64(y, z) != 1ULL || gcd64(z, x) != 1ULL) return 21;
        int64_t arr[3] = {x, y, z};
        for (int i = 0; i < 3; ++i) {
            if ((arr[i] & 1) == 0) {
                if ((arr[i] & 31) != 2) return 22;
                if ((arr[i] & 63) == 2) seen_mod64_2 = 1;
                if ((arr[i] & 63) == 34) seen_mod64_34 = 1;
            } else {
                if ((arr[i] & 3) != 1) return 23;
            }
        }
        int64_t cand[2][3] = {
            {y, z, 3*y*z - x},
            {x, z, 3*x*z - y}
        };
        int ncand = (x == 1 && y == 1 && z == 1) ? 1 : ((x == 1 && y == 1 && z == 2) ? 1 : 2);
        if (x == 1 && y == 1 && z == 2) {
            cand[0][0] = 1; cand[0][1] = 2; cand[0][2] = 5;
        }
        for (int c = 0; c < ncand; ++c) {
            if (cand[c][2] <= 100000 && tail < 2048) {
                queue[tail][0] = cand[c][0];
                queue[tail][1] = cand[c][1];
                queue[tail][2] = cand[c][2];
                tail++;
            }
        }
    }
    if (!seen_mod64_2 || !seen_mod64_34) return 24;

    /* 5-step symbolic cluster Laurent positivity & exact divisions P1*P4, P2*P5 */
    for (int64_t x1 = 1; x1 <= 2; ++x1)
    for (int64_t x2 = 1; x2 <= 2; ++x2)
    for (int64_t x3 = 1; x3 <= 2; ++x3) {
        int64_t p1 = x2 * x2 + x3 * x3;
        int64_t v = x1 * x1 * x3 * x3;
        int64_t w = x1 * x1 * x2 * x2;
        int64_t p2 = p1 * p1 + v;
        int64_t p3 = w * p1 * p1 + p2 * p2;
        int64_t r4 = p1 * p1 * p1 + 2 * x1 * x1 * p1 * p1 + x1 * x1 * v;
        int64_t p4 = w * w * p1 * p1 * p1 + p2 * p2 * r4;
        int64_t p5 = w * w * w * w * p1 * p1 * p1 * p1
            + p2 * (2 * w * w * w * v * p1 * p1 + w * w * v * p2 * p2
                    + 2 * w * w * p1 * p1 * p1 * r4 + p2 * p2 * r4 * r4);
        if (x1 == 1 && x2 == 1 && x3 == 1) {
            if (p1 != 2 || p2 != 5 || p3 != 29 || p4 != 433 || p5 != 37666) return 28;
        }
        int64_t x1_2 = x1 * x1, x1_4 = x1_2 * x1_2, x1_6 = x1_4 * x1_2;
        int64_t x2_2 = x2 * x2, x2_4 = x2_2 * x2_2, x3_2 = x3 * x3;
        if (p1 * p4 != x1_4 * x2_2 * x3_2 * p2 * p2 + p3 * p3) return 29;
        if (p2 * p5 != x1_6 * x2_4 * x3_2 * p3 * p3 + p4 * p4) return 30;
    }

    /* Check Hurwitz n=4 exhaustive for x <= 40 across ALL FOUR entries (x1, x2, x3, x4) */
    for (int64_t a = 1; a <= 6; ++a) {
        for (int64_t x1 = 1; x1 <= 40; ++x1)
        for (int64_t x2 = x1; x2 <= 40; ++x2)
        for (int64_t x3 = x2; x3 <= 40; ++x3)
        for (int64_t x4 = x3; x4 <= 40; ++x4) {
            if (x1*x1 + x2*x2 + x3*x3 + x4*x4 == a*x1*x2*x3*x4) {
                if (a != 1 && a != 4) return 25;
                if (a == 1 && ((x1 & 3) != 2 || (x2 & 3) != 2 || (x3 & 3) != 2 || (x4 & 3) != 2)) return 26;
                if (a == 4 && ((x1 & 1) != 1 || (x2 & 1) != 1 || (x3 & 1) != 1 || (x4 & 1) != 1)) return 27;
            }
        }
    }
    return 0;
}

int main(void) {
    int rc;
    if ((rc = check_apollonian_and_octahedral()) != 0) {
        fprintf(stderr, "FAIL pillar1 rc=%d\n", rc);
        return rc;
    }
    if ((rc = check_sandpile_dhar_and_dets()) != 0) {
        fprintf(stderr, "FAIL pillar2 rc=%d\n", rc);
        return rc;
    }
    if ((rc = check_markov_cluster_and_hurwitz()) != 0) {
        fprintf(stderr, "FAIL pillar3 rc=%d\n", rc);
        return rc;
    }
    printf("{\"c11_status\":\"PASS\",\"version\":\"2.0.0\",\"pillars\":[1,2,3],\"dets\":[192,100352,1092,5393920],\"markov_mod32_sharp\":true,\"hurwitz_n4_clean\":true}\n");
    return 0;
}
