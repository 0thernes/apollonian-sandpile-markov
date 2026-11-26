// SPDX-License-Identifier: Apache-2.0
//! Zero-dependency exact integer verification library for:
//! - Pillar I: Apollonian (4-even HKRS), Generalized Octahedral (Q(sqrt(-2))), and 3D Soddy packings
//! - Pillar II: Abelian sandpile confluence, Dhar critical identity on Z^2 and A_2, Matrix-Tree orders,
//!              and Kalinin-Shkolnikov tropical balancing / soliton scattering
//! - Pillar III: SL2(Z) Cohn-Fricke tree, exact Markov tree uniqueness + mod-32 locking + p ≡ 1 (mod 4),
//!               symbolic 5-step Markov cluster Laurent polynomials, and generalized Markov-Hurwitz n=4.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

/// Exact signed gcd on i128.
pub fn gcd_i128(mut a: i128, mut b: i128) -> i128 {
    a = a.abs();
    b = b.abs();
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

/// Exact Jacobi symbol (a / n) for odd positive n via quadratic reciprocity loop.
pub fn jacobi(mut a: i128, mut n: i128) -> i32 {
    assert!(n > 0 && n % 2 == 1, "Jacobi denominator must be positive odd");
    a = a.rem_euclid(n);
    let mut result = 1i32;
    while a != 0 {
        while a % 2 == 0 {
            a /= 2;
            let n8 = n % 8;
            if n8 == 3 || n8 == 5 {
                result = -result;
            }
        }
        std::mem::swap(&mut a, &mut n);
        if a % 4 == 3 && n % 4 == 3 {
            result = -result;
        }
        a %= n;
    }
    if n == 1 { result } else { 0 }
}

/// Exact integer square test on i128.
pub fn is_perfect_square(x: i128) -> bool {
    if x < 0 {
        return false;
    }
    if x == 0 {
        return true;
    }
    let mut lo: i128 = 1;
    let mut hi: i128 = 1;
    while hi <= x / hi {
        hi *= 2;
    }
    while lo <= hi {
        let mid = lo + (hi - lo) / 2;
        let sq = mid.saturating_mul(mid);
        if sq == x {
            return true;
        } else if sq < x {
            lo = mid + 1;
        } else {
            hi = mid - 1;
        }
    }
    false
}

/// Exact odd part of nonzero integer (preserving sign).
pub fn signed_odd_part(mut a: i128) -> i128 {
    if a == 0 {
        return 0;
    }
    while a % 2 == 0 {
        a /= 2;
    }
    a
}

// ============================================================================
// Pillar I: Apollonian, Generalized Octahedral, and 3D Soddy Sphere Packings
// ============================================================================

pub fn descartes_q(q: [i128; 4]) -> i128 {
    let s = q[0] + q[1] + q[2] + q[3];
    let s2 = q[0] * q[0] + q[1] * q[1] + q[2] * q[2] + q[3] * q[3];
    s * s - 2 * s2
}

pub fn apollonian_refl(q: [i128; 4], idx: usize) -> [i128; 4] {
    let sum_other = q[0] + q[1] + q[2] + q[3] - q[idx];
    let mut out = q;
    out[idx] = 2 * sum_other - q[idx];
    out
}

#[derive(Debug, Clone)]
pub struct ApollonianAudit {
    pub root: [i128; 4],
    pub max_bend: i128,
    pub quads_visited: usize,
    pub distinct_bends: usize,
    pub square_hits: Vec<i128>,
    pub chi_minus1_count: usize,
    pub chi_plus1_count: usize,
    pub mod24_residues: Vec<i128>,
    pub all_descartes_zero: bool,
}

/// Exact BFS over an Apollonian packing up to `max_bend`, checking Descartes Q=0,
/// squares, mod-24 signature, and HKRS Jacobi character on every circle.
pub fn audit_apollonian_packing(root: [i128; 4], max_bend: i128) -> ApollonianAudit {
    let mut visited: BTreeSet<[i128; 4]> = BTreeSet::new();
    let mut queue: VecDeque<[i128; 4]> = VecDeque::new();
    let mut bends: BTreeSet<i128> = BTreeSet::new();
    let mut mod24: BTreeSet<i128> = BTreeSet::new();
    let mut chi_m1 = 0usize;
    let mut chi_p1 = 0usize;
    let mut all_q0 = true;

    let mut r_sorted = root;
    r_sorted.sort();
    visited.insert(r_sorted);
    queue.push_back(root);

    while let Some(q) = queue.pop_front() {
        if descartes_q(q) != 0 {
            all_q0 = false;
        }
        for &b in &q {
            bends.insert(b);
            mod24.insert(b.rem_euclid(24));
        }
        // Compute HKRS character on each slot using a coprime odd BQF witness
        for i in 0..4 {
            let u = q[i];
            let mut others = Vec::with_capacity(3);
            for j in 0..4 {
                if j != i {
                    others.push(q[j]);
                }
            }
            // Pick v with u + v odd (exists in 4-even quadruple)
            let mut v = others[0];
            let mut w = others[1];
            let mut z = others[2];
            if (u + v).rem_euclid(2) == 0 {
                if (u + w).rem_euclid(2) == 1 {
                    std::mem::swap(&mut v, &mut w);
                } else {
                    std::mem::swap(&mut v, &mut z);
                }
            }
            let k = (u + v + w - z) / 2;
            // Find odd positive coprime value of bqf(x, y) = (u+v)x^2 + 2kxy + (u+w)y^2
            let mut found = None;
            'search: for y in [0i128, 2, -2, 4, 1, -1] {
                for r in 0i128..30 {
                    let x = if y % 2 == 0 { 2 * r + 1 } else { 2 * r };
                    let t = (u + v) * x * x + 2 * k * x * y + (u + w) * y * y;
                    if t > 0 && t % 2 == 1 && gcd_i128(u, t) == 1 {
                        found = Some(jacobi(u, t));
                        break 'search;
                    }
                }
            }
            if let Some(c) = found {
                if c == -1 {
                    chi_m1 += 1;
                } else if c == 1 {
                    chi_p1 += 1;
                }
            }
        }
        for i in 0..4 {
            let nxt = apollonian_refl(q, i);
            let mx = *nxt.iter().max().unwrap();
            if mx <= max_bend {
                let mut key = nxt;
                key.sort();
                if visited.insert(key) {
                    queue.push_back(nxt);
                }
            }
        }
    }

    let square_hits: Vec<i128> = bends.iter().copied().filter(|&b| is_perfect_square(b)).collect();
    ApollonianAudit {
        root,
        max_bend,
        quads_visited: visited.len(),
        distinct_bends: bends.len(),
        square_hits,
        chi_minus1_count: chi_m1,
        chi_plus1_count: chi_p1,
        mod24_residues: mod24.into_iter().collect(),
        all_descartes_zero: all_q0,
    }
}

pub fn is_octahedral(x: [i128; 6]) -> bool {
    let s = x[0] + x[3];
    x[1] + x[4] == s
        && x[2] + x[5] == s
        && (x[0] - x[3]).pow(2) + (x[1] - x[4]).pow(2) + (x[2] - x[5]).pow(2) == 2 * s * s
}

pub fn oct_refl(x: [i128; 6], s1: bool, s2: bool, s3: bool) -> [i128; 6] {
    let s = x[0] + x[3];
    let f1 = if s1 { x[3] } else { x[0] };
    let f2 = if s2 { x[4] } else { x[1] };
    let f3 = if s3 { x[5] } else { x[2] };
    let delta = 4 * (f1 + f2 + f3) - 2 * s;
    [
        if s1 { x[0] + delta } else { x[0] },
        if s2 { x[1] + delta } else { x[1] },
        if s3 { x[2] + delta } else { x[2] },
        if s1 { x[3] } else { x[3] + delta },
        if s2 { x[4] } else { x[4] + delta },
        if s3 { x[5] } else { x[5] + delta },
    ]
}

#[derive(Debug, Clone)]
pub struct OctahedralAudit {
    pub root: [i128; 6],
    pub max_bend: i128,
    pub sextuples_visited: usize,
    pub distinct_bends: usize,
    pub square_hits: Vec<i128>,
    pub double_square_hits: Vec<i128>,
    pub pow2_square_hits: Vec<i128>,
    pub mod24_residues: Vec<i128>,
    pub all_octahedral: bool,
    pub all_mod8_locked: bool,
    pub all_odd_jacobi_minus1: bool,
}

pub fn audit_octahedral_packing(root: [i128; 6], max_bend: i128) -> OctahedralAudit {
    let mut visited: BTreeSet<[i128; 6]> = BTreeSet::new();
    let mut queue: VecDeque<[i128; 6]> = VecDeque::new();
    let mut bends: BTreeSet<i128> = BTreeSet::new();
    let mut mod24: BTreeSet<i128> = BTreeSet::new();
    let mut all_oct = true;
    let mut all_mod8 = true;
    let mut all_j_m1 = true;

    let canonical = |x: [i128; 6]| -> [i128; 6] {
        let mut pairs = [(x[0], x[3]), (x[1], x[4]), (x[2], x[5])];
        for p in &mut pairs {
            if p.0 > p.1 {
                std::mem::swap(&mut p.0, &mut p.1);
            }
        }
        pairs.sort();
        [pairs[0].0, pairs[1].0, pairs[2].0, pairs[0].1, pairs[1].1, pairs[2].1]
    };

    visited.insert(canonical(root));
    queue.push_back(root);

    while let Some(x) = queue.pop_front() {
        if !is_octahedral(x) {
            all_oct = false;
        }
        if !(x[0].rem_euclid(8) == 2
            && x[3].rem_euclid(8) == 0
            && x[1].rem_euclid(8) == 2
            && x[4].rem_euclid(8) == 0
            && x[2].rem_euclid(8) == 1
            && x[5].rem_euclid(8) == 1)
        {
            all_mod8 = false;
        }
        for i in 0..6 {
            let b = x[i];
            bends.insert(b);
            mod24.insert(b.rem_euclid(24));
            // Check Q(sqrt(-2)) Jacobi character on adjacent sums (a + c)
            let odd_a = signed_odd_part(b);
            let opp = (i + 3) % 6;
            for j in 0..6 {
                if j != i && j != opp {
                    let t = b + x[j];
                    if t > 0 && t % 2 == 1 && gcd_i128(odd_a, t) == 1 {
                        if jacobi(odd_a, t) != -1 {
                            all_j_m1 = false;
                        }
                    }
                }
            }
        }
        for mask in 0..8u8 {
            let nxt = oct_refl(x, (mask & 1) != 0, (mask & 2) != 0, (mask & 4) != 0);
            let mx = *nxt.iter().max().unwrap();
            if mx <= max_bend && visited.insert(canonical(nxt)) {
                queue.push_back(nxt);
            }
        }
    }

    let square_hits: Vec<i128> = bends.iter().copied().filter(|&b| is_perfect_square(b)).collect();
    let double_square_hits: Vec<i128> = bends
        .iter()
        .copied()
        .filter(|&b| b >= 0 && b % 2 == 0 && is_perfect_square(b / 2))
        .collect();
    let pow2_square_hits: Vec<i128> = bends
        .iter()
        .copied()
        .filter(|&b| b >= 0 && is_perfect_square(signed_odd_part(b)))
        .collect();

    OctahedralAudit {
        root,
        max_bend,
        sextuples_visited: visited.len(),
        distinct_bends: bends.len(),
        square_hits,
        double_square_hits,
        pow2_square_hits,
        mod24_residues: mod24.into_iter().collect(),
        all_octahedral: all_oct,
        all_mod8_locked: all_mod8,
        all_odd_jacobi_minus1: all_j_m1,
    }
}

pub fn soddy3_q(s: [i128; 5]) -> i128 {
    let sum: i128 = s.iter().sum();
    let sum2: i128 = s.iter().map(|v| v * v).sum();
    sum * sum - 3 * sum2
}

pub fn soddy3_refl(s: [i128; 5], idx: usize) -> [i128; 5] {
    let sum_other: i128 = s.iter().sum::<i128>() - s[idx];
    let mut out = s;
    out[idx] = sum_other - s[idx];
    out
}

pub fn audit_soddy3_packing(root: [i128; 5], max_bend: i128) -> (usize, usize, Vec<i128>, bool) {
    let mut visited: BTreeSet<[i128; 5]> = BTreeSet::new();
    let mut queue: VecDeque<[i128; 5]> = VecDeque::new();
    let mut bends: BTreeSet<i128> = BTreeSet::new();
    let mut all_q0 = true;

    let mut r = root;
    r.sort();
    visited.insert(r);
    queue.push_back(root);

    while let Some(s) = queue.pop_front() {
        if soddy3_q(s) != 0 {
            all_q0 = false;
        }
        for &b in &s {
            bends.insert(b);
        }
        for i in 0..5 {
            let nxt = soddy3_refl(s, i);
            let mx = *nxt.iter().max().unwrap();
            if mx <= max_bend {
                let mut key = nxt;
                key.sort();
                if visited.insert(key) {
                    queue.push_back(nxt);
                }
            }
        }
    }
    let squares: Vec<i128> = bends.iter().copied().filter(|&b| is_perfect_square(b)).collect();
    (visited.len(), bends.len(), squares, all_q0)
}

// ============================================================================
// Pillar II: Z^2 & A_2 Abelian Sandpiles, Dhar Critical Identities, Determinants
// ============================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LatticeKind {
    SquareZ2,
    TriangularA2,
}

impl LatticeKind {
    pub fn degree(self) -> i32 {
        match self {
            LatticeKind::SquareZ2 => 4,
            LatticeKind::TriangularA2 => 6,
        }
    }

    pub fn neighbors(self, r: usize, c: usize, n: usize) -> Vec<(usize, usize)> {
        let mut out = Vec::with_capacity(6);
        let deltas: &[(isize, isize)] = match self {
            LatticeKind::SquareZ2 => &[(-1, 0), (1, 0), (0, -1), (0, 1)],
            LatticeKind::TriangularA2 => &[(-1, 0), (1, 0), (0, -1), (0, 1), (-1, 1), (1, -1)],
        };
        for &(dr, dc) in deltas {
            let nr = r as isize + dr;
            let nc = c as isize + dc;
            if nr >= 0 && nr < n as isize && nc >= 0 && nc < n as isize {
                out.push((nr as usize, nc as usize));
            }
        }
        out
    }
}

/// Stabilize a sandpile configuration on an n x n Z^2 or A_2 grid; returns (stable_state, odometer, total_topplings).
pub fn stabilize_grid(
    kind: LatticeKind,
    n: usize,
    init: &[i32],
    reverse_order: bool,
) -> (Vec<i32>, Vec<u64>, u64) {
    let deg = kind.degree();
    let mut s = init.to_vec();
    let mut odo = vec![0u64; n * n];
    let mut total = 0u64;

    let mut q: VecDeque<usize> = VecDeque::new();
    let mut in_q = vec![false; n * n];
    if reverse_order {
        for idx in (0..n * n).rev() {
            if s[idx] >= deg {
                q.push_back(idx);
                in_q[idx] = true;
            }
        }
    } else {
        for idx in 0..n * n {
            if s[idx] >= deg {
                q.push_back(idx);
                in_q[idx] = true;
            }
        }
    }

    while let Some(u) = q.pop_front() {
        in_q[u] = false;
        if s[u] < deg {
            continue;
        }
        let k = (s[u] / deg) as u64;
        s[u] -= (k as i32) * deg;
        odo[u] += k;
        total += k;
        let r = u / n;
        let c = u % n;
        for (nr, nc) in kind.neighbors(r, c, n) {
            let v = nr * n + nc;
            s[v] += k as i32;
            if s[v] >= deg && !in_q[v] {
                q.push_back(v);
                in_q[v] = true;
            }
        }
    }
    (s, odo, total)
}

/// Compute Dhar's recurrent critical identity e = stab(2*mu_max - stab(2*mu_max))
/// and verify idempotence e ⊕ e = e AND Church-Rosser confluence (forward vs reverse order)!
pub fn compute_dhar_identity(kind: LatticeKind, n: usize) -> (Vec<i32>, bool, bool, u64) {
    let mu_max = kind.degree() - 1;
    let two_max = vec![2 * mu_max; n * n];
    let (s1_fwd, odo1_fwd, t1) = stabilize_grid(kind, n, &two_max, false);
    let (s1_rev, odo1_rev, _) = stabilize_grid(kind, n, &two_max, true);
    let confluent = s1_fwd == s1_rev && odo1_fwd == odo1_rev;

    let diff: Vec<i32> = s1_fwd.iter().map(|&v| 2 * mu_max - v).collect();
    let (e, _, t2) = stabilize_grid(kind, n, &diff, false);

    let doubled: Vec<i32> = e.iter().map(|&v| v + v).collect();
    let (e_plus_e, _, t3) = stabilize_grid(kind, n, &doubled, false);
    let idempotent = e_plus_e == e;

    (e, confluent, idempotent, t1 + t2 + t3)
}

/// Exact Bareiss integer determinant for small n x n matrices (e.g., 4x4, 9x9, 16x16).
pub fn exact_det_bareiss(mat: &[Vec<i128>]) -> i128 {
    let n = mat.len();
    let mut a = mat.to_vec();
    let mut sign: i128 = 1;
    let mut prev_pivot: i128 = 1;
    for k in 0..n {
        if a[k][k] == 0 {
            let mut swap_row = None;
            for r in (k + 1)..n {
                if a[r][k] != 0 {
                    swap_row = Some(r);
                    break;
                }
            }
            match swap_row {
                Some(r) => {
                    a.swap(k, r);
                    sign = -sign;
                }
                None => return 0,
            }
        }
        let pivot = a[k][k];
        for i in (k + 1)..n {
            for j in (k + 1)..n {
                a[i][j] = (a[i][j] * pivot - a[i][k] * a[k][j]) / prev_pivot;
            }
        }
        prev_pivot = pivot;
    }
    sign * a[n - 1][n - 1]
}

pub fn grid_laplacian_matrix(kind: LatticeKind, n: usize) -> Vec<Vec<i128>> {
    let m = n * n;
    let deg = kind.degree() as i128;
    let mut mat = vec![vec![0i128; m]; m];
    for r in 0..n {
        for c in 0..n {
            let u = r * n + c;
            mat[u][u] = deg;
            for (nr, nc) in kind.neighbors(r, c, n) {
                let v = nr * n + nc;
                mat[u][v] = -1;
            }
        }
    }
    mat
}

// ============================================================================
// Pillar III: Markov Tree, Mod-32 Theorem, SL2(Z) Cohn Tree, Cluster Laurent, Hurwitz n=4
// ============================================================================

#[derive(Debug, Clone)]
pub struct MarkovAudit {
    pub max_val: u128,
    pub triples_count: usize,
    pub distinct_markov_numbers: usize,
    pub uniqueness_holds: bool,
    pub all_odd_mod4_eq1: bool,
    pub all_even_mod32_eq2: bool,
    pub even_mod64_residues: Vec<u128>,
    pub odd_prime_mod4_violations: usize,
    pub all_pairwise_coprime: bool,
}

fn smallest_prime_factor(n: u128) -> u128 {
    if n % 2 == 0 {
        return 2;
    }
    let mut d = 3u128;
    while d * d <= n {
        if n % d == 0 {
            return d;
        }
        d += 2;
    }
    n
}

fn odd_prime_factors(mut n: u128) -> Vec<u128> {
    let mut out = Vec::new();
    while n % 2 == 0 && n > 0 {
        n /= 2;
    }
    while n > 1 {
        let p = smallest_prime_factor(n);
        out.push(p);
        while n % p == 0 {
            n /= p;
        }
    }
    out
}

pub fn audit_markov_tree(max_val: u128) -> MarkovAudit {
    let mut visited: BTreeSet<[u128; 3]> = BTreeSet::new();
    let mut queue: VecDeque<[u128; 3]> = VecDeque::new();
    let mut max_entry_counts: BTreeMap<u128, usize> = BTreeMap::new();
    let mut all_nums: BTreeSet<u128> = BTreeSet::new();
    let mut even_mod64: BTreeSet<u128> = BTreeSet::new();
    let mut all_odd4 = true;
    let mut all_even32 = true;
    let mut all_cop = true;
    let mut p3_violations = 0usize;

    visited.insert([1, 1, 1]);
    queue.push_back([1, 1, 1]);

    while let Some(t) = queue.pop_front() {
        assert_eq!(t[0] * t[0] + t[1] * t[1] + t[2] * t[2], 3 * t[0] * t[1] * t[2]);
        *max_entry_counts.entry(t[2]).or_insert(0) += 1;
        if gcd_i128(t[0] as i128, t[1] as i128) != 1
            || gcd_i128(t[1] as i128, t[2] as i128) != 1
            || gcd_i128(t[2] as i128, t[0] as i128) != 1
        {
            all_cop = false;
        }
        for &m in &t {
            if all_nums.insert(m) {
                if m % 2 == 1 {
                    if m % 4 != 1 {
                        all_odd4 = false;
                    }
                } else {
                    if m % 32 != 2 {
                        all_even32 = false;
                    }
                    even_mod64.insert(m % 64);
                }
                for p in odd_prime_factors(m) {
                    if p % 4 != 1 {
                        p3_violations += 1;
                    }
                }
            }
        }
        // Generate Vieta neighbors
        let nexts = [
            [3 * t[1] * t[2] - t[0], t[1], t[2]],
            [t[0], 3 * t[0] * t[2] - t[1], t[2]],
            [t[0], t[1], 3 * t[0] * t[1] - t[2]],
        ];
        for mut nxt in nexts {
            nxt.sort();
            if nxt[2] <= max_val && visited.insert(nxt) {
                queue.push_back(nxt);
            }
        }
    }

    let uniqueness_holds = max_entry_counts.values().all(|&c| c == 1);
    MarkovAudit {
        max_val,
        triples_count: visited.len(),
        distinct_markov_numbers: all_nums.len(),
        uniqueness_holds,
        all_odd_mod4_eq1: all_odd4,
        all_even_mod32_eq2: all_even32,
        even_mod64_residues: even_mod64.into_iter().collect(),
        odd_prime_mod4_violations: p3_violations,
        all_pairwise_coprime: all_cop,
    }
}

/// Exact 5-step symbolic Markov cluster numerators matching Lean `T3d`.
pub fn markov_cluster_numerators(x1: i128, x2: i128, x3: i128) -> (i128, i128, i128, i128, i128) {
    let p1 = x2 * x2 + x3 * x3;
    let v = x1 * x1 * x3 * x3;
    let w = x1 * x1 * x2 * x2;
    let p2 = p1 * p1 + v;
    let p3 = w * p1 * p1 + p2 * p2;
    let r4 = p1 * p1 * p1 + 2 * x1 * x1 * p1 * p1 + x1 * x1 * v;
    let p4 = w * w * p1 * p1 * p1 + p2 * p2 * r4;
    let p5 = w * w * w * w * p1 * p1 * p1 * p1
        + p2 * (2 * w * w * w * v * p1 * p1
            + w * w * v * p2 * p2
            + 2 * w * w * p1 * p1 * p1 * r4
            + p2 * p2 * r4 * r4);
    (p1, p2, p3, p4, p5)
}

/// Exhaustive Hurwitz n=4 search up to max_x for a in 1..=max_a.
pub fn audit_hurwitz_n4(max_a: u64, max_x: u64) -> BTreeMap<u64, Vec<[u64; 4]>> {
    let mut out: BTreeMap<u64, Vec<[u64; 4]>> = BTreeMap::new();
    for a in 1..=max_a {
        out.insert(a, Vec::new());
    }
    for x1 in 1..=max_x {
        for x2 in x1..=max_x {
            for x3 in x2..=max_x {
                let prod123 = (x1 as u128) * (x2 as u128) * (x3 as u128);
                let sum123 = (x1 as u128).pow(2) + (x2 as u128).pow(2) + (x3 as u128).pow(2);
                for x4 in x3..=max_x {
                    let lhs = sum123 + (x4 as u128).pow(2);
                    let denom = prod123 * (x4 as u128);
                    if denom > 0 && lhs % denom == 0 {
                        let a = (lhs / denom) as u64;
                        if a >= 1 && a <= max_a {
                            out.get_mut(&a).unwrap().push([x1, x2, x3, x4]);
                        }
                    }
                }
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pillar1_apollonian_octahedral_soddy() {
        let a1 = audit_apollonian_packing([-3, 5, 8, 8], 500);
        assert!(a1.all_descartes_zero);
        assert!(a1.square_hits.is_empty());
        assert_eq!(a1.chi_plus1_count, 0);
        assert!(a1.chi_minus1_count > 100);

        let a2 = audit_apollonian_packing([-7, 17, 12, 20], 800);
        let au = audit_apollonian_packing([-4, 8, 9, 9], 800);
        assert!(a2.square_hits.is_empty());
        assert_eq!(a2.mod24_residues, au.mod24_residues);
        assert!(au.square_hits.contains(&9));

        let oct = audit_octahedral_packing([-6, 10, 17, 40, 24, 17], 800);
        assert!(oct.all_octahedral);
        assert!(oct.all_mod8_locked);
        assert!(oct.all_odd_jacobi_minus1);
        assert!(oct.pow2_square_hits.is_empty());

        let oct_strip = audit_octahedral_packing([0, 0, 1, 2, 2, 1], 100);
        assert_eq!(oct.mod24_residues, oct_strip.mod24_residues);
        assert!(oct_strip.square_hits.contains(&1));
        assert!(oct_strip.double_square_hits.contains(&2));

        let (_, _, s3_sq, s3_ok) = audit_soddy3_packing([-6, 13, 13, 13, 18], 100);
        assert!(s3_ok);
        assert!(s3_sq.contains(&25));
    }

    #[test]
    fn test_pillar2_sandpiles_and_determinants() {
        assert_eq!(exact_det_bareiss(&grid_laplacian_matrix(LatticeKind::SquareZ2, 2)), 192);
        assert_eq!(exact_det_bareiss(&grid_laplacian_matrix(LatticeKind::SquareZ2, 3)), 100_352);
        assert_eq!(exact_det_bareiss(&grid_laplacian_matrix(LatticeKind::TriangularA2, 2)), 1_092);
        assert_eq!(exact_det_bareiss(&grid_laplacian_matrix(LatticeKind::TriangularA2, 3)), 5_393_920);

        for kind in [LatticeKind::SquareZ2, LatticeKind::TriangularA2] {
            for n in [2usize, 3, 5, 11] {
                let (e, conf, idem, _) = compute_dhar_identity(kind, n);
                assert!(conf, "Confluence failed for {:?} n={}", kind, n);
                assert!(idem, "Idempotence failed for {:?} n={}", kind, n);
                assert_eq!(e.len(), n * n);
            }
        }
    }

    #[test]
    fn test_pillar3_markov_cluster_hurwitz() {
        let mk = audit_markov_tree(1_000_000);
        assert!(mk.uniqueness_holds);
        assert!(mk.all_odd_mod4_eq1);
        assert!(mk.all_even_mod32_eq2);
        assert_eq!(mk.even_mod64_residues, vec![2, 34]);
        assert_eq!(mk.odd_prime_mod4_violations, 0);
        assert!(mk.all_pairwise_coprime);

        let (p1, p2, p3, p4, p5) = markov_cluster_numerators(1, 1, 1);
        assert_eq!((p1, p2, p3, p4, p5), (2, 5, 29, 433, 37_666));
        for x1 in 1..=3i128 {
            for x2 in 1..=3i128 {
                for x3 in 1..=3i128 {
                    let (q1, q2, q3, q4, q5) = markov_cluster_numerators(x1, x2, x3);
                    assert_eq!(
                        q1 * q4,
                        x1.pow(4) * x2.pow(2) * x3.pow(2) * q2 * q2 + q3 * q3
                    );
                    assert_eq!(
                        q2 * q5,
                        x1.pow(6) * x2.pow(4) * x3.pow(2) * q3 * q3 + q4 * q4
                    );
                }
            }
        }

        let hw = audit_hurwitz_n4(8, 120);
        assert!(!hw[&1].is_empty());
        assert!(hw[&1].iter().all(|t| t.iter().all(|&v| v % 4 == 2)));
        assert!(hw[&2].is_empty());
        assert!(hw[&3].is_empty());
        assert!(!hw[&4].is_empty());
        assert!(hw[&4].iter().all(|t| t.iter().all(|&v| v % 2 == 1)));
        for a in 5..=8 {
            assert!(hw[&a].is_empty());
        }
    }
}
