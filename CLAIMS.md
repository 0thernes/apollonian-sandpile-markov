<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Claims Matrix (`CLAIMS.md`, v1.0.0)

Every mathematical and empirical claim in `apollonian-sandpile-markov` (`0TH-2026-017`) is mapped below to its exact machine-checked Lean 4 declaration, independent computational oracle, and explicit epistemic tier.

## Tier 1 — Unconditionally Machine-Checked (Lean 4.35.0, Zero Mathlib, 6 Kernels)

| Claim ID | Lean Declaration (`ApollonianSandpileMarkov.Palomar.*`) | Statement Summary | Axioms |
| :--- | :--- | :--- | :--- |
| `T1a` | `t1a_descartes_lorentzian_and_gaussian_norm` | Descartes Lorentzian involutions, `(a+b)(a+c)=a^2+k^2`, Brahmagupta–Descartes BQF | `[propext, Classical.choice, Quot.sound]` |
| `T1b` | `t1b_jacobi_reciprocity_master` | Zero-Mathlib Jacobi symbol, Eisenstein (1844) QR, `(-1/n)`, `(2/n)`, multiplicativity, squares=1 | `[propext, Classical.choice, Quot.sound]` |
| `T1c` | `t1c_hkrs_apollonian_reciprocity_obstruction` | Zero-GCD Dehn-twist CRT global square obstruction on `(-3,5,8,8)`, `(-7,17,12,20)`, `(-11,21,24,28)` vs `(-4,8,9,9)` | `[propext, Classical.choice, Quot.sound]` |
| `T1d` | `t1d_octahedral_lorentzian_and_sqrt_neg2_obstruction` | Octahedral $\mathbb{Q}(\sqrt{-2})$ 8 reflections, mod-8 locking & Jacobi obstruction on `(-6,10,17,40,24,17)` vs strip | `[propext, Classical.choice, Quot.sound]` |
| `T1e` | `t1e_soddy_dimension_dichotomy_and_3d_contrast` | Exact Soddy integrality dichotomy `(d-1) ∣ 2 ↔ d=2 ∨ d=3` + 3D square hit `25=5^2` | `[propext, Classical.choice, Quot.sound]` |
| `T2a` | `t2a_abelian_sandpile_confluence_and_least_action` | Universal Abelian commutativity, Discrete Least Action, Church–Rosser confluence | `[propext, Classical.choice, Quot.sound]` |
| `T2b` | `t2b_dhar_critical_identity_and_grid_orders` | Exact `det(L_{2×2})=192`, `det(L_{3×3})=100,352` (Kronecker) + legal Dhar traces | `[propext, Quot.sound]` |
| `T2c` | `t2c_lps_z2_superharmonic_and_isotropic_obstruction` | LPS $\mathbb{Z}^2$ torus Green's id, isotropic `K=3` obstruction, `K=2,3` witnesses | `[propext, Classical.choice, Quot.sound]` |
| `T2d` | `t2d_triangular_a2_even_laplacian_rigidity_and_obstruction` | **Original $\mathbb{A}_2$ Even-Laplacian Rigidity:** `K % 2 = 0` universally obstructing `K=5`; `K=4,2` witnesses | `[propext, Classical.choice, Quot.sound]` |
| `T2e` | `t2e_kalinin_shkolnikov_tropical_balancing_and_solitons` | Universal cyclic lattice polygon balancing, trivalent det invariance, 2-/3-soliton balances | `[propext, Classical.choice, Quot.sound]` |
| `T3a` | `t3a_sl2z_fricke_cohn_markov_correspondence` | Universal $SL_2(\mathbb{Z})$ Fricke trace identity & infinite Cohn tree `tr/3` correspondence | `[propext, Classical.choice, Quot.sound]` |
| `T3b` | `t3b_markov_coprimality_odd_primes_and_mod32` | Pairwise coprimality, odd `p ≡ 1 (4)`, odd `m ≡ 1 (4)`, **Exact Mod-32 (`m % 32 = 2`)**, sharp mod 64 | `[propext, Classical.choice, Quot.sound]` |
| `T3c` | `t3c_hensel_sqrt_neg1_prime_power_uniqueness` | Universal Hensel lifting uniqueness of $\sqrt{-1} \pmod{p^k}$ for all odd primes `p`, `k ≥ 1` | `[propext, Classical.choice, Quot.sound]` |
| `T3d` | `t3d_cluster_algebra_markov_laurent_positivity` | Symbolic 3-variable 5-step Markov cluster Laurent integrality & positivity (`(1,1,1) ↦ (2,5,29,433,37666)`) | `[propext, Classical.choice, Quot.sound]` |
| `T3e` | `t3e_markov_hurwitz_n4_complete_classification` | Complete Markov–Hurwitz `n=4` classification (`a=1` all `≡ 2 mod 4`; `a=4` all odd; `a∈{2,3} ∪ [5,∞)` empty) | `[propext, Classical.choice, Quot.sound]` |
| `NONVAC` | `NonVacuity.nonvac_all_hypotheses` | Constructive non-vacuity witnesses for all 15 theorem premises | `[propext, Classical.choice, Quot.sound]` |
| `ADV` | `Adversarial.all_adversarial_refutations` | Sharp boundary counterexamples showing every structural hypothesis is tight | `[propext, Classical.choice, Quot.sound]` |

## Tier 2 — Exact Independent Computational Verification (Rust, ISO C11, Python)

- `C1`: Exact BFS orbit statistics (`results/rust_summary.json` & `results/exact_verification_report.json`) across all 4 Apollonian roots (`≤ 1000`), 2 Octahedral roots (`≤ 1500` / `≤ 400`), and 3D Soddy (`≤ 150`), bit-for-bit identical between Rust and Python.
- `C2`: Exact Bareiss integer determinants `det(L_{A_2, 2×2}) = 1,092`, `det(L_{A_2, 3×3}) = 5,393,920`, and $15\times 15$ & $65\times 65$ Dhar critical identities (`results/figure_stats.json`).
- `C3`: Exhaustive Markov tree audit up to $10^7$ (`56` triples, `56` distinct numbers, uniqueness=`true`, `61` odd primes `p ≡ 1 (4)`, `0` violations, even mod-64 set `{2, 34}`) and Hurwitz `n=4` search `≤ 120`.

## Tier 3 — Explicitly Open Conjectures (NOT Claimed Solved)

- `O1`: Complete classification of all reciprocity obstructions across all primitive integral Apollonian and Bianchi sphere packings.
- `O2`: Full continuum PDE scaling limit of the $\mathbb{Z}^2$ and $\mathbb{A}_2$ sandpile identities (`STAT-058`).
- `O3`: General-composite Markov Uniqueness Conjecture (`NT-083`).
- `O4`: Machine-checked formalization of Lee–Schiffler all-depth cluster positivity and Hurwitz $n \ge 5$ asymptotics.
