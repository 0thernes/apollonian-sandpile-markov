<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Apollonian–Sandpile–Markov (`0TH-2026-018`)

**Thin Vieta Reflection Groups, Apollonian–Octahedral Obstructions, Lattice Sandpile Identities, and Markov–Hurwitz Spectra: A Zero-Mathlib Six-Kernel Formalization.**

[![CI](https://github.com/0thernes/apollonian-sandpile-markov/actions/workflows/ci.yml/badge.svg)](https://github.com/0thernes/apollonian-sandpile-markov/actions/workflows/ci.yml)
[![Pages](https://github.com/0thernes/apollonian-sandpile-markov/actions/workflows/pages.yml/badge.svg)](https://0thernes.github.io/apollonian-sandpile-markov/)
[![Lean 4.35.0](https://img.shields.io/badge/Lean-4.35.0_Zero--Mathlib-blue)](lean/lean-toolchain)
[![Six Kernels](https://img.shields.io/badge/Formal_Kernels-6_Independent-brightgreen)](VERIFICATION.md)
[![Code License](https://img.shields.io/badge/Code-Apache--2.0-orange)](LICENSE-CODE)
[![Prose License](https://img.shields.io/badge/Paper_%26_Data-CC--BY--4.0-purple)](LICENSE)
[![ORCID](https://img.shields.io/badge/ORCID-0009--0006--8168--9648-a6ce39)](https://orcid.org/0009-0006-8168-9648)

![Visual overview of an HKRS Apollonian packing, the A2 51x51 Dhar identity computation, and the Markov tree](docs/media/social-preview.png)

- **Author:** Alexander Stephen Donahue (Independent Researcher, Spokane, WA, USA · ORCID `0009-0006-8168-9648`)
- **Version:** `v2.0.0` (November 26, 2026 — resolves all 13 paper items & all 9 formal-code items from the 2026-11-26 statement audit; see [`ERRATA.md`](ERRATA.md))
- **Archive ID:** `0TH-2026-018` (registered in [0thernes-research-archive](https://github.com/0thernes/0thernes-research-archive))
- **Live Interactive Observatory:** [https://0thernes.github.io/apollonian-sandpile-markov/studio/](https://0thernes.github.io/apollonian-sandpile-markov/studio/)
- **Live Lean 4 Proof Blueprint:** [https://0thernes.github.io/apollonian-sandpile-markov/blueprint/](https://0thernes.github.io/apollonian-sandpile-markov/blueprint/)
- **Frozen AMS-LaTeX White Paper:** [dist/Donahue_2026_apollonian_sandpile_markov.pdf](dist/Donahue_2026_apollonian_sandpile_markov.pdf)

---

## Summary

This repository contains a zero-Mathlib Lean 4.35.0 development with **16 headline statements** (`T1a`–`T3e` plus `T2f`), a master conjunction, constructive non-vacuity witnesses, and six false-variant refutations (**19 kernel-audited declarations**), together with Rust, ISO C11 (ASan/UBSan + 100k 7-law fuzz + `libFuzzer`), and Python programs that recompute and cross-check the finite data.

Most of the 16 statements are zero-Mathlib formalizations of known results: the Haag–Kertzer–Rickards–Stange square obstruction for three specific Apollonian packings, Ying Zhang's 2007 theorem that every even Markov number is 2 mod 32, the classical Hurwitz `n = 4` admissible-coefficient classification, and the Abelian sandpile toppling laws (Dhar 1990). The others are finite computations (including direct kernel-checked 9×9 Laplace determinants `detMat 9` in `T2b` and `T2f`), elementary identities, and one elementary parity lemma on the triangular lattice (`T2d`) for which no prior statement was found. No open problem is solved, and no theorem here is a bounded case of `STAT-058` or `NT-083`; those links are thematic only.

**What is checked and how.** All built Lean modules contain zero `sorry`, zero `admit`, and zero `native_decide`. The file `lean/PalomarChallenge.lean` holds 17 intentional `by sorry` stubs: it is the comparator challenge contract and is not a build target. All **19 audited declarations** depend strictly on `[propext, Classical.choice, Quot.sound]` (block below). Ubuntu CI runs `lake build` and diffs `VerifyAxioms.lean` against `results/lean_axioms.txt`; replays `Solution` and `PalomarSolution` with `leanchecker --fresh` and `leanchecker-paranoid` (`lean4lean`); checks an export of the three root declarations (master conjunction, `NonVacuity.nonvac_all_hypotheses`, `Adversarial.all_adversarial_refutations`) and their dependency closure with `nanoda_bin`, `con-leche`, and `con-ron`; runs `lake comparator --paranoid` on all 17 targets listed in `lean/comparator.json`; and executes a live negative kernel rejection gate proving tampered `sorry`, custom `axiom`, and altered statement inputs fail closed. CI also runs differential tests across Rust, C11, and Python and a Python semantic mutation harness (10/10 = 100% killed).

### What the Lean statements say

1. **Reflection groups and packings (`T1a`–`T1e`):**
   - `T1a`: The four Apollonian reflections are involutions preserving the Descartes form; for Descartes quadruples `(a+b)(a+c) = a^2 + k^2`; a two-square product identity for the associated binary quadratic form. Classical algebra, used as a lemma for `T1c`.
   - `T1b`: A Jacobi symbol built from Euler's criterion, with the `(-1/n)` and `(2/n)` laws, reciprocity for coprime odd `m, n ≥ 1`, multiplicativity, and `(a^2/n) = 1` for `gcd(a,n) = 1`. Classical; the proof follows Eisenstein's 1844 lattice-point argument.
   - `T1c`: In the packings generated by `(-3,5,8,8)`, `(-7,17,12,20)` and `(-11,21,24,28)` (every quadruple reachable by the four reflections), no curvature equals `m^2` for any integer `m`. This formalizes, for these three packings, the square obstruction of Haag, Kertzer, Rickards and Stange (*Ann. of Math.* 200 (2024), arXiv:2307.02749; Theorem 1.6 for `(-3,5,8,8)`, Appendix Table A for the other two); only the zero-Mathlib parabolic Dehn-twist CRT proof route is new. The contrast root `rootSquareContrast = (9,9,-4,8)` is shown in Lean to have Descartes form 0 and to contain the square `9 = 3^2`. Its mod-24 curvature set `{0,8,9,12,17,20}` equals that of `(-7,17,12,20)` (a computation, not a Lean statement). It is **not** an unobstructed packing: HKRS list quadratic obstructions `3n^2`, `6n^2` and quartic obstructions `n^4`, `4n^4` for it.
   - `T1d`: Eight octahedral reflections are involutions preserving the octahedral equations, and a `sqrt(-2)` norm identity holds. Every sextuple reachable from `(-6,10,17,40,24,17)` has residues `(2,2,1,0,0,1)` mod 8, so `b1, b2` are never squares and `b3, b6` are never twice a square. This is a mod-8 congruence argument. The five Jacobi symbol values in the statement are closed evaluations not linked to the orbit, and no reciprocity argument is formalized. The strip `(0,0,1,2,2,1)` is the contrast. Quadratic reciprocity obstructions for generalized/octahedral packings were given by Shi, Shi, Whitehead, Williams-Tracy and Zhang (arXiv:2510.21702, 2025).
   - `T1e`: For natural `d ≥ 2`, `(d - 1) ∣ 2 ↔ d = 2 ∨ d = 3` (the arithmetic divisibility fact used in Lagarias–Mallows–Wilks 2002; Lean does not link it to general `d`-dimensional Soddy reflections). All five 3D Soddy reflections are involutions preserving the 3D Soddy form `3∑ b_i^2 - (∑ b_i)^2` (all five preservation laws exported in `v2.0.0`), and one reflection of `(-6,13,13,13,18)` produces `25 = 5^2`.
2. **Sandpiles and lattice Laplacians (`T2a`–`T2f`):**
   - `T2a`: For `SandpileGraph n` (symmetric zero-diagonal adjacency with arbitrary degrees, no sink condition), topplings commute; any legal trace fires each vertex at most `w` times for a stabilizing odometer `w` (least action bound); two legal stabilizing traces have equal firing counts and equal results. No termination theorem is formalized. The Abelian property is due to Dhar (1990) and the least action principle is a known result.
   - `T2b`: Direct Lean determinants `det4 (gridLap 2) = 192` and `detMat 9 (gridLap 3) = 100,352` (via our zero-Mathlib general `n × n` Laplace determinant `detMat` and verified row-operation certificate added in `v2.0.0`), plus the `D_4` integer block similarity `Q * Qinv = 4I`, `L * Q = Q * D` with `4 * det(B2)^2 * det(B4) = 100,352`, and explicit legal Dhar toppling traces reaching `[2,2,2,2]` and `[2,1,2,1,0,1,2,1,2]`. No Matrix–Tree theorem or sandpile-group-identity theorem is formalized.
   - `T2c`: No integer `u` on `Z^2` with `4u = 3(x^2+y^2) + ψ`, `ψ` doubly periodic, has square-lattice Laplacian `≤ 3` everywhere; four explicit functions have constant Laplacian 2 or 3. This is one isotropic case, not the Levine–Pegden–Smart classification.
   - `T2d` (elementary parity lemma, no prior statement found): Let `M ≥ 1`, `ψ` doubly periodic, and `u : Z^2 → Z` with `M*u = A*x^2 + B*x*y + C*y^2 + D*x + E*y + ψ`. If `M*K = 4A - 2B + 4C` and the six-neighbour triangular-lattice Laplacian of `u` is `≤ K` everywhere, then `K` is even; so `K = 5` is impossible in this class, while `K = 4` and `K = 2` are attained. The lemma says nothing about sandpile configurations of height 5 or about the `A_2` sandpile identity.
   - `T2e`: A lattice-polygon edge-normal closure identity `∑ R_{90°}(v_{i+1} - v_i) = (0,0)`, the identity `det(v1,v2) = det(v2,v3) = det(v3,v1)` when `v1 + v2 + v3 = 0`, and closed numeric checks. The Kalinin–Shkolnikov theorem is not formalized; the declaration name is descriptive only.
   - `T2f`: Direct Lean determinants `det4 (a2GridLap 2) = 1,092` and `detMat 9 (a2GridLap 3) = 5,393,920`, plus the Klein-4 integer block similarity `Q_A2 * Q_A2_inv = 4I`, `L_A2 * Q_A2 = Q_A2 * D_A2` with `7 * 28 * 40 * 688 = 5,393,920`, and explicit legal Dhar toppling traces reaching `[4,3,3,4]` and `[4,2,3,2,0,2,3,2,4]` on `A_2`. No Matrix–Tree or group-identity theorem is formalized.
3. **Markov–Hurwitz equations and cluster mutations (`T3a`–`T3e`):**
   - `T3a`: The Fricke trace identity for 2×2 integer matrices of determinant 1, and at every node of the Cohn tree from `A_0 = ((1,1),(1,2))`, `B_0 = ((1,2),(2,5))`: determinant 1, `tr[A,B] = -2`, explicit divisibility `3 ∣ tr A ∧ 3 ∣ tr B ∧ 3 ∣ tr(A B)` (exported in `v2.0.0`), and the quotients `tr/3` satisfy the Markov equation. Classical (Fricke; Cohn 1955).
   - `T3b`: For triples reachable from `(1,1,1)` by Vieta moves: positive, Markov, pairwise coprime; odd primes dividing the first entry are 1 mod 4; an odd first entry is 1 mod 4; an even first entry is 2 mod 32; `(2,1,1)` and `(34,13,1)` occur, so the residue mod 64 is not fixed. The mod-32 statement and these witnesses are Ying Zhang's theorem (*Congruence and uniqueness of certain Markoff numbers*, Acta Arith. 128 (2007) 295–301, arXiv:math/0612620); this repository gives a zero-Mathlib formalization of it. Markov's theorem that every positive Markov triple lies in the tree is not formalized.
   - `T3c`: For an odd prime `p` and `k ≥ 1`, if `p^k` divides `r1^2 + 1` and `r2^2 + 1` then `p^k` divides `r1 - r2` or `r1 + r2`. Standard elementary number theory.
   - `T3d`: Exchange identities along one five-step mutation sequence of the Markov quiver (whose `(1,1,1)` specialization passes through `(2,5,29)`, `(5,29,433)`, `(29,433,37666)`): `P1*P4 = x1^4 x2^2 x3^2 P2^2 + P3^2` and `P2*P5 = x1^6 x2^4 x3^2 P3^2 + P4^2` for explicit subtraction-free polynomials, including divisions by the non-monomial `P1 = x2^2 + x3^2` and `P2 = P1^2 + x1^2 x3^2`. Lean states positivity of values at positive integers; coefficient positivity holds by inspection of the definitions, not as a stated theorem. Finite instance of Fomin–Zelevinsky (2002) and Lee–Schiffler (2015).
   - `T3e`: Positive integer solutions of `x1^2 + x2^2 + x3^2 + x4^2 = a*x1*x2*x3*x4` exist only for `a = 1` (all `x_i ≡ 2 mod 4`) or `a = 4` (all `x_i` odd); there are none for `a ∈ {2,3}` or `a ≥ 5`; explicit solutions are given. Classical classification of admissible coefficients (Hurwitz, 1907). The description of all solutions as Vieta orbits is not part of the exported statement.

`NonVacuity.lean` provides constructive premise witnesses across all pillars (including explicit witnesses for the `T2d` hypothesis bundle and `IsStabilizingOdometer` on `gridGraph 2` and `a2GridGraph 3` added in `v2.0.0`). `Adversarial.lean` proves six refutations of false variants; `adv6` is a corollary of `T3e`, and the suite does not claim every single hypothesis of every theorem is individually tight.

---

## 5-Second Axiom Certificate (`results/lean_axioms.txt`, Verbatim)

Verified by `scripts/check_readme_axioms.py` against the output of `lake env lean VerifyAxioms.lean` (also diffed in CI):

```text
'ApollonianSandpileMarkov.Palomar.t1a_descartes_lorentzian_and_gaussian_norm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ApollonianSandpileMarkov.Palomar.t1b_jacobi_reciprocity_master' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ApollonianSandpileMarkov.Palomar.t1c_hkrs_apollonian_reciprocity_obstruction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ApollonianSandpileMarkov.Palomar.t1d_octahedral_lorentzian_and_sqrt_neg2_obstruction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ApollonianSandpileMarkov.Palomar.t1e_soddy_dimension_dichotomy_and_3d_contrast' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ApollonianSandpileMarkov.Palomar.t2a_abelian_sandpile_confluence_and_least_action' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ApollonianSandpileMarkov.Palomar.t2b_dhar_critical_identity_and_grid_orders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ApollonianSandpileMarkov.Palomar.t2c_lps_z2_superharmonic_and_isotropic_obstruction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ApollonianSandpileMarkov.Palomar.t2d_triangular_a2_even_laplacian_rigidity_and_obstruction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ApollonianSandpileMarkov.Palomar.t2e_kalinin_shkolnikov_tropical_balancing_and_solitons' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ApollonianSandpileMarkov.Palomar.t2f_a2_grid_orders_and_dhar_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ApollonianSandpileMarkov.Palomar.t3a_sl2z_fricke_cohn_markov_correspondence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ApollonianSandpileMarkov.Palomar.t3b_markov_coprimality_odd_primes_and_mod32' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ApollonianSandpileMarkov.Palomar.t3c_hensel_sqrt_neg1_prime_power_uniqueness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ApollonianSandpileMarkov.Palomar.t3d_cluster_algebra_markov_laurent_positivity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ApollonianSandpileMarkov.Palomar.t3e_markov_hurwitz_n4_complete_classification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ApollonianSandpileMarkov.Palomar.prove_all_apollonian_sandpile_markov_theorems' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ApollonianSandpileMarkov.NonVacuity.nonvac_all_hypotheses' depends on axioms: [propext, Classical.choice, Quot.sound]
'ApollonianSandpileMarkov.Adversarial.all_adversarial_refutations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

---

## Quickstart & One-Command Reproduction

```bash
# 1. Offline Python quickstart exercising all three pillars
PYTHONPATH=python python examples/quickstart_demo.py

# 2. Zero-dependency Rust core tests & JSON summary
(cd rust && cargo clippy --all-targets -- -D warnings && cargo test --release && cargo run --release -- --json ../results/rust_summary.json)

# 3. Independent ISO C11 verifier + 100k 7-law fuzzer + libFuzzer (Linux/macOS with gcc/clang)
gcc -std=c11 -O2 -Wall -Wextra -Werror -fsanitize=address,undefined native/asm_verify.c -o native/asm_verify && ./native/asm_verify
gcc -std=c11 -O2 -Wall -Wextra -Werror -fsanitize=address,undefined native/fuzz_asm.c -o native/fuzz_asm && ./native/fuzz_asm
clang -std=c11 -O1 -g -Wall -Wextra -Werror -fsanitize=fuzzer,address,undefined native/fuzz_libfuzzer.c -o native/fuzz_libfuzzer && ./native/fuzz_libfuzzer -max_total_time=5

# 4. Python exact oracle, Hypothesis property suite, differential tests & 10/10 mutation suite
PYTHONPATH=python pytest -v tests/test_all.py
PYTHONPATH=python python scripts/mutate.py

# 5. Zero-Mathlib Lean 4.35.0 build, axiom audit & fresh leanchecker
(cd lean && lake build && lake env lean VerifyAxioms.lean && lake env leanchecker --fresh Solution && lake env leanchecker --fresh PalomarSolution)

# 6. Full repo hygiene, verbatim axioms, and 23/23 live citation verification
python scripts/check_readme_axioms.py && python scripts/check_citations.py && python scripts/audit_repo.py
```

Or run `just all` via [`justfile`](justfile).

---

## Usage & Examples

- **Python CLI / library (`python/apollonian_sandpile_markov/oracle.py`):**
  ```bash
  PYTHONPATH=python python examples/quickstart_demo.py
  PYTHONPATH=python python -m apollonian_sandpile_markov.oracle --json results/exact_verification_report.json
  ```
- **Rust CLI (`rust/src/main.rs`):**
  ```bash
  (cd rust && cargo run --release -- --json ../results/rust_summary.json)
  ```
- **Interactive Browser Observatory & Blueprint:** Open `studio/index.html` or `blueprint/index.html` locally or visit GitHub Pages.

---

## Scope and Open Problems

All 16 statements are kernel-checked as written; their exact scope is given above and in [`CLAIMS.md`](CLAIMS.md). All 13 paper items and 9 formal-code items from the 2026-11-26 statement audit are logged and resolved in [`ERRATA.md`](ERRATA.md). The following problems remain open and are not addressed by any theorem here (see [`LIMITATIONS.md`](LIMITATIONS.md)):
- Classification of reciprocity obstructions across all primitive Apollonian and generalized circle or sphere packings;
- The continuum scaling limit of the $\mathbb{Z}^2$ or $\mathbb{A}_2$ sandpile identity (`STAT-058`), and the description of integer superharmonic matrices on $\mathbb{A}_2$;
- The Markov uniqueness conjecture (`NT-083`);
- A formalization of all-depth cluster positivity (proved by Lee–Schiffler 2015) and of Hurwitz equations for $n \ge 5$.

---

## Maintenance & Licensing

- **Status:** Actively maintained `v2.0.0` archival research release. Report findings via GitHub Issues (10-class Build Standard taxonomy).
- **Dual License:** All software, Lean 4 proofs, Rust/C11/Python code, scripts, and studio HTML/JS are licensed under **Apache-2.0** ([`LICENSE-CODE`](LICENSE-CODE)). All prose, white paper, figures, documentation, and verified datasets are licensed under **CC-BY-4.0** ([`LICENSE`](LICENSE)).
