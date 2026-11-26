<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Apollonian–Sandpile–Markov (`0TH-2026-018`)

**Thin Vieta Reflection Groups, Apollonian–Octahedral Reciprocity Obstructions, Integer-Superharmonic Sandpile Envelopes, and Markov–Hurwitz Geodesic Spectra: A Zero-Mathlib Six-Kernel Formalization.**

[![CI](https://github.com/0thernes/apollonian-sandpile-markov/actions/workflows/ci.yml/badge.svg)](https://github.com/0thernes/apollonian-sandpile-markov/actions/workflows/ci.yml)
[![Pages](https://github.com/0thernes/apollonian-sandpile-markov/actions/workflows/pages.yml/badge.svg)](https://0thernes.github.io/apollonian-sandpile-markov/)
[![Lean 4.35.0](https://img.shields.io/badge/Lean-4.35.0_Zero--Mathlib-blue)](lean/lean-toolchain)
[![Six Kernels](https://img.shields.io/badge/Formal_Kernels-6_Independent-brightgreen)](VERIFICATION.md)
[![Code License](https://img.shields.io/badge/Code-Apache--2.0-orange)](LICENSE-CODE)
[![Prose License](https://img.shields.io/badge/Paper_%26_Data-CC--BY--4.0-purple)](LICENSE)
[![ORCID](https://img.shields.io/badge/ORCID-0009--0006--8168--9648-a6ce39)](https://orcid.org/0009-0006-8168-9648)

![Visual overview of HKRS Apollonian packing, A2 sandpile Even-Laplacian rigidity, and Cohn-Markov Mod-32 tree](docs/media/social-preview.png)

- **Author:** Alexander Stephen Donahue (Independent Researcher, Spokane, WA, USA · ORCID `0009-0006-8168-9648`)
- **Archive ID:** `0TH-2026-018` (registered in [0thernes-research-archive](https://github.com/0thernes/0thernes-research-archive))
- **Live Interactive Observatory:** [https://0thernes.github.io/apollonian-sandpile-markov/studio/](https://0thernes.github.io/apollonian-sandpile-markov/studio/)
- **Live Lean 4 Proof Blueprint:** [https://0thernes.github.io/apollonian-sandpile-markov/blueprint/](https://0thernes.github.io/apollonian-sandpile-markov/blueprint/)
- **Frozen AMS-LaTeX White Paper:** [dist/Donahue_2026_apollonian_sandpile_markov.pdf](dist/Donahue_2026_apollonian_sandpile_markov.pdf)

---

## Executive Summary

Three celebrated areas of arithmetic geometry, statistical mechanics, and algebraic combinatorics are driven by the same algebraic generator: **quadratic Vieta involutions** on indefinite integer forms. This repository delivers **15 machine-checked headline theorems (`T1a`–`T3e`)**, constructive non-vacuity witnesses, and sharp adversarial counterexamples in **zero-Mathlib Lean 4.35.0** (zero `sorry`, zero `admit`, zero `native_decide`, zero external dependencies), independently replayed across **six formal type-checking kernels** (`lean 4.35.0`, `leanchecker`, `leanchecker-paranoid`/`lean4lean`, `nanoda_bin`, `con-leche`, `con-ron` + `lake comparator --paranoid`) and cross-verified bit-for-bit across **Rust**, **ISO C11 (ASan/UBSan + 100k fuzz)**, and **Python + Hypothesis + 100% (8/8) mutation testing**.

### Headline Results Across Three Unified Pillars

1. **Pillar I — Thin Vieta Reflection Groups (`T1a`–`T1e`):**
   - `T1a`: Descartes Lorentzian form, Gaussian norm `(a+b)(a+c) = a^2 + k^2`, and Brahmagupta–Descartes BQF identity.
   - `T1b`: Self-contained zero-Mathlib Legendre–Jacobi symbol, Gauss's Lemma, Eisenstein (1844) lattice-point proof of Gauss Quadratic Reciprocity, and both Supplementary Laws.
   - `T1c`: Zero-GCD-exception parabolic Dehn-twist CRT formal proof of the Haag–Kertzer–Rickards–Stange (*Annals of Mathematics*, 2024) global square obstruction on `(-3,5,8,8)`, `(-7,17,12,20)`, and `(-11,21,24,28)`, contrasted with `(-4,8,9,9)` (identical mod-24 residue set `{0,8,9,12,17,20}`, 8 squares `9, 36, ..., 900` up to `1000`).
   - `T1d`: Generalized Octahedral $\mathbb{Q}(\sqrt{-2})$ Lorentzian sextuples, 8 face reflections, exact mod-8 antipodal locking and Jacobi obstruction on `(-6,10,17,40,24,17)` vs. unobstructed strip `(0,0,1,2,2,1)` (identical mod-24 set `{0,1,2,8,9,10,16,17,18}`).
   - `T1e`: Exact Soddy dimension integrality dichotomy `(d - 1) ∣ 2 ↔ d = 2 ∨ d = 3` plus 3D integral cluster `(-6,13,13,13,18)` reflecting to `25 = 5^2`.
2. **Pillar II — Abelian Sandpiles & Tropical Curves (`T2a`–`T2e`, `STAT-058`):**
   - `T2a`: Universal Abelian sandpile toppling commutativity, Discrete Least Action Principle, and Church–Rosser confluence on arbitrary finite sinked graphs.
   - `T2b`: Exact Matrix–Tree determinants `det(L_{Z^2, 2×2}) = 192` and `det(L_{Z^2, 3×3}) = 100,352` (via integer Kronecker block-diagonalization) plus explicit legal Dhar critical identity traces (`[2,2,2,2]` and `[2,1,2,1,0,1,2,1,2]`). Rust/Python Bareiss determinants also certify `det(L_{A_2, 2×2}) = 1,092` and `det(L_{A_2, 3×3}) = 5,393,920`.
   - `T2c`: Levine–Pegden–Smart $\mathbb{Z}^2$ discrete Green's First Identity on the torus, periodic superharmonic rigidity, isotropic max-sea `K = 3` obstruction, and constant-Laplacian `2, 3` witnesses.
   - `T2d` (**Original Theorem — Triangular Lattice $\mathbb{A}_2$ Even-Laplacian Rigidity**): Every periodic integer superharmonic envelope `M*u = A*x^2+B*x*y+C*y^2+D*x+E*y+ψ` on the 6-regular triangular lattice $\mathbb{A}_2$ with `Δ_{A2} u ≤ K` and mean curvature `M*K = 4A-2B+4C` MUST satisfy **`K % 2 = 0`**, universally obstructing the maximal stable sea `K = 5` while certifying `K = 4` and `K = 2`.
   - `T2e`: Universal Kalinin–Shkolnikov cyclic lattice polygon balancing `∑ R_{90°}(v_{i+1} - v_i) = (0,0)`, trivalent determinant invariance, and 2-/3-soliton scattering balances.
3. **Pillar III — Markov–Hurwitz & Cluster Spectra (`T3a`–`T3e`, `NT-083`):**
   - `T3a`: Universal $SL_2(\mathbb{Z})$ Fricke trace identity and infinite Cohn matrix tree `tr/3` correspondence.
   - `T3b`: Universal Markov pairwise coprimality, odd-prime `p ≡ 1 (mod 4)` obstruction, odd Markov `m ≡ 1 (mod 4)`, and **Exact Mod-32 Theorem** (`e % 32 = 2` for every even Markov number, sharp mod 64 at `2` and `34`).
   - `T3c`: Universal Hensel lifting uniqueness of $\sqrt{-1} \pmod{p^k}$ for every odd prime $p$ and exponent $k \ge 1$.
   - `T3d`: Symbolic 3-variable Fomin–Zelevinsky cluster-algebra Laurent integrality and positivity on the Markov quiver through **5 mutations** including BOTH consecutive non-monomial divisions (`P1 = x2^2+x3^2` and `P2 = P1^2+x1^2*x3^2`), specializing at `(1,1,1)` to `(2, 5, 29, 433, 37666)`.
   - `T3e`: Complete Markov–Hurwitz $n=4$ classification via well-founded Vieta descent (`a ∈ {2,3}` and `a ≥ 5` empty; `a=1` forces all `x_i ≡ 2 mod 4`; `a=4` forces all `x_i` odd).

---

## 5-Second Axiom Certificate (`results/lean_axioms.txt`, Verbatim)

Verified by `scripts/check_readme_axioms.py` and replayed across all six formal kernels in CI:

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
'ApollonianSandpileMarkov.Palomar.t2b_dhar_critical_identity_and_grid_orders' depends on axioms: [propext, Quot.sound]
'ApollonianSandpileMarkov.Palomar.t2c_lps_z2_superharmonic_and_isotropic_obstruction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ApollonianSandpileMarkov.Palomar.t2d_triangular_a2_even_laplacian_rigidity_and_obstruction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ApollonianSandpileMarkov.Palomar.t2e_kalinin_shkolnikov_tropical_balancing_and_solitons' depends on axioms: [propext,
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
(cd rust && cargo test --release && cargo run --release -- --json ../results/rust_summary.json)

# 3. Independent ISO C11 verifier + 100k fuzzer (Linux/macOS with gcc/clang)
gcc -std=c11 -O2 -Wall -Wextra -Werror -fsanitize=address,undefined native/asm_verify.c -o native/asm_verify && ./native/asm_verify
gcc -std=c11 -O2 -Wall -Wextra -Werror -fsanitize=address,undefined native/fuzz_asm.c -o native/fuzz_asm && ./native/fuzz_asm

# 4. Python exact oracle, Hypothesis property suite, differential tests & 100% mutation suite
PYTHONPATH=python pytest -v tests/test_all.py
PYTHONPATH=python python scripts/mutate.py

# 5. Zero-Mathlib Lean 4.35.0 build, axiom audit & leanchecker
(cd lean && lake build && lake env lean VerifyAxioms.lean && lake env leanchecker Solution && lake env leanchecker PalomarSolution)

# 6. Full repo hygiene, verbatim axioms, and citation verification
python scripts/check_readme_axioms.py && python scripts/check_citations.py --offline && python scripts/audit_repo.py
```

Or run `just all` via [`justfile`](justfile).

---

## Honest Epistemic Boundaries

All 15 theorems (`T1a`–`T3e`) are unconditionally machine-checked. The following overarching open conjectures are **explicitly NOT claimed as solved** (see [`CLAIMS.md`](CLAIMS.md) and [`LIMITATIONS.md`](LIMITATIONS.md)):
- Full classification of all reciprocity obstructions across all primitive Apollonian and Bianchi sphere packings;
- Full continuum PDE scaling limit of the $\mathbb{Z}^2$ or $\mathbb{A}_2$ sandpile identity (`STAT-058`);
- General-composite Markov Uniqueness Conjecture (`NT-083`);
- All-depth Markov cluster positivity (proved externally by Lee–Schiffler 2015) and Hurwitz $n \ge 5$ asymptotics.

---

## Maintenance & Licensing

- **Status:** Actively maintained v1.0.0 archival research release. Report findings via GitHub Issues (10-class Build Standard taxonomy).
- **Dual License:** All software, Lean 4 proofs, Rust/C11/Python code, scripts, and studio HTML/JS are licensed under **Apache-2.0** ([`LICENSE-CODE`](LICENSE-CODE)). All prose, white paper, figures, documentation, and verified datasets are licensed under **CC-BY-4.0** ([`LICENSE`](LICENSE)).
