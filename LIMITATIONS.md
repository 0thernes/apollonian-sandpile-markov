<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Limitations & Falsification Criteria (`LIMITATIONS.md`, v1.0.0)

## Scope Boundaries

1. **Overarching Conjectures Remain Open:** This project proves 15 concrete structural, obstruction, rigidity, and classification theorems (`T1a`–`T3e`) unconditionally in Lean 4. It does **not** claim proofs of full Apollonian local-global classification, the continuum PDE scaling limit of `STAT-058`, or general-composite Markov Uniqueness (`NT-083`).
2. **Finite Depth vs. Arbitrary Depth in `T3d`:** Theorem `T3d` proves exact symbolic 3-variable Laurent integrality and positivity through 5 mutations (explicitly verifying the first two non-monomial polynomial cancellations by `P1` and `P2`). All-depth positivity for skew-symmetric cluster algebras holds by Lee–Schiffler (2015), whose general proof is not formalized here.
3. **Finite Cutoffs in Computational Audits:** BFS orbit counts (`≤ 1000`, `≤ 1500`), Markov tree uniqueness verification (`≤ 10^7`), and Hurwitz `n=4` exhaustive tables (`≤ 120`) provide independent empirical corroboration beyond the universal Lean theorems; they are not substitutes for universal proofs where those remain open.
4. **Local C11 Execution vs. CI:** On Windows development hosts lacking GCC/Clang on PATH, the ISO C11 verifier and 100k fuzzer run in Ubuntu GitHub Actions CI under `-fsanitize=address,undefined`; Rust and Python run natively on both Ubuntu and Windows.
5. **Independent Review Status:** All 3 hardening cycles and the Playbook v1.3 10-pass review were executed internally with automated formal kernel replay across six independent typecheckers; formal external journal peer review has not yet occurred.

## What Would Prove Us Wrong (Concrete Falsification Criteria)

Any of the following reproducible findings would immediately falsify a core claim and trigger a documented entry in `ERRATA.md`:

1. **Kernel / Axiom Failure:** Any of the 6 independent Lean kernels (`lean 4.35.0`, `leanchecker`, `lean4lean`, `nanoda_bin`, `con-leche`, `con-ron`) rejecting `Solution`/`PalomarSolution`, or `lake comparator --paranoid` reporting a statement mismatch or unpermitted axiom beyond `[propext, Classical.choice, Quot.sound]`.
2. **HKRS / Octahedral Counterexample:** Any integer quadruple reachable from `(-3,5,8,8)`, `(-7,17,12,20)`, or `(-11,21,24,28)` containing a perfect-square curvature `m^2`, or any octahedral sextuple reachable from `(-6,10,17,40,24,17)` breaking the mod-8 pattern `(2,2,1,0,0,1)`.
3. **$\mathbb{A}_2$ Odd-Laplacian Counterexample:** Any integer function `u : ℤ² → ℤ`, denominator `M ≥ 1`, quadratic form `(A,B,C,D,E)`, and doubly periodic remainder `ψ` with `Δ_{A2} u ≤ 5` and mean `5` (`5M = 4A - 2B + 4C`).
4. **Even Markov Mod-32 Violation:** Any Markov triple `(x,y,z)` generated from `(1,1,1)` having an even entry `x ≢ 2 (mod 32)`, or any odd prime divisor `p ≡ 3 (mod 4)`.
5. **Cluster Cancellation Failure:** Any integers `(x1,x2,x3)` for which `P1 * P4 ≠ x1^4 x2^2 x3^2 P2^2 + P3^2` or `P2 * P5 ≠ x1^6 x2^4 x3^2 P3^2 + P4^2`, or Hurwitz `n=4` positive integer solution with `a ∈ {2,3}` or `a ≥ 5`.
6. **Differential / Memory-Safety Failure:** Any discrepancy between Rust, ISO C11, and Python outputs on shared inputs, or any ASan/UBSan violation in `native/asm_verify.c` or `native/fuzz_asm.c`.
