<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Limitations & Falsification Criteria (`LIMITATIONS.md`, v1.0.0, corrected 2026-11-26)

## Scope Boundaries

1. **Mostly known results.** The 15 statements (`T1a`–`T3e`) are kernel-checked, but most formalize known results: HKRS (Ann. of Math. 2024) for three packings (`T1c`), Zhang (Acta Arith. 2007) for the mod-32 theorem (`T3b`), Hurwitz (1907) for `n = 4` (`T3e`), Dhar (1990) and the least action principle (`T2a`), Fricke and Cohn (1955) (`T3a`), and classical reciprocity (`T1b`, `T3c`). The only statement with no prior statement found is `T2d`, an elementary parity lemma. The project does not prove the Apollonian local-global classification, the `STAT-058` scaling limit, or the Markov uniqueness conjecture (`NT-083`), and no theorem is a bounded case of these problems.
2. **Narrower than the theorem names.** Several Lean declaration names are broader than their statements; the names are kept so that the comparator contract is unchanged:
   - `T1d` is mod-8 residue locking on one octahedral orbit. Nothing is shown about squares at `b3`–`b6` or twice-squares at `b1, b2, b4, b5`, and no reciprocity argument is formalized. Reciprocity obstructions for octahedral packings were given in arXiv:2510.21702 (Shi, Shi, Whitehead, Williams-Tracy, Zhang, 2025).
   - `T2a` has no sink condition and no termination theorem; it gives uniqueness of legal stabilizing traces, not existence of stabilization.
   - `T2b` does not state the 9×9 determinant `det(L_{3×3}) = 100,352`; it proves a block similarity whose block determinants multiply to that value. No Matrix–Tree or sandpile-group-order link is formalized, and the identity configurations are not proved to be group identities.
   - `T2c` covers one isotropic quadratic, not the Levine–Pegden–Smart classification.
   - `T2d` requires the Laplacian bound `K` to equal the mean curvature `(4A - 2B + 4C)/M`; it says nothing about height-5 sandpile configurations or the A2 sandpile identity.
   - `T2e` is an edge-normal closure identity for lattice polygons; the Kalinin–Shkolnikov theorem is not formalized.
   - `T3b` is stated for tree triples from `(1,1,1)`; that every positive Markov triple lies in the tree is not formalized.
   - `T3d` follows one mutation path of depth five. Lean states positivity of values at positive integers; positivity of Laurent coefficients holds by inspection of the subtraction-free definitions but is not a theorem. All-depth positivity (Lee–Schiffler 2015) is not formalized.
   - `T3e` classifies the admissible coefficients `a` with parity constraints; the orbit description of all solutions is not part of the exported statement.
3. **Contrast packings.** `(-4,8,9,9)` is only shown to contain the square 9. HKRS list quadratic (`3n^2`, `6n^2`) and quartic (`n^4`, `4n^4`) obstructions for it, so it is not an unobstructed packing. Mod-24 residue-set comparisons are computational, not Lean statements.
4. **Finite cutoffs in computational audits.** BFS orbit counts (`≤ 1000`, `≤ 1500`), Markov tree enumeration (`≤ 10^7`) and Hurwitz `n=4` tables (`≤ 120`) are finite checks. They corroborate the Lean statements on finite ranges and do not replace proofs.
5. **Kernel replay coverage.** `leanchecker` and `leanchecker-paranoid` replay the `Solution` and `PalomarSolution` modules. `nanoda_bin`, `con-leche` and `con-ron` check an export of three root declarations and their dependency closure. `lake comparator --paranoid` compares the 16 targets in `lean/comparator.json` with `PalomarChallenge.lean`. The 2026-11-26 audit did not re-run this replay locally; it relies on CI run 45849166650.
6. **Comparator stubs.** `lean/PalomarChallenge.lean` contains 16 intentional `by sorry` stubs (the challenge side of the comparator). Built modules contain none. The `sorry_count: 0` field in `lean/formalization.yaml` refers to built modules.
7. **Local C11 execution vs. CI.** On Windows hosts without GCC/Clang on PATH, the ISO C11 verifier and fuzzer run only in Ubuntu GitHub Actions CI under `-fsanitize=address,undefined`; Rust and Python run on both Ubuntu and Windows.
8. **Review status.** The three internal hardening cycles were automated and internal. An independent statement audit (2026-11-26) found the corrections recorded in [`ERRATA.md`](ERRATA.md). No journal peer review has taken place.

## What Would Prove Us Wrong (Concrete Falsification Criteria)

Any of the following reproducible findings would falsify a claim and would be recorded in `ERRATA.md`:

1. **Kernel / axiom failure:** any of the kernels run in CI (`lean 4.35.0`, `leanchecker`, `lean4lean`, `nanoda_bin`, `con-leche`, `con-ron`) rejecting the checked modules or export, or `lake comparator --paranoid` reporting a statement mismatch or an axiom beyond `[propext, Classical.choice, Quot.sound]`.
2. **HKRS / octahedral counterexample:** an integer quadruple reachable from `(-3,5,8,8)`, `(-7,17,12,20)` or `(-11,21,24,28)` containing a curvature `m^2`, or an octahedral sextuple reachable from `(-6,10,17,40,24,17)` breaking the mod-8 pattern `(2,2,1,0,0,1)`.
3. **A2 odd-Laplacian counterexample:** an integer function `u : ℤ² → ℤ`, `M ≥ 1`, quadratic form `(A,B,C,D,E)` and doubly periodic `ψ` with `Δ_{A2} u ≤ 5` and `5M = 4A - 2B + 4C`.
4. **Even Markov mod-32 violation:** a Markov triple generated from `(1,1,1)` with an even entry `x ≢ 2 (mod 32)`, or an odd prime divisor `p ≡ 3 (mod 4)`.
5. **Cluster identity failure:** integers `(x1,x2,x3)` with `P1 * P4 ≠ x1^4 x2^2 x3^2 P2^2 + P3^2` or `P2 * P5 ≠ x1^6 x2^4 x3^2 P3^2 + P4^2`, or a positive integer solution of the `n=4` Hurwitz equation with `a ∈ {2,3}` or `a ≥ 5`.
6. **Differential / memory-safety failure:** a discrepancy between Rust, ISO C11 and Python outputs on shared inputs, or an ASan/UBSan violation in `native/asm_verify.c` or `native/fuzz_asm.c`.
