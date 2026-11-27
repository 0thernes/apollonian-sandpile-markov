<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# ADR 0002: Direct Zero-Mathlib `detMat 9` Determinants, Statement-Audit Remediation & Exhaustive `Lean.collectAxioms` Auditing

- **Status:** Accepted (`v2.0.0`–`v2.1.0`, 2026-11-26)
- **Context:** In `v1.0.0`, `T2b` established the `3×3` $\mathbb{Z}^2$ grid determinant (`100,352`) via a `D_4` integer block similarity rather than directly evaluating $\det(L_{\mathbb{Z}^2,3\times 3})$, while the triangular-lattice $\mathbb{A}_2$ determinants (`1,092`, `5,393,920`) and Dhar traces lived only in Rust/Python/C11. Additionally, an independent 2026-11-26 statement audit flagged 13 manuscript/attribution items and 9 formal-code items (recorded in `ERRATA.md`), and Cycle 1 of the `v2.1.0` hardening audit identified the need to verify axioms exhaustively across *every* declaration in `ApollonianSandpileMarkov.*` (not just the 19 headline exports).
- **Decision:**
  1. Implement a self-contained zero-Mathlib inductive Laplace determinant `detMat` with machine-checked elementary row-operation soundness (`SandpileTropical.lean`), directly proving `detMat 9 (gridLap 3) = 100352` in `T2b` and adding **`T2f` (`t2f_a2_grid_orders_and_dhar_identity`)** proving `detMat 9 (a2GridLap 3) = 5393920`, `det4 = 1092`, Klein-4 block similarity, and legal `A_2` Dhar traces.
  2. Resolve all 13 paper/attribution items (Zhang 2007, Shi et al. 2025, Hurwitz 1907, Cohn `B_0`, `plainurl` clickable DOIs) and all 9 formal-code items (all 5 3D Soddy preservations in `T1e`, `3 ∣ tr` in `T3a`, `rootSquareContrast`, expanded `NonVacuity.lean`, 9 refutations in `Adversarial.lean`) while keeping existing `PalomarChallenge` theorem names intact for comparator continuity.
  3. Add `lean/VerifyAllDecls.lean`, a Lean 4.35.0 metaprogram that runs `Lean.collectAxioms` over every declaration under `ApollonianSandpileMarkov.*` (818 declarations) and fails elaboration on any axiom outside `[propext, Classical.choice, Quot.sound]`.
- **Consequences:**
  - Zero external Lean dependencies remain (`lake build` stays fast and clean); all 17 comparator targets and all 818 internal declarations are audited on every CI run.
  - Honest scope boundaries (e.g., no Matrix–Tree theorem or Kalinin–Shkolnikov theorem formalized) are stated explicitly alongside every declaration in code, docs, and manuscript.
