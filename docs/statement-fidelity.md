<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Statement Fidelity Audit (`docs/statement-fidelity.md`)

Every headline theorem in `paper/main.tex` is verified below to match its literal formal Lean 4.35.0 proposition in `lean/Challenge.lean` and `lean/PalomarChallenge.lean` with zero hidden weakenings or vacuous hypotheses (certified independently by `NonVacuity.lean` and `Adversarial.lean`).

| Paper Theorem | Lean Proposition (`ApollonianSandpileMarkov.Challenge.*`) | Exact Fidelity Check |
| :--- | :--- | :--- |
| Thm 2.1 (`T1a`) | `T1a_DescartesLorentzianAndGaussianNorm` | Quantifies universally over `q : Quad` and `a b c d x1 y1 x2 y2 : Int`; exact Gaussian norm and Brahmagupta–Descartes BQF identity. |
| Thm 2.2 (`T1b`) | `T1b_JacobiReciprocityMaster` | Quantifies universally over all odd `m, n ≥ 1` and `a, b : Int`; proves both supplementary laws, full Jacobi reciprocity, multiplicativity, and squares=1 without Mathlib. |
| Thm 2.3 (`T1c`) | `T1c_HKRSApollonianReciprocityObstruction` | Quantifies over the full inductive reflection orbit `InApollonianOrbit` of all 3 HKRS roots and all `m : Int`; proves `q.{a,b,c,d} ≠ m * m` with zero GCD side conditions, contrasted with `rootUnobstructed`. |
| Thm 2.4 (`T1d`) | `T1d_OctahedralLorentzianAndSqrtNeg2Obstruction` | Quantifies over all 8 face reflections and the full `InOctOrbit` of `(-6,10,17,40,24,17)`; proves mod-8 locking, square/double-square exclusions, 5 Jacobi witnesses, and strip contrast. |
| Thm 2.5 (`T1e`) | `T1e_SoddyDimensionDichotomyAnd3DContrast` | Exact biconditional `∀ d ≥ 2, (d - 1) ∣ 2 ↔ d = 2 ∨ d = 3`, all 5 3D Soddy involutions, and explicit `25 = 5 * 5` reflection. |
| Thm 3.1 (`T2a`) | `T2a_AbelianSandpileConfluenceAndLeastAction` | Quantifies universally over arbitrary `n : Nat` and arbitrary finite sinked graph `G : SandpileGraph n`. |
| Thm 3.2 (`T2b`) | `T2b_DharCriticalIdentityAndGridOrders` | Exact integer `det4 = 192`, exact integer `Q * (4 Q^{-1}) = 4 I_9` & block diagonalization `100352`, plus exact legal Dhar traces for `2×2` and `3×3`. |
| Sec 3.2 (`T2c`) | `T2c_LPSZ2SuperharmonicAndIsotropicObstruction` | Quantifies universally over all periods `Px Py ≥ 1`, all `u ψ : Int → Int → Int`; proves `4u = 3(x^2+y^2)+ψ` with `lapZ2 u ≤ 3` yields `False`, plus constant Laplacian `2, 3` witnesses. |
| Thm 3.3 (`T2d`) | `T2d_TriangularA2EvenLaplacianRigidityAndObstruction` | Quantifies universally over ALL `M ≥ 1`, ALL `A B C D E K : Int`, ALL periods `Px Py ≥ 1`, ALL `u ψ`; proves `K % 2 = 0`, universally obstructing `K = 5`, plus `K = 4, 2` witnesses. |
| Sec 3.3 (`T2e`) | `T2e_KalininShkolnikovTropicalBalancingAndSolitons` | Quantifies universally over every list `vs : List Vec2` and balanced triples `v1+v2+v3=(0,0)`, plus 2-/3-soliton witnesses. |
| Sec 4.1 (`T3a`) | `T3a_SL2ZFrickeCohnMarkovCorrespondence` | Quantifies universally over all `A B : Mat2` with `det = 1` and the full inductive `InCohnTree`. |
| Thm 4.1 (`T3b`) | `T3b_MarkovCoprimalityOddPrimesAndMod32` | Quantifies universally over the full inductive `InMarkovTree`; proves pairwise coprimality, odd prime `p % 4 = 1`, odd `x % 4 = 1`, **even `x % 32 = 2`**, and sharp mod-64 witnesses `(2,1,1)` & `(34,13,1)`. |
| Sec 4.3 (`T3c`) | `T3c_HenselSqrtNeg1PrimePowerUniqueness` | Quantifies universally over all odd primes `p`, all `k ≥ 1`, and all `r1, r2 : Int`. |
| Thm 4.2 (`T3d`) | `T3d_ClusterAlgebraMarkovLaurentPositivity` | Quantifies universally over all symbolic integers `x1 x2 x3 : Int`, proving BOTH non-monomial polynomial identities `P1*P4 = ...` and `P2*P5 = ...`, strict positivity for `x_i ≥ 1`, and `(1,1,1)` specialization `(2,5,29,433,37666)`. |
| Thm 4.3 (`T3e`) | `T3e_MarkovHurwitzN4CompleteClassification` | Quantifies universally over all `a x1 x2 x3 x4 : Nat`; proves complete classification (`a=1` all `≡ 2 mod 4`, `a=4` all odd, zero solutions for `a ∈ {2,3}` and `a ≥ 5`). |
