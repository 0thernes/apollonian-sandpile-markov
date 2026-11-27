<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# ADR 0003: Closing Four Major Formal-Proof Gaps in `v3.0.0` (General `d`-Dim Soddy, Sandpile Termination, Markov Descent, and Complete Hurwitz `n = 4` Vieta Orbits)

- **Status:** Accepted (`v3.0.0`, 2026-11-27)
- **Context:** After resolving all 13 paper items and 9 formal-code items from the 2026-11-26 statement audit (`v2.0.0`) and hardening all tooling/audits (`v2.1.0`), four explicit mathematical scope gaps remained documented in `LIMITATIONS.md` and `ERRATA.md`:
  1. `T1e` stated only the arithmetic divisibility fact `(d - 1) ∣ 2 ↔ d = 2 ∨ d = 3`, without linking it in Lean to general `d`-dimensional Soddy–Gosset reflections.
  2. `T2a` lacked a sink condition and proved only uniqueness of legal stabilizing traces, not finite termination or existence of stabilization.
  3. `T3b` assumed `InMarkovTree x y z` rather than proving Markov's classical descent theorem that every positive integer solution of `x^2 + y^2 + z^2 = 3xyz` lies in the tree.
  4. `T3e` classified only admissible coefficients `a ∈ {1, 4}` and parities, omitting the exact Vieta-orbit description of all positive solutions.
- **Decision:** Upgrade all four theorems in zero-Mathlib Lean 4.35.0 (`Challenge.lean` & `PalomarChallenge.lean`, triggering major SemVer bump **`v3.0.0`**) while preserving every existing theorem name:
  1. **`T1e` (`ApollonianReciprocity.lean`):** Formalize `soddyQ d b` and `soddyRefl d α k b` over `Fin (d + 2) → Int`, prove universal involution, exact change factorization, preservation iff `(d - 1) * α = 2`, and the Lagarias–Mallows–Wilks (2002) dichotomy `∃ α, ∀ b k, soddyQ d (soddyRefl d α k b) = soddyQ d b ↔ d = 2 ∨ d = 3`.
  2. **`T2a` (`SandpileTropical.lean`):** Define `IsDissipative G` and inductive `ReachesSink` / `HasReachableSink G`, build a constructive strictly superharmonic potential `potentialVal R D (dist i)` satisfying `(L g)(i) ≥ 1`, construct an explicit stabilizing odometer `w = M * g`, and prove universal finite trace-length bounds and existence of a legal stabilizing trace via `stabilizeTrace`.
  3. **`T3b` (`MarkovHurwitzCluster.lean`):** Prove `markov_descent_in_tree` by strong induction on `(x + y + z).toNat` using `(c - b)(b - c') = (3a - 2)b^2 - a^2 ≥ 0`, lifting pairwise coprimality, odd-prime `p ≡ 1 (mod 4)`, and Ying Zhang's mod-32 theorem to ALL positive integer Markov solutions.
  4. **`T3e` (`MarkovHurwitzCluster.lean`):** Define `InHurwitz4Orbit` and prove exact bi-implications `IsHurwitz4 1 x1 x2 x3 x4 ↔ InHurwitz4Orbit 1 2 2 2 2 x1 x2 x3 x4` and `IsHurwitz4 4 x1 x2 x3 x4 ↔ InHurwitz4Orbit 4 1 1 1 1 x1 x2 x3 x4`.
  5. **Non-Vacuity & Adversarial Coverage:** Expand `NonVacuity.lean` with sinked-dissipative multi-hop `gridGraph 3`, `soddyQ 3`, and `InHurwitz4Orbit` witnesses, strengthen `adv2_4d_soddy_not_integral` to refute 4D `soddyRefl`, and add `adv10_t2a_sink_reachability_necessary` on a 2-vertex dissipative sinkless graph (`sinklessGraph2`).
- **Consequences:**
  - `VerifyAllDecls.lean` exhaustively audits **884 declarations** (up from 818), all strictly within `[propext, Classical.choice, Quot.sound]`, zero `sorry`, zero `native_decide`, zero Mathlib.
  - Because the types of `T1e`, `T2a`, `T3b`, and `T3e` in `Challenge.lean` are strictly strengthened, the release increments major version to **`v3.0.0`** per Semantic Versioning 2.0.0 (`UPGRADING.md`).
  - Remaining honest boundaries (octahedral global reciprocity in `T1d`, Matrix–Tree theorem in `T2b`/`T2f`, full LPS classification in `T2c`, Kalinin–Shkolnikov theorem in `T2e`, Lee–Schiffler all-depth positivity in `T3d`, and open problems `STAT-058`/`NT-083`) stay explicitly documented in `CLAIMS.md` and `LIMITATIONS.md`.
