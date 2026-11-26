-- SPDX-License-Identifier: Apache-2.0
module

public import ApollonianSandpileMarkov.JacobiReciprocity
public import ApollonianSandpileMarkov.ApollonianReciprocity
public import ApollonianSandpileMarkov.SandpileTropical
public import ApollonianSandpileMarkov.MarkovHurwitzCluster

/-!
# Non-Vacuity Witnesses (`ApollonianSandpileMarkov` v1.0.0)

Explicit constructive witnesses proving that EVERY hypothesis predicate appearing in our
universal theorems (`T1a`–`T3e`) is non-vacuously inhabited on concrete mathematical objects.
-/

namespace ApollonianSandpileMarkov.NonVacuity

open ApollonianSandpileMarkov.JacobiReciprocity
open ApollonianSandpileMarkov.ApollonianReciprocity
open ApollonianSandpileMarkov.SandpileTropical
open ApollonianSandpileMarkov.MarkovHurwitzCluster

@[expose] public section

theorem nonvac_all_hypotheses :
    -- Pillar I: primes, obstructed & unobstructed Apollonian orbits, Octahedral orbits, 3D Soddy
    (IsPrime 3 ∧ IsPrime 5 ∧ IsPrime 7 ∧
     HasHKRSObstruction rootHKRS1 ∧
     InApollonianOrbit rootHKRS1 (refl1 rootHKRS1) ∧
     IsOctahedral octRootObstructed ∧ HasOctMod8Pattern octRootObstructed ∧
     InOctOrbit octRootObstructed (octRefl false false false octRootObstructed) ∧
     soddy3Q (-5) 9 12 13 16 = 0) ∧
    -- Pillar II: finite sandpile graphs, legal stabilizing traces, periodic 2D functions, lattice polygons
    (LegalTrace (gridGraph 2) traceId2x2 (fun i => id2x2 i + id2x2 i) ∧
     IsStable (gridGraph 2) id2x2 ∧
     IsPeriodic2D 2 2 (fun x y => (x + y) % 2) ∧
     cycleNormals [(0, 0), (1, 0), (0, 1)] ≠ []) ∧
    -- Pillar III: SL2(Z) Cohn tree, Markov tree, odd prime-power roots of -1, Hurwitz n=4 solutions
    (InCohnTree cohnA0 (Mat2.mul cohnA0 cohnB0) ∧
     InMarkovTree 34 13 1 ∧
     ((5 ^ 2 : Nat) : Int) ∣ (7 * 7 + 1) ∧
     IsHurwitz4 1 2 2 2 6 ∧ IsHurwitz4 4 1 1 1 3) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, hkrs_root1_obstructed,
            InApollonianOrbit.s1 InApollonianOrbit.base,
            ⟨by decide, by decide, by decide⟩,
            ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩,
            InOctOrbit.step false false false InOctOrbit.base,
            by decide⟩
    · exact ⟨by decide, fun d hd => by
        have hle := Nat.le_of_dvd (by decide) hd
        have hd0 : d ≠ 0 := fun h => by subst h; rcases hd with ⟨k, hk⟩; simp at hk
        have hc : d = 1 ∨ d = 2 ∨ d = 3 := by omega
        rcases hc with rfl | rfl | rfl
        · left; rfl
        · exfalso; rcases hd with ⟨k, hk⟩; omega
        · right; rfl⟩
    · exact ⟨by decide, fun d hd => by
        have hle := Nat.le_of_dvd (by decide) hd
        have hd0 : d ≠ 0 := fun h => by subst h; rcases hd with ⟨k, hk⟩; simp at hk
        have hc : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 := by omega
        rcases hc with rfl | rfl | rfl | rfl | rfl
        · left; rfl
        · exfalso; rcases hd with ⟨k, hk⟩; omega
        · exfalso; rcases hd with ⟨k, hk⟩; omega
        · exfalso; rcases hd with ⟨k, hk⟩; omega
        · right; rfl⟩
    · exact ⟨by decide, fun d hd => by
        have hle := Nat.le_of_dvd (by decide) hd
        have hd0 : d ≠ 0 := fun h => by subst h; rcases hd with ⟨k, hk⟩; simp at hk
        have hc : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 := by omega
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · left; rfl
        · exfalso; rcases hd with ⟨k, hk⟩; omega
        · exfalso; rcases hd with ⟨k, hk⟩; omega
        · exfalso; rcases hd with ⟨k, hk⟩; omega
        · exfalso; rcases hd with ⟨k, hk⟩; omega
        · exfalso; rcases hd with ⟨k, hk⟩; omega
        · right; rfl⟩
  · refine ⟨t2b_dhar_critical_identity_and_grid_orders.2.2.2.2.1.1,
            t2b_dhar_critical_identity_and_grid_orders.2.2.2.2.1.2.2.1,
            ⟨by decide, by decide, fun x y => by dsimp; omega, fun x y => by dsimp; omega⟩,
            by decide⟩
  · refine ⟨InCohnTree.left InCohnTree.base,
            t3b_markov_coprimality_odd_primes_and_mod32.2.2.2.2.2.1,
            ⟨2, by decide⟩,
            ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩,
            ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩⟩

end

end ApollonianSandpileMarkov.NonVacuity
