-- SPDX-License-Identifier: Apache-2.0
module

public import ApollonianSandpileMarkov.JacobiReciprocity
public import ApollonianSandpileMarkov.ApollonianReciprocity
public import ApollonianSandpileMarkov.SandpileTropical
public import ApollonianSandpileMarkov.MarkovHurwitzCluster

/-!
# Non-Vacuity Witnesses (`ApollonianSandpileMarkov` v2.0.0)

Explicit constructive witnesses proving that every hypothesis predicate appearing in `T1a`–`T3e`
and `T2f` — including the joint `T2d` hypothesis bundle and `IsStabilizingOdometer` — is
non-vacuously inhabited on concrete mathematical objects.
-/

namespace ApollonianSandpileMarkov.NonVacuity

open ApollonianSandpileMarkov.JacobiReciprocity
open ApollonianSandpileMarkov.ApollonianReciprocity
open ApollonianSandpileMarkov.SandpileTropical
open ApollonianSandpileMarkov.MarkovHurwitzCluster

@[expose] public section

theorem nonvac_all_hypotheses :
    -- Pillar I: primes, HKRS & square-contrast Apollonian orbits, Octahedral orbits, 3D Soddy
    (IsPrime 3 ∧ IsPrime 5 ∧ IsPrime 7 ∧
     HasHKRSObstruction rootHKRS1 ∧
     InApollonianOrbit rootHKRS1 (refl1 rootHKRS1) ∧
     rootSquareContrast.descartes = 0 ∧
     IsOctahedral octRootObstructed ∧ HasOctMod8Pattern octRootObstructed ∧
     InOctOrbit octRootObstructed (octRefl false false false octRootObstructed) ∧
     soddy3Q (-5) 9 12 13 16 = 0) ∧
    -- Pillar II: finite sandpile graphs (Z^2 and A_2), legal stabilizing traces, stabilizing odometers,
    -- joint T2d hypothesis bundle witness, periodic 2D functions, lattice polygons
    (LegalTrace (gridGraph 2) traceId2x2 (fun i => id2x2 i + id2x2 i) ∧
     IsStable (gridGraph 2) id2x2 ∧
     IsStabilizingOdometer (gridGraph 2) (fun i => id2x2 i + id2x2 i) (countFin traceId2x2) ∧
     LegalTrace (a2GridGraph 3) traceIdA2_3x3 (fun i => idA2_3x3 i + idA2_3x3 i) ∧
     IsStable (a2GridGraph 3) idA2_3x3 ∧
     IsStabilizingOdometer (a2GridGraph 3) (fun i => idA2_3x3 i + idA2_3x3 i) (countFin traceIdA2_3x3) ∧
     IsPeriodic2D 2 2 (fun x y => (x + y) % 2) ∧
     (∃ (M A B C D E K : Int) (Px Py : Nat) (u ψ : Int → Int → Int),
       1 ≤ M ∧ IsPeriodic2D Px Py ψ ∧
       (∀ x y, M * u x y = A * x * x + B * x * y + C * y * y + D * x + E * y + ψ x y) ∧
       M * K = 4 * A - 2 * B + 4 * C ∧ (∀ x y, lapA2 u x y ≤ K)) ∧
     cycleNormals [(0, 0), (1, 0), (0, 1)] ≠ []) ∧
    -- Pillar III: SL2(Z) Cohn tree, Markov tree, odd prime-power roots of -1, Hurwitz n=4 solutions
    (InCohnTree cohnA0 (Mat2.mul cohnA0 cohnB0) ∧
     InMarkovTree 34 13 1 ∧
     ((5 ^ 2 : Nat) : Int) ∣ (7 * 7 + 1) ∧
     IsHurwitz4 1 2 2 2 6 ∧ IsHurwitz4 4 1 1 1 3) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, hkrs_root1_obstructed,
            InApollonianOrbit.s1 InApollonianOrbit.base,
            by decide,
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
  · have hstab_z2 : IsStabilizingOdometer (gridGraph 2) (fun i => id2x2 i + id2x2 i) (countFin traceId2x2) := by
      intro i
      rw [← toppleList_laplacian_identity (gridGraph 2) traceId2x2 (fun j => id2x2 j + id2x2 j) i]
      rw [t2b_dhar_critical_identity_and_grid_orders.2.2.2.2.2.1.2.1]
      exact t2b_dhar_critical_identity_and_grid_orders.2.2.2.2.2.1.2.2.1 i
    have hstab_a2 : IsStabilizingOdometer (a2GridGraph 3) (fun i => idA2_3x3 i + idA2_3x3 i) (countFin traceIdA2_3x3) := by
      intro i
      rw [← toppleList_laplacian_identity (a2GridGraph 3) traceIdA2_3x3 (fun j => idA2_3x3 j + idA2_3x3 j) i]
      rw [t2f_a2_grid_orders_and_dhar_identity.2.2.2.2.2.2.2.1]
      exact t2f_a2_grid_orders_and_dhar_identity.2.2.2.2.2.2.2.2.1 i
    refine ⟨t2b_dhar_critical_identity_and_grid_orders.2.2.2.2.2.1.1,
            t2b_dhar_critical_identity_and_grid_orders.2.2.2.2.2.1.2.2.1,
            hstab_z2,
            t2f_a2_grid_orders_and_dhar_identity.2.2.2.2.2.2.1,
            t2f_a2_grid_orders_and_dhar_identity.2.2.2.2.2.2.2.2.1,
            hstab_a2,
            ⟨by decide, by decide, fun x y => by dsimp; omega, fun x y => by dsimp; omega⟩,
            ⟨1, 1, 0, 0, 0, 0, 4, 1, 1, fun x _ => x * x, fun _ _ => 0,
             by decide, ⟨by decide, by decide, fun _ _ => rfl, fun _ _ => rfl⟩,
             fun x y => by grind, by decide, fun x y => by unfold lapA2; grind⟩,
            by decide⟩
  · refine ⟨InCohnTree.left InCohnTree.base,
            t3b_markov_coprimality_odd_primes_and_mod32.2.2.2.2.2.1,
            ⟨2, by decide⟩,
            ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩,
            ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩⟩

end

end ApollonianSandpileMarkov.NonVacuity
