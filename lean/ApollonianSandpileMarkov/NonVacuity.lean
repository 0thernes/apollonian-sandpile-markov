-- SPDX-License-Identifier: Apache-2.0
module

public import ApollonianSandpileMarkov.JacobiReciprocity
public import ApollonianSandpileMarkov.ApollonianReciprocity
public import ApollonianSandpileMarkov.SandpileTropical
public import ApollonianSandpileMarkov.MarkovHurwitzCluster

/-!
# Non-Vacuity Witnesses (`ApollonianSandpileMarkov` v3.0.0)

Explicit constructive witnesses proving that every hypothesis predicate appearing in `T1a`–`T3e`
and `T2f` — including all three HKRS roots (`rootHKRS1`–`rootHKRS3`), the general `d`-dimensional
Soddy form `soddyQ`, the sinked-dissipative sandpile predicates (`IsDissipative` and multi-hop
`HasReachableSink` on `gridGraph 2`, `gridGraph 3`, and `a2GridGraph 2`), the `ℤ²` superharmonic
premise `lapZ2 u ≤ 3`, the joint `T2d` hypothesis bundle, `IsStabilizingOdometer`, `InHurwitz4Orbit`,
and the `SL₂(ℤ)` Cohn seed determinants — is non-vacuously inhabited on concrete mathematical objects.
-/

namespace ApollonianSandpileMarkov.NonVacuity

open ApollonianSandpileMarkov.JacobiReciprocity
open ApollonianSandpileMarkov.ApollonianReciprocity
open ApollonianSandpileMarkov.SandpileTropical
open ApollonianSandpileMarkov.MarkovHurwitzCluster

@[expose] public section

theorem nonvac_all_hypotheses :
    -- Pillar I: primes, all three HKRS orbits, square-contrast root, Octahedral orbits, general & 3D Soddy
    (IsPrime 3 ∧ IsPrime 5 ∧ IsPrime 7 ∧
     HasHKRSObstruction rootHKRS1 ∧
     HasHKRSObstruction rootHKRS2 ∧
     HasHKRSObstruction rootHKRS3 ∧
     InApollonianOrbit rootHKRS1 (refl1 rootHKRS1) ∧
     InApollonianOrbit rootHKRS2 (refl1 rootHKRS2) ∧
     InApollonianOrbit rootHKRS3 (refl1 rootHKRS3) ∧
     rootSquareContrast.descartes = 0 ∧
     IsOctahedral octRootObstructed ∧ HasOctMod8Pattern octRootObstructed ∧
     InOctOrbit octRootObstructed (octRefl false false false octRootObstructed) ∧
     soddy3Q (-5) 9 12 13 16 = 0 ∧
     soddyQ 3 (fun i => match i.val with | 0 => -5 | 1 => 9 | 2 => 12 | 3 => 13 | _ => 16) = 0) ∧
    -- Pillar II: finite sandpile graphs (Z^2 and A_2), sinked-dissipative graphs (including multi-hop 3x3),
    -- legal stabilizing traces, stabilizing odometers, Z^2 superharmonic premise, joint T2d bundle,
    -- periodic 2D functions, lattice polygons
    (IsDissipative (gridGraph 2) ∧ HasReachableSink (gridGraph 2) ∧
     IsDissipative (gridGraph 3) ∧ HasReachableSink (gridGraph 3) ∧
     IsDissipative (a2GridGraph 2) ∧ HasReachableSink (a2GridGraph 2) ∧
     LegalTrace (gridGraph 2) traceId2x2 (fun i => id2x2 i + id2x2 i) ∧
     IsStable (gridGraph 2) id2x2 ∧
     IsStabilizingOdometer (gridGraph 2) (fun i => id2x2 i + id2x2 i) (countFin traceId2x2) ∧
     LegalTrace (a2GridGraph 3) traceIdA2_3x3 (fun i => idA2_3x3 i + idA2_3x3 i) ∧
     IsStable (a2GridGraph 3) idA2_3x3 ∧
     IsStabilizingOdometer (a2GridGraph 3) (fun i => idA2_3x3 i + idA2_3x3 i) (countFin traceIdA2_3x3) ∧
     IsPeriodic2D 2 2 (fun x y => (x + y) % 2) ∧
     (∀ x y : Int, lapZ2 uZ2_lap3a x y ≤ 3) ∧
     (∃ (M A B C D E K : Int) (Px Py : Nat) (u ψ : Int → Int → Int),
       1 ≤ M ∧ IsPeriodic2D Px Py ψ ∧
       (∀ x y, M * u x y = A * x * x + B * x * y + C * y * y + D * x + E * y + ψ x y) ∧
       M * K = 4 * A - 2 * B + 4 * C ∧ (∀ x y, lapA2 u x y ≤ K)) ∧
     cycleNormals [(0, 0), (1, 0), (0, 1)] ≠ []) ∧
    -- Pillar III: SL2(Z) Cohn seed & tree, Markov tree, odd prime-power roots of -1, Hurwitz n=4 solutions & orbits
    (cohnA0.det = 1 ∧ cohnB0.det = 1 ∧
     InCohnTree cohnA0 (Mat2.mul cohnA0 cohnB0) ∧
     InMarkovTree 34 13 1 ∧
     ((5 ^ 2 : Nat) : Int) ∣ (7 * 7 + 1) ∧
     IsHurwitz4 1 2 2 2 6 ∧ IsHurwitz4 4 1 1 1 3 ∧
     InHurwitz4Orbit 1 2 2 2 2 2 2 2 6 ∧ InHurwitz4Orbit 4 1 1 1 1 1 1 1 3) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, hkrs_root1_obstructed, hkrs_root2_obstructed, hkrs_root3_obstructed,
            InApollonianOrbit.s1 InApollonianOrbit.base,
            InApollonianOrbit.s1 InApollonianOrbit.base,
            InApollonianOrbit.s1 InApollonianOrbit.base,
            by decide,
            ⟨by decide, by decide, by decide⟩,
            ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩,
            InOctOrbit.step false false false InOctOrbit.base,
            by decide,
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
  · have hdiss2 : IsDissipative (gridGraph 2) := fun i => by revert i; decide
    have hsink2 : HasReachableSink (gridGraph 2) := fun i => ⟨0, ReachesSink.base (by revert i; decide)⟩
    have hdiss3 : IsDissipative (gridGraph 3) := fun i => by revert i; decide
    have hsink3 : HasReachableSink (gridGraph 3) := fun i => by
      by_cases h4 : i = 4
      · subst h4; exact ⟨1, ReachesSink.step (j := 1) (by decide) (ReachesSink.base (by decide))⟩
      · exact ⟨0, ReachesSink.base (by revert i h4; decide)⟩
    have hdissA2 : IsDissipative (a2GridGraph 2) := fun i => by revert i; decide
    have hsinkA2 : HasReachableSink (a2GridGraph 2) := fun i => ⟨0, ReachesSink.base (by revert i; decide)⟩
    have hstab_z2 : IsStabilizingOdometer (gridGraph 2) (fun i => id2x2 i + id2x2 i) (countFin traceId2x2) := by
      intro i
      rw [← toppleList_laplacian_identity (gridGraph 2) traceId2x2 (fun j => id2x2 j + id2x2 j) i]
      rw [t2b_dhar_critical_identity_and_grid_orders.2.2.2.2.2.1.2.1]
      exact t2b_dhar_critical_identity_and_grid_orders.2.2.2.2.2.1.2.2.1 i
    have hstab_a2 : IsStabilizingOdometer (a2GridGraph 3) (fun i => idA2_3x3 i + idA2_3x3 i) (countFin traceIdA2_3x3) := by
      intro i
      rw [← toppleList_laplacian_identity (a2GridGraph 3) traceIdA2_3x3 (fun j => idA2_3x3 j + idA2_3x3 j) i]
      rw [t2f_a2_grid_orders_and_dhar_identity.2.2.2.2.2.2.2.1]
      exact t2f_a2_grid_orders_and_dhar_identity.2.2.2.2.2.2.2.2.1 i
    have hlap3 : ∀ x y : Int, lapZ2 uZ2_lap3a x y ≤ 3 := fun x y => by
      rw [(t2c_lps_z2_superharmonic_and_isotropic_obstruction.2 x y).2.1]
      decide
    refine ⟨hdiss2, hsink2, hdiss3, hsink3, hdissA2, hsinkA2,
            t2b_dhar_critical_identity_and_grid_orders.2.2.2.2.2.1.1,
            t2b_dhar_critical_identity_and_grid_orders.2.2.2.2.2.1.2.2.1,
            hstab_z2,
            t2f_a2_grid_orders_and_dhar_identity.2.2.2.2.2.2.1,
            t2f_a2_grid_orders_and_dhar_identity.2.2.2.2.2.2.2.2.1,
            hstab_a2,
            ⟨by decide, by decide, fun x y => by dsimp; omega, fun x y => by dsimp; omega⟩,
            hlap3,
            ⟨1, 1, 0, 0, 0, 0, 4, 1, 1, fun x _ => x * x, fun _ _ => 0,
             by decide, ⟨by decide, by decide, fun _ _ => rfl, fun _ _ => rfl⟩,
             fun x y => by grind, by decide, fun x y => by unfold lapA2; grind⟩,
            by decide⟩
  · refine ⟨by decide, by decide,
            InCohnTree.left InCohnTree.base,
            markov_tree_34_13_1,
            ⟨2, by decide⟩,
            ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩,
            ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩,
            InHurwitz4Orbit.vieta4 InHurwitz4Orbit.base,
            InHurwitz4Orbit.vieta4 InHurwitz4Orbit.base⟩

end

end ApollonianSandpileMarkov.NonVacuity
