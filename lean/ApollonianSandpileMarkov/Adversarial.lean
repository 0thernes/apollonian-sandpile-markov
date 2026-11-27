-- SPDX-License-Identifier: Apache-2.0
module

public import ApollonianSandpileMarkov.JacobiReciprocity
public import ApollonianSandpileMarkov.ApollonianReciprocity
public import ApollonianSandpileMarkov.SandpileTropical
public import ApollonianSandpileMarkov.MarkovHurwitzCluster

/-!
# Adversarial False-Variant & Hypothesis-Necessity Refutations (`ApollonianSandpileMarkov` v3.0.0)

Explicit machine-checked refutations of ten false strengthenings and dropped-hypothesis variants
across all three pillars (`adv1`–`adv10`). Note that `adv2` and `adv6` are direct corollaries of
`T1e` and `T3e` respectively, and these ten refutations do not establish minimality of every single
hypothesis across all 16 theorems.
-/

namespace ApollonianSandpileMarkov.Adversarial

open ApollonianSandpileMarkov.JacobiReciprocity
open ApollonianSandpileMarkov.ApollonianReciprocity
open ApollonianSandpileMarkov.SandpileTropical
open ApollonianSandpileMarkov.MarkovHurwitzCluster

@[expose] public section

/-- Refutation 1: Local mod-4 / mod-24 congruence alone does NOT forbid squares (`(-4,8,9,9)`
    hits `9 = 3^2`, though HKRS list `3n^2, 6n^2, n^4, 4n^4` obstructions for it). -/
theorem adv1_square_contrast_hits_square :
    ¬ (∀ q : Quad, q.descartes = 0 → q.a % 4 = 1 → q.b % 4 = 1 → q.c % 4 = 0 → q.d % 4 = 0 →
       ∀ m : Int, q.a ≠ m * m) := by
  intro hall
  exact hall rootSquareContrast (by decide) (by decide) (by decide) (by decide) (by decide) 3 (by decide)

/-- Refutation 2: No integer linear sphere-inversion multiplier `α : Int` preserves the 4D Soddy–Gosset
    quadratic form `soddyQ 4` (direct corollary of `T1e`). -/
theorem adv2_4d_soddy_not_integral :
    ¬ (∃ α : Int, ∀ (b : Fin 6 → Int) (k : Fin 6), soddyQ 4 (soddyRefl 4 α k b) = soddyQ 4 b) := by
  intro h
  have h23 := (soddy_general_d_integrality_dichotomy 4 (by decide)).mp h
  omega

/-- Refutation 3: On `ℤ²`, odd constant Laplacian `3` IS achievable (contrasting the `𝔸₂`
    even-Laplacian parity lemma `T2d`). -/
theorem adv3_z2_allows_odd_constant_laplacian :
    ¬ (∀ u : Int → Int → Int, (∀ x y, lapZ2 u x y = lapZ2 u 0 0) → lapZ2 u 0 0 % 2 = 0) := by
  intro hall
  have h3 := fun x y => (t2c_lps_z2_superharmonic_and_isotropic_obstruction.2 x y).2.1
  have hconst : ∀ x y, lapZ2 uZ2_lap3a x y = lapZ2 uZ2_lap3a 0 0 := fun x y => by
    rw [h3 x y, h3 0 0]
  have hev := hall uZ2_lap3a hconst
  rw [h3 0 0] at hev
  omega

/-- Refutation 4: Even Markov numbers are NOT all `≡ 2 (mod 64)` (Zhang's mod-32 theorem is
    sharp mod 64 because `(34, 13, 1)` is in the Markov tree with `34 % 64 = 34 ≠ 2`). -/
theorem adv4_even_markov_not_mod64 :
    ¬ (∀ x y z : Int, InMarkovTree x y z → x % 2 = 0 → x % 64 = 2) := by
  intro hall
  have hbad := hall 34 13 1 markov_tree_34_13_1 (by decide)
  omega

/-- Refutation 5: `√(-1)` uniqueness up to sign fails for composite odd moduli (`65 = 5 * 13`
    has four roots `±8, ±18` of `r^2 ≡ -1 (mod 65)`). -/
theorem adv5_composite_modulus_four_roots_of_neg1 :
    ¬ (∀ n : Nat, 1 ≤ n → n % 2 = 1 → ∀ r1 r2 : Int,
        (n : Int) ∣ (r1 * r1 + 1) → (n : Int) ∣ (r2 * r2 + 1) →
        (n : Int) ∣ (r1 - r2) ∨ (n : Int) ∣ (r1 + r2)) := by
  intro hall
  have hbad := hall 65 (by decide) (by decide) 8 18 ⟨1, by decide⟩ ⟨5, by decide⟩
  rcases hbad with ⟨k, hk⟩ | ⟨k, hk⟩ <;> omega

/-- Refutation 6: Hurwitz `n = 4` has no positive solution for `a = 3` (corollary of `T3e`). -/
theorem adv6_hurwitz4_no_a3_solution : ¬ (∃ x1 x2 x3 x4 : Nat, IsHurwitz4 3 x1 x2 x3 x4) := by
  rintro ⟨x1, x2, x3, x4, h⟩
  exact t3e_markov_hurwitz_n4_complete_classification.2.1 3 x1 x2 x3 x4 (Or.inr (Or.inl rfl)) h

/-- Refutation 7 (`T2d` hypothesis necessity): Dropping the mean-curvature equality
    `M * K = 4 * A - 2 * B + 4 * C` in `T2d` allows odd upper bounds such as `K = 5`
    (witnessed by `u(x, y) = x^2`, `M = 1`, `A = 1`, `ψ = 0`, where `lapA2 u x y = 4 ≤ 5`). -/
theorem adv7_t2d_mean_equation_necessary :
    ¬ (∀ (M A B C D E K : Int) (Px Py : Nat) (u ψ : Int → Int → Int),
        1 ≤ M → IsPeriodic2D Px Py ψ →
        (∀ x y, M * u x y = A * x * x + B * x * y + C * y * y + D * x + E * y + ψ x y) →
        (∀ x y, lapA2 u x y ≤ K) → K % 2 = 0) := by
  intro hall
  have h5 := hall 1 1 0 0 0 0 5 1 1 (fun x _ => x * x) (fun _ _ => 0)
    (by decide)
    ⟨by decide, by decide, fun _ _ => rfl, fun _ _ => rfl⟩
    (fun x y => by grind)
    (fun x y => by unfold lapA2; grind)
  omega

/-- Refutation 8 (`T2a` hypothesis necessity): Dropping `LegalTrace G L s` in the Discrete Least
    Action principle breaks the odometer upper bound `countFin L i ≤ w i` (witnessed on
    `gridGraph 2` with zero configuration `s = 0`, stabilizing odometer `w = 0`, and illegal
    toppling list `L = [0]`). -/
theorem adv8_t2a_legal_trace_necessary :
    ¬ (∀ {n : Nat} (G : SandpileGraph n) (L : List (Fin n)) (s : Config n) (w : Fin n → Nat),
        IsStabilizingOdometer G s w → ∀ i, countFin L i ≤ w i) := by
  intro hall
  have hw : IsStabilizingOdometer (gridGraph 2) (fun _ => 0) (fun _ => 0) := by
    intro i
    have hsum : sumFin (fun j : Fin 4 => ((gridGraph 2).adj j i : Int) * ((0 : Nat) : Int)) = 0 := by
      have heq : (fun j : Fin 4 => ((gridGraph 2).adj j i : Int) * ((0 : Nat) : Int)) = (fun _ => 0) := by
        funext j; simp
      rw [heq]
      exact sumFin_zero
    rw [hsum]
    simp [gridGraph]
  have hle := hall (gridGraph 2) [0] (fun _ => 0) (fun _ => 0) hw 0
  simp [countFin] at hle

/-- Refutation 9 (`T1d` hypothesis necessity): Satisfying `IsOctahedral` alone (without
    `HasOctMod8Pattern`) does NOT forbid squares `m^2` or twice-squares `2 * m^2`, as
    witnessed by the strip root `octRootStrip = (0, 0, 1, 2, 2, 1)` hitting `1 = 1^2` and
    `2 = 2 * 1^2`. -/
theorem adv9_octahedral_strip_hits_square_and_double_square :
    ¬ (∀ x : OctSext, IsOctahedral x →
        ∀ m : Int, x.b3 ≠ m * m ∧ x.b4 ≠ 2 * m * m) := by
  intro hall
  have hbad := hall octRootStrip ⟨by decide, by decide, by decide⟩ 1
  exact hbad.1 (by decide)

/-- Conservative 2-vertex dissipative sandpile graph with no absorbing sink (`deg = 1`, `adj 0 1 = 1`). -/
def sinklessGraph2 : SandpileGraph 2 where
  adj i j := if i = j then 0 else 1
  deg _ := 1
  adj_diag i := by simp
  adj_symm i j := by by_cases h : i = j <;> simp [h, eq_comm]

/-- Refutation 10 (`T2a` termination hypothesis necessity): Dropping `HasReachableSink G` breaks
    existence of stabilization even on a dissipative graph with `deg ≥ 1` everywhere — on
    `sinklessGraph2`, every toppling preserves total chip count `s 0 + s 1 = 2`, while stability
    requires `s' 0 ≤ 0 ∧ s' 1 ≤ 0`. -/
theorem adv10_t2a_sink_reachability_necessary :
    ¬ (∀ {n : Nat} (G : SandpileGraph n), IsDissipative G → ∀ s : Config n,
        ∃ L : List (Fin n), LegalTrace G L s ∧ IsStable G (toppleList G L s)) := by
  intro hall
  have hdiss : IsDissipative sinklessGraph2 := fun i => by revert i; decide
  rcases hall sinklessGraph2 hdiss (fun _ => 1) with ⟨L, _, hstab⟩
  have hcons : ∀ (M : List (Fin 2)) (s : Config 2),
      toppleList sinklessGraph2 M s 0 + toppleList sinklessGraph2 M s 1 = s 0 + s 1 := by
    intro M
    induction M with
    | nil => intro _; rfl
    | cons u us ih =>
      intro s
      simp only [toppleList, ih]
      have hu : u = 0 ∨ u = 1 := by
        rcases u with ⟨v, hv⟩
        have hc : v = 0 ∨ v = 1 := by omega
        rcases hc with rfl | rfl
        · left; rfl
        · right; rfl
      rcases hu with rfl | rfl <;> simp [topple, sinklessGraph2] <;> omega
  have hsum := hcons L (fun _ => 1)
  have h0 : toppleList sinklessGraph2 L (fun _ => 1) 0 < 1 := hstab 0
  have h1 : toppleList sinklessGraph2 L (fun _ => 1) 1 < 1 := hstab 1
  omega

theorem all_adversarial_refutations :
    (¬ (∀ q : Quad, q.descartes = 0 → q.a % 4 = 1 → q.b % 4 = 1 → q.c % 4 = 0 → q.d % 4 = 0 →
        ∀ m : Int, q.a ≠ m * m)) ∧
    (¬ (∃ α : Int, ∀ (b : Fin 6 → Int) (k : Fin 6), soddyQ 4 (soddyRefl 4 α k b) = soddyQ 4 b)) ∧
    (¬ (∀ u : Int → Int → Int, (∀ x y, lapZ2 u x y = lapZ2 u 0 0) → lapZ2 u 0 0 % 2 = 0)) ∧
    (¬ (∀ x y z : Int, InMarkovTree x y z → x % 2 = 0 → x % 64 = 2)) ∧
    (¬ (∀ n : Nat, 1 ≤ n → n % 2 = 1 → ∀ r1 r2 : Int,
        (n : Int) ∣ (r1 * r1 + 1) → (n : Int) ∣ (r2 * r2 + 1) →
        (n : Int) ∣ (r1 - r2) ∨ (n : Int) ∣ (r1 + r2))) ∧
    (¬ (∃ x1 x2 x3 x4 : Nat, IsHurwitz4 3 x1 x2 x3 x4)) ∧
    (¬ (∀ (M A B C D E K : Int) (Px Py : Nat) (u ψ : Int → Int → Int),
        1 ≤ M → IsPeriodic2D Px Py ψ →
        (∀ x y, M * u x y = A * x * x + B * x * y + C * y * y + D * x + E * y + ψ x y) →
        (∀ x y, lapA2 u x y ≤ K) → K % 2 = 0)) ∧
    (¬ (∀ {n : Nat} (G : SandpileGraph n) (L : List (Fin n)) (s : Config n) (w : Fin n → Nat),
        IsStabilizingOdometer G s w → ∀ i, countFin L i ≤ w i)) ∧
    (¬ (∀ x : OctSext, IsOctahedral x →
        ∀ m : Int, x.b3 ≠ m * m ∧ x.b4 ≠ 2 * m * m)) ∧
    (¬ (∀ {n : Nat} (G : SandpileGraph n), IsDissipative G → ∀ s : Config n,
        ∃ L : List (Fin n), LegalTrace G L s ∧ IsStable G (toppleList G L s))) :=
  ⟨adv1_square_contrast_hits_square, adv2_4d_soddy_not_integral,
   adv3_z2_allows_odd_constant_laplacian, adv4_even_markov_not_mod64,
   adv5_composite_modulus_four_roots_of_neg1, adv6_hurwitz4_no_a3_solution,
   adv7_t2d_mean_equation_necessary, adv8_t2a_legal_trace_necessary,
   adv9_octahedral_strip_hits_square_and_double_square,
   adv10_t2a_sink_reachability_necessary⟩

end

end ApollonianSandpileMarkov.Adversarial
