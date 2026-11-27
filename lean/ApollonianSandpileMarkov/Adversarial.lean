-- SPDX-License-Identifier: Apache-2.0
module

public import ApollonianSandpileMarkov.JacobiReciprocity
public import ApollonianSandpileMarkov.ApollonianReciprocity
public import ApollonianSandpileMarkov.SandpileTropical
public import ApollonianSandpileMarkov.MarkovHurwitzCluster

/-!
# Adversarial False-Variant Refutations (`ApollonianSandpileMarkov` v2.0.0)

Explicit machine-checked refutations of six false strengthenings / boundary variants across
all three pillars (note: `adv6` is a corollary of `T3e`, and these six refutations do not
establish minimality of every hypothesis across all 16 theorems).
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

/-- Refutation 2: `(4 - 1)` does not divide `2`. -/
theorem adv2_4d_soddy_not_integral : ¬ ((4 - 1 : Nat) ∣ 2) := by
  intro h
  have := Nat.le_of_dvd (by decide) h
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
  have h34 := t3b_markov_coprimality_odd_primes_and_mod32.2.2.2.2.2.1
  have hbad := hall 34 13 1 h34 (by decide)
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

theorem all_adversarial_refutations :
    (¬ (∀ q : Quad, q.descartes = 0 → q.a % 4 = 1 → q.b % 4 = 1 → q.c % 4 = 0 → q.d % 4 = 0 →
        ∀ m : Int, q.a ≠ m * m)) ∧
    (¬ ((4 - 1 : Nat) ∣ 2)) ∧
    (¬ (∀ u : Int → Int → Int, (∀ x y, lapZ2 u x y = lapZ2 u 0 0) → lapZ2 u 0 0 % 2 = 0)) ∧
    (¬ (∀ x y z : Int, InMarkovTree x y z → x % 2 = 0 → x % 64 = 2)) ∧
    (¬ (∀ n : Nat, 1 ≤ n → n % 2 = 1 → ∀ r1 r2 : Int,
        (n : Int) ∣ (r1 * r1 + 1) → (n : Int) ∣ (r2 * r2 + 1) →
        (n : Int) ∣ (r1 - r2) ∨ (n : Int) ∣ (r1 + r2))) ∧
    (¬ (∃ x1 x2 x3 x4 : Nat, IsHurwitz4 3 x1 x2 x3 x4)) :=
  ⟨adv1_square_contrast_hits_square, adv2_4d_soddy_not_integral,
   adv3_z2_allows_odd_constant_laplacian, adv4_even_markov_not_mod64,
   adv5_composite_modulus_four_roots_of_neg1, adv6_hurwitz4_no_a3_solution⟩

end

end ApollonianSandpileMarkov.Adversarial
