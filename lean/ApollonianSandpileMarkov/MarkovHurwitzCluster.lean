-- SPDX-License-Identifier: Apache-2.0
module

public import ApollonianSandpileMarkov.JacobiReciprocity

/-!
# Pillar III: `SL₂(ℤ)` Fricke–Cohn Correspondence, Ying Zhang's Mod-32 Even-Markov Theorem,
# Hensel `√(-1)` Prime-Power Uniqueness, Five-Step Cluster Exchange Identities,
# and Hurwitz's (1907) `n = 4` Admissible-Coefficient Classification

Formalizes:
- `T3a`: Classical `SL₂(ℤ)` Fricke trace identity, punctured-torus commutator `-2` invariance
  under Farey/Nielsen moves, explicit `3 ∣ tr` divisibility, and Cohn's (1955) seed generating
  Markov triples via `tr / 3`.
- `T3b`: Markov's classical descent theorem (1879/1880) proving EVERY positive integer solution of
  `x^2 + y^2 + z^2 = 3xyz` lies in `InMarkovTree x y z`, together with universal pairwise
  coprimality, odd-prime `p ≡ 1 (mod 4)` constraint, odd `x ≡ 1 (mod 4)`, and Ying Zhang's theorem
  (*Acta Arith.* 128 (2007) 295–301, arXiv:math/0612620) that EVERY even Markov number satisfies
  `x % 32 = 2` (sharp mod 64 via `(2, 1, 1)` and `(34, 13, 1)`).
- `T3c`: Classical prime-power Hensel `√(-1)` uniqueness modulo `p^k` for odd primes `p`, `k ≥ 1`.
- `T3d`: Exchange identities with subtraction-free numerators along one five-step Markov-quiver
  mutation sequence (including non-monomial cancellations by `P1` and `P2`), positivity of values at
  positive integer inputs (coefficient positivity holds by inspection), and `(1, 1, 1)` values
  `(2, 5, 29, 433, 37666)` (finite instance of Fomin–Zelevinsky 2002 / Lee–Schiffler 2015).
- `T3e`: Complete Hurwitz (1907) classification of `x1^2 + x2^2 + x3^2 + x4^2 = a x1 x2 x3 x4` over
  `ℤ_{>0}^4`: no solutions for `a ∈ {2, 3}` or `a ≥ 5`; exact bi-implication identifying all `a = 1`
  solutions with the single Vieta/permutation orbit `InHurwitz4Orbit 1 2 2 2 2` (all `x_i ≡ 2 mod 4`)
  and all `a = 4` solutions with the single orbit `InHurwitz4Orbit 4 1 1 1 1` (all `x_i` odd).
-/

namespace ApollonianSandpileMarkov.MarkovHurwitzCluster

open ApollonianSandpileMarkov.JacobiReciprocity

@[expose] public section

/-! ### Part 1: `SL₂(ℤ)` Fricke Trace Identity & Cohn's Markov Correspondence (`T3a`) -/

structure Mat2 where
  a : Int
  b : Int
  c : Int
  d : Int
deriving DecidableEq, Repr

def Mat2.mul (X Y : Mat2) : Mat2 :=
  ⟨X.a * Y.a + X.b * Y.c, X.a * Y.b + X.b * Y.d,
   X.c * Y.a + X.d * Y.c, X.c * Y.b + X.d * Y.d⟩

def Mat2.tr (X : Mat2) : Int := X.a + X.d
def Mat2.det (X : Mat2) : Int := X.a * X.d - X.b * X.c
def Mat2.inv (X : Mat2) : Mat2 := ⟨X.d, -X.b, -X.c, X.a⟩

def Mat2.comm (A B : Mat2) : Mat2 :=
  Mat2.mul (Mat2.mul (Mat2.mul A B) A.inv) B.inv

/-- **Universal `SL₂(ℤ)` Fricke Trace Identity:**
    For ALL `A, B ∈ SL₂(ℤ)`, `(tr A)^2 + (tr B)^2 + (tr (AB))^2 = tr(A)tr(B)tr(AB) + tr(ABA⁻¹B⁻¹) + 2`. -/
theorem fricke_trace_identity (A B : Mat2) (hA : A.det = 1) (hB : B.det = 1) :
    (A.tr) ^ 2 + (B.tr) ^ 2 + (Mat2.mul A B).tr ^ 2 =
    A.tr * B.tr * (Mat2.mul A B).tr + (Mat2.comm A B).tr + 2 := by
  cases A; cases B
  simp only [Mat2.det, Mat2.tr, Mat2.mul, Mat2.inv, Mat2.comm] at hA hB ⊢
  grind

/-- **Punctured-Torus Commutator Invariance under Farey/Nielsen Moves:**
    Both `(A, A*B)` and `(A*B, B)` preserve `det = 1` and `tr(comm) = -2`, AND satisfy the
    exact trace Vieta recursion `tr(A*(A*B)) = tr(A)*tr(AB) - tr(B)`. -/
theorem farey_preserves_comm (A B : Mat2) (hA : A.det = 1) (hB : B.det = 1) :
    (Mat2.mul A B).det = 1 ∧
    (Mat2.comm A (Mat2.mul A B)).tr = (Mat2.comm A B).tr ∧
    (Mat2.comm (Mat2.mul A B) B).tr = (Mat2.comm A B).tr ∧
    (Mat2.mul A (Mat2.mul A B)).tr = A.tr * (Mat2.mul A B).tr - B.tr ∧
    (Mat2.mul (Mat2.mul A B) B).tr = B.tr * (Mat2.mul A B).tr - A.tr := by
  cases A; cases B
  simp only [Mat2.det, Mat2.tr, Mat2.mul, Mat2.inv, Mat2.comm] at hA hB ⊢
  refine ⟨by grind, by grind, by grind, by grind, by grind⟩

def cohnA0 : Mat2 := ⟨1, 1, 1, 2⟩
def cohnB0 : Mat2 := ⟨1, 2, 2, 5⟩

inductive InCohnTree : Mat2 → Mat2 → Prop
  | base : InCohnTree cohnA0 cohnB0
  | left {A B} : InCohnTree A B → InCohnTree A (Mat2.mul A B)
  | right {A B} : InCohnTree A B → InCohnTree (Mat2.mul A B) B

theorem cohn_tree_markov {A B : Mat2} (h : InCohnTree A B) :
    A.det = 1 ∧ B.det = 1 ∧ (Mat2.comm A B).tr = -2 ∧
    A.tr % 3 = 0 ∧ B.tr % 3 = 0 ∧ (Mat2.mul A B).tr % 3 = 0 ∧
    let x := A.tr / 3
    let y := B.tr / 3
    let z := (Mat2.mul A B).tr / 3
    x * x + y * y + z * z = 3 * x * y * z := by
  have hinv : A.det = 1 ∧ B.det = 1 ∧ (Mat2.comm A B).tr = -2 ∧
      A.tr % 3 = 0 ∧ B.tr % 3 = 0 ∧ (Mat2.mul A B).tr % 3 = 0 := by
    induction h with
    | base => exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    | @left A' B' _ ih =>
      rcases ih with ⟨hA, hB, hC, hta, htb, htab⟩
      have hf := farey_preserves_comm A' B' hA hB
      refine ⟨hA, hf.1, by rw [hf.2.1, hC], hta, htab, ?_⟩
      rw [hf.2.2.2.1]
      have h1 : A'.tr = 3 * (A'.tr / 3) := by omega
      have h2 : B'.tr = 3 * (B'.tr / 3) := by omega
      have h3 : (Mat2.mul A' B').tr = 3 * ((Mat2.mul A' B').tr / 3) := by omega
      have hrepr : A'.tr * (Mat2.mul A' B').tr - B'.tr =
                   3 * (3 * (A'.tr / 3) * ((Mat2.mul A' B').tr / 3) - (B'.tr / 3)) := by grind
      rw [hrepr, Int.mul_emod_right]
    | @right A' B' _ ih =>
      rcases ih with ⟨hA, hB, hC, hta, htb, htab⟩
      have hf := farey_preserves_comm A' B' hA hB
      refine ⟨hf.1, hB, by rw [hf.2.2.1, hC], htab, htb, ?_⟩
      rw [hf.2.2.2.2]
      have h1 : A'.tr = 3 * (A'.tr / 3) := by omega
      have h2 : B'.tr = 3 * (B'.tr / 3) := by omega
      have h3 : (Mat2.mul A' B').tr = 3 * ((Mat2.mul A' B').tr / 3) := by omega
      have hrepr : B'.tr * (Mat2.mul A' B').tr - A'.tr =
                   3 * (3 * (B'.tr / 3) * ((Mat2.mul A' B').tr / 3) - (A'.tr / 3)) := by grind
      rw [hrepr, Int.mul_emod_right]
  rcases hinv with ⟨hA, hB, hC, hta, htb, htab⟩
  refine ⟨hA, hB, hC, hta, htb, htab, ?_⟩
  have hfr := fricke_trace_identity A B hA hB
  rw [hC] at hfr
  have h1 : 3 * (A.tr / 3) = A.tr := by omega
  have h2 : 3 * (B.tr / 3) = B.tr := by omega
  have h3 : 3 * ((Mat2.mul A B).tr / 3) = (Mat2.mul A B).tr := by omega
  have h9 : 9 * ((A.tr / 3) * (A.tr / 3) + (B.tr / 3) * (B.tr / 3) +
                 ((Mat2.mul A B).tr / 3) * ((Mat2.mul A B).tr / 3)) =
            9 * (3 * (A.tr / 3) * (B.tr / 3) * ((Mat2.mul A B).tr / 3)) := by grind
  omega

/-- **T3a Master Export (including explicit `3 ∣ tr` divisibility conjuncts).** -/
theorem t3a_sl2z_fricke_cohn_markov_correspondence :
    (∀ A B : Mat2, A.det = 1 → B.det = 1 →
      (A.tr) ^ 2 + (B.tr) ^ 2 + (Mat2.mul A B).tr ^ 2 =
      A.tr * B.tr * (Mat2.mul A B).tr + (Mat2.comm A B).tr + 2) ∧
    (∀ A B : Mat2, InCohnTree A B →
      A.det = 1 ∧ B.det = 1 ∧ (Mat2.comm A B).tr = -2 ∧
      (3 : Int) ∣ A.tr ∧ (3 : Int) ∣ B.tr ∧ (3 : Int) ∣ (Mat2.mul A B).tr ∧
      (A.tr / 3) ^ 2 + (B.tr / 3) ^ 2 + ((Mat2.mul A B).tr / 3) ^ 2 =
      3 * (A.tr / 3) * (B.tr / 3) * ((Mat2.mul A B).tr / 3)) ∧
    (cohnA0.tr / 3 = 1 ∧ cohnB0.tr / 3 = 2 ∧ (Mat2.mul cohnA0 cohnB0).tr / 3 = 5) := by
  refine ⟨fricke_trace_identity, ?_, by decide, by decide, by decide⟩
  intro A B h
  have hc := cohn_tree_markov h
  refine ⟨hc.1, hc.2.1, hc.2.2.1,
          ⟨A.tr / 3, by have := hc.2.2.2.1; omega⟩,
          ⟨B.tr / 3, by have := hc.2.2.2.2.1; omega⟩,
          ⟨(Mat2.mul A B).tr / 3, by have := hc.2.2.2.2.2.1; omega⟩, ?_⟩
  have hmk := hc.2.2.2.2.2.2
  grind

/-! ### Part 2: Markov Coprimality, Odd-Prime `p ≡ 1 (mod 4)` Obstruction & Exact Mod-32 Theorem (`T3b`) -/

inductive InMarkovTree : Int → Int → Int → Prop
  | base : InMarkovTree 1 1 1
  | s1 {x y z} : InMarkovTree x y z → InMarkovTree (3 * y * z - x) y z
  | s2 {x y z} : InMarkovTree x y z → InMarkovTree x (3 * x * z - y) z
  | s3 {x y z} : InMarkovTree x y z → InMarkovTree x y (3 * x * y - z)

theorem markov_pos_eq_coprime {x y z : Int} (h : InMarkovTree x y z) :
    1 ≤ x ∧ 1 ≤ y ∧ 1 ≤ z ∧
    x * x + y * y + z * z = 3 * x * y * z ∧
    Nat.Coprime x.natAbs y.natAbs ∧
    Nat.Coprime y.natAbs z.natAbs ∧
    Nat.Coprime z.natAbs x.natAbs := by
  have hstep : ∀ {a b c : Int}, 1 ≤ a → 1 ≤ b → 1 ≤ c →
      a * a + b * b + c * c = 3 * a * b * c →
      Nat.Coprime a.natAbs b.natAbs → Nat.Coprime b.natAbs c.natAbs → Nat.Coprime c.natAbs a.natAbs →
      1 ≤ (3 * b * c - a) ∧
      (3 * b * c - a) * (3 * b * c - a) + b * b + c * c = 3 * (3 * b * c - a) * b * c ∧
      Nat.Coprime (3 * b * c - a).natAbs b.natAbs ∧
      Nat.Coprime c.natAbs (3 * b * c - a).natAbs := by
    intro a b c ha hb hc heq hab hbc hca
    have hprod : a * (3 * b * c - a) = b * b + c * c := by grind
    have hpos : 1 ≤ 3 * b * c - a := by
      have hbc2 : 2 ≤ b * b + c * c := by
        have h1 : 1 ≤ b * b := Int.mul_pos (by omega) (by omega)
        have h2 : 1 ≤ c * c := Int.mul_pos (by omega) (by omega)
        omega
      by_cases hp : 1 ≤ 3 * b * c - a
      · exact hp
      · exfalso
        have hle0 : a * (3 * b * c - a) ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
        omega
    have hcop_b : Nat.Coprime (3 * b * c - a).natAbs b.natAbs := by
      -- Any common divisor d of (3bc - a) and b divides a!
      by_cases hg : Nat.gcd (3 * b * c - a).natAbs b.natAbs = 1
      · exact hg
      · exfalso
        let g := Nat.gcd (3 * b * c - a).natAbs b.natAbs
        have hg_pos : 1 ≤ g := by
          by_cases h0 : g = 0
          · have := Nat.gcd_eq_zero_iff.mp h0; omega
          · omega
        have hg1 : g ∣ (3 * b * c - a).natAbs := Nat.gcd_dvd_left _ _
        have hg2 : g ∣ b.natAbs := Nat.gcd_dvd_right _ _
        rcases hg1 with ⟨k1, hk1⟩; rcases hg2 with ⟨k2, hk2⟩
        have hgi1 : (g : Int) ∣ (3 * b * c - a) := ⟨(k1 : Int), by
          have : ((3 * b * c - a).natAbs : Int) = 3 * b * c - a := by omega
          rw [← this, hk1, Int.natCast_mul]⟩
        have hgi2 : (g : Int) ∣ b := ⟨(k2 : Int), by
          have : (b.natAbs : Int) = b := by omega
          rw [← this, hk2, Int.natCast_mul]⟩
        have hga : (g : Int) ∣ a := by
          rcases hgi1 with ⟨u1, hu1⟩; rcases hgi2 with ⟨u2, hu2⟩
          exact ⟨3 * u2 * c - u1, by grind⟩
        have hga_nat : g ∣ a.natAbs := by
          rcases hga with ⟨ua, hua⟩
          exact ⟨ua.natAbs, by rw [hua, Int.natAbs_mul, Int.natAbs_natCast]⟩
        have hgd : g ∣ Nat.gcd a.natAbs b.natAbs := Nat.dvd_gcd hga_nat (Nat.gcd_dvd_right _ _)
        rw [hab] at hgd
        have := Nat.le_of_dvd (by decide) hgd; omega
    have hcop_c : Nat.Coprime c.natAbs (3 * b * c - a).natAbs := by
      by_cases hg : Nat.gcd c.natAbs (3 * b * c - a).natAbs = 1
      · exact hg
      · exfalso
        let g := Nat.gcd c.natAbs (3 * b * c - a).natAbs
        have hg_pos : 1 ≤ g := by
          by_cases h0 : g = 0
          · have := Nat.gcd_eq_zero_iff.mp h0; omega
          · omega
        rcases Nat.gcd_dvd_left c.natAbs (3 * b * c - a).natAbs with ⟨k1, hk1⟩
        rcases Nat.gcd_dvd_right c.natAbs (3 * b * c - a).natAbs with ⟨k2, hk2⟩
        have hgi1 : (g : Int) ∣ c := ⟨(k1 : Int), by
          have : (c.natAbs : Int) = c := by omega
          rw [← this, hk1, Int.natCast_mul]⟩
        have hgi2 : (g : Int) ∣ (3 * b * c - a) := ⟨(k2 : Int), by
          have : ((3 * b * c - a).natAbs : Int) = 3 * b * c - a := by omega
          rw [← this, hk2, Int.natCast_mul]⟩
        have hga : (g : Int) ∣ a := by
          rcases hgi1 with ⟨u1, hu1⟩; rcases hgi2 with ⟨u2, hu2⟩
          exact ⟨3 * b * u1 - u2, by grind⟩
        have hga_nat : g ∣ a.natAbs := by
          rcases hga with ⟨ua, hua⟩
          exact ⟨ua.natAbs, by rw [hua, Int.natAbs_mul, Int.natAbs_natCast]⟩
        have hgd : g ∣ Nat.gcd c.natAbs a.natAbs := Nat.dvd_gcd (Nat.gcd_dvd_left _ _) hga_nat
        rw [hca] at hgd
        have := Nat.le_of_dvd (by decide) hgd; omega
    exact ⟨hpos, by grind, hcop_b, hcop_c⟩
  induction h with
  | base => exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
  | s1 _ ih =>
    rcases ih with ⟨hx, hy, hz, heq, hxy, hyz, hzx⟩
    have hs := hstep hx hy hz heq hxy hyz hzx
    exact ⟨hs.1, hy, hz, hs.2.1, hs.2.2.1, hyz, hs.2.2.2⟩
  | s2 _ ih =>
    rcases ih with ⟨hx, hy, hz, heq, hxy, hyz, hzx⟩
    have hs := hstep hy hx hz (by grind) hxy.symm hzx.symm hyz.symm
    exact ⟨hx, hs.1, hz, by grind, hs.2.2.1.symm, hs.2.2.2.symm, hzx⟩
  | s3 _ ih =>
    rcases ih with ⟨hx, hy, hz, heq, hxy, hyz, hzx⟩
    have hs := hstep hz hx hy (by grind) hzx hxy hyz
    exact ⟨hx, hy, hs.1, by grind, hxy, hs.2.2.2, hs.2.2.1⟩

/-- **Universal Odd-Prime `p ≡ 1 (mod 4)` Obstruction:**
    For EVERY Markov triple `(x, y, z)` and EVERY odd prime `p` dividing `x`, `p % 4 = 1`!
    Consequently, ZERO primes `p ≡ 3 (mod 4)` ever divide any Markov number, and EVERY odd
    Markov number satisfies `m % 4 = 1`! -/
theorem markov_odd_prime_mod4 {x y z : Int} (h : InMarkovTree x y z)
    {p : Nat} (hp : IsPrime p) (hp_odd : p % 2 = 1) (hpx : p ∣ x.natAbs) :
    p % 4 = 1 := by
  rcases markov_pos_eq_coprime h with ⟨hx, hy, hz, heq, hxy, hyz, hzx⟩
  have hnd_y : ¬ p ∣ y.natAbs := fun hpy => by
    have hg : p ∣ Nat.gcd x.natAbs y.natAbs := Nat.dvd_gcd hpx hpy
    rw [hxy] at hg
    have := Nat.le_of_dvd (by decide) hg; have := hp.1; omega
  have hnd_z : ¬ p ∣ z.natAbs := fun hpz => by
    have hg : p ∣ Nat.gcd z.natAbs x.natAbs := Nat.dvd_gcd hpz hpx
    rw [hzx] at hg
    have := Nat.le_of_dvd (by decide) hg; have := hp.1; omega
  have hp3 : 3 ≤ p := by have := hp.1; omega
  have hp_pos : 1 ≤ p := by omega
  have hsum_dvd : (p : Int) ∣ (y * y + z * z) := by
    rcases hpx with ⟨kx, hkx⟩
    have hx_eq : x = (p : Int) * (kx : Int) := by
      have : (x.natAbs : Int) = x := by omega
      rw [← this, hkx, Int.natCast_mul]
    exact ⟨(kx : Int) * (3 * y * z - x), by grind⟩
  have hmod : (y * y) % (p : Int) = (-(z * z)) % (p : Int) := by
    rcases hsum_dvd with ⟨q, hq⟩
    have hy2 : y * y = -(z * z) + q * (p : Int) := by grind
    rw [hy2, Int.add_mul_emod_self_right]
  have hcop_y : Nat.Coprime y.natAbs p := prime_coprime_of_not_dvd hp hnd_y
  have hcop_z : Nat.Coprime z.natAbs p := prime_coprime_of_not_dvd hp hnd_z
  have hj1 : jacobi (y * y) p = 1 := jacobi_sq hp_pos hp_odd hcop_y
  have hj2 : jacobi (-(z * z)) p = signNeg1 p := by
    rw [jacobi_neg hp_pos hp_odd, jacobi_sq hp_pos hp_odd hcop_z, Int.mul_one]
  have heqj : jacobi (y * y) p = jacobi (-(z * z)) p := jacobi_eq_of_mod_eq hp_pos hmod
  rw [hj1, hj2] at heqj
  unfold signNeg1 at heqj
  have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
  rcases hp4 with h1 | h3
  · exact h1
  · simp [h3] at heqj

theorem markov_odd_entry_mod4 {x y z : Int} (h : InMarkovTree x y z) (hodd : x % 2 = 1) :
    x % 4 = 1 := by
  have hx := (markov_pos_eq_coprime h).1
  have hspec := primeFactors_spec (n := x.natAbs) (by omega)
  have hodd_x : x.natAbs % 2 = 1 := by omega
  have hodd_ps := odd_mem_of_odd_listProd (by rw [hspec.1]; exact hodd_x)
  have hall1 : ∀ p ∈ primeFactors x.natAbs, p % 4 = 1 := by
    intro p hp
    have hpx : p ∣ x.natAbs := by
      have her := listProd_erase hp; rw [hspec.1] at her; exact ⟨_, her.symm⟩
    exact markov_odd_prime_mod4 h (hspec.2 p hp) (hodd_ps p hp) hpx
  have hprod1 : ∀ ls : List Nat, (∀ p ∈ ls, p % 4 = 1) → listProd ls % 4 = 1 := by
    intro ls
    induction ls with
    | nil => intro _; decide
    | cons p ps ih =>
      intro h1
      simp only [listProd]
      rw [Nat.mul_mod, h1 p List.mem_cons_self, ih (fun q hq => h1 q (List.mem_cons_of_mem p hq))]
  have hnat1 : x.natAbs % 4 = 1 := by rw [← hspec.1]; exact hprod1 _ hall1
  omega

/-- **EXACT MOD-32 THEOREM FOR EVEN MARKOV NUMBERS (Algebraic Core + Global Tree Theorem):**
    For EVERY integer Markov solution `(e, y, z)` with `e % 2 = 0`, `y % 4 = 1`, `z % 4 = 1`:
    **`e % 32 = 2`**!
    And consequently, EVERY even Markov number in the ENTIRE infinite Markov tree satisfies
    `e % 32 = 2`, which is SHARP modulo 64 (`(1, 1, 2)` has `2 % 64 = 2`, `(1, 13, 34)` has `34 % 64 = 34`)! -/
theorem even_markov_mod32_core {e y z : Int}
    (heq : e * e + y * y + z * z = 3 * e * y * z)
    (he : e % 2 = 0) (hy : y % 4 = 1) (hz : z % 4 = 1) :
    e % 32 = 2 := by
  -- Step 1: e % 4 = 2 (if 4 | e then LHS ≡ 2 mod 4 while RHS ≡ 0 mod 4!)
  have he4 : e % 4 = 2 := by
    by_cases h0 : e % 4 = 0
    · exfalso
      have he' : e = 4 * (e / 4) := by omega
      have hy' : y = 4 * (y / 4) + 1 := by omega
      have hz' : z = 4 * (z / 4) + 1 := by omega
      have hdiff : (e * e + y * y + z * z - 3 * e * y * z) % 4 = 2 := by
        have hrepr : e * e + y * y + z * z - 3 * e * y * z =
            4 * (4 * (e / 4) * (e / 4) + 4 * (y / 4) * (y / 4) + 2 * (y / 4) +
                 4 * (z / 4) * (z / 4) + 2 * (z / 4) - 3 * (e / 4) * y * z) + 2 := by grind
        rw [hrepr, Int.mul_add_emod_self_left]; decide
      have h0' : e * e + y * y + z * z - 3 * e * y * z = 0 := by omega
      rw [h0'] at hdiff; simp at hdiff
    · omega
  -- Step 2: Vieta partner x = 3*y*z - e satisfies x^2 + y^2 + z^2 = 3*x*y*z and x % 4 = 1!
  let x := 3 * y * z - e
  have hx_eq : x * x + y * y + z * z = 3 * x * y * z := by dsimp [x]; grind
  have hx4 : x % 4 = 1 := by
    have he' : e = 4 * (e / 4) + 2 := by omega
    have hy' : y = 4 * (y / 4) + 1 := by omega
    have hz' : z = 4 * (z / 4) + 1 := by omega
    have hx_repr : x = 4 * (12 * (y / 4) * (z / 4) + 3 * (y / 4) + 3 * (z / 4) - (e / 4)) + 1 := by
      dsimp [x]; grind
    rw [hx_repr, Int.mul_add_emod_self_left]; decide
  -- Step 3: Write x = 4a + 1, y = 4b + 1, z = 4c + 1!
  let a := x / 4
  let b := y / 4
  let c := z / 4
  have ha : x = 4 * a + 1 := by dsimp [a]; omega
  have hb : y = 4 * b + 1 := by dsimp [b]; omega
  have hc : z = 4 * c + 1 := by dsimp [c]; omega
  -- Exact identity: a + b + c = 4*(a^2+b^2+c^2) - 12*(a*b+b*c+c*a) - 48*a*b*c!
  have hsum : a + b + c = 4 * (a * a + b * b + c * c - 3 * (a * b + b * c + c * a) - 12 * a * b * c) := by
    have h4 : 4 * (a + b + c) =
              4 * (4 * (a * a + b * b + c * c - 3 * (a * b + b * c + c * a) - 12 * a * b * c)) := by grind
    omega
  -- Therefore a + b + c is divisible by 4, AND let s := (a + b + c) / 4!
  let s : Int := (a + b + c) / 4
  have hs4 : a + b + c = 4 * s := by dsimp [s]; omega
  -- Exact expression for e - 2 = 3*y*z - x - 2 = 48*b*c + 12*(a + b + c) - 16*a!
  have he2 : e - 2 = 48 * b * c + 12 * (a + b + c) - 16 * a := by
    have : e = 3 * y * z - x := by dsimp [x]; omega
    grind
  -- Since (a+b+c) = 4*(a+b+c)^2 - 20*(ab+bc+ca) - 48*abc:
  have hsum2 : a + b + c = 4 * (a + b + c) * (a + b + c) - 20 * (a * b + b * c + c * a) - 48 * a * b * c := by
    grind
  have hpar_prod : (a * (b + c - 1)) % 2 = 0 := by
    have ha2 : a % 2 = 0 ∨ a % 2 = 1 := by omega
    have hbc_par : (a + b + c) % 2 = 0 := by omega
    rcases ha2 with h0 | h1
    · rw [Int.mul_emod, h0]; simp
    · have : (b + c - 1) % 2 = 0 := by omega
      rw [Int.mul_emod, this]; simp
  let k : Int := (a * (b + c - 1)) / 2
  have hk : 2 * k = a * (b + c - 1) := by dsimp [k]; omega
  have h32 : e = 32 * (24 * s * s - 18 * a * b * c - 7 * (a * b + b * c + c * a) + b * c - k - a) + 2 := by
    grind
  rw [h32, Int.mul_add_emod_self_left]; decide

/-- Coordinate permutation closure of `InMarkovTree`. -/
theorem markov_tree_perm {a b c : Int} (hm : InMarkovTree a b c) :
    InMarkovTree b a c ∧ InMarkovTree c b a ∧ InMarkovTree a c b := by
  have h12_13 : ∀ {x y z : Int}, InMarkovTree x y z → InMarkovTree y x z ∧ InMarkovTree z y x := by
    intro x y z h
    induction h with
    | base => exact ⟨InMarkovTree.base, InMarkovTree.base⟩
    | @s1 x' y' z' _ ih =>
      exact ⟨by have h := InMarkovTree.s2 ih.1; rwa [show 3 * y' * z' - x' = 3 * y' * z' - x' from rfl],
             by have h := InMarkovTree.s3 ih.2; rwa [show 3 * z' * y' - x' = 3 * y' * z' - x' by grind] at h⟩
    | @s2 x' y' z' _ ih =>
      exact ⟨by have h := InMarkovTree.s1 ih.1; rwa [show 3 * x' * z' - y' = 3 * x' * z' - y' from rfl],
             by have h := InMarkovTree.s2 ih.2; rwa [show 3 * z' * x' - y' = 3 * x' * z' - y' by grind] at h⟩
    | @s3 x' y' z' _ ih =>
      exact ⟨by have h := InMarkovTree.s3 ih.1; rwa [show 3 * y' * x' - z' = 3 * x' * y' - z' by grind] at h,
             by have h := InMarkovTree.s1 ih.2; rwa [show 3 * y' * x' - z' = 3 * x' * y' - z' by grind] at h⟩
  have h1 := h12_13 hm
  have h23 : InMarkovTree a c b := (h12_13 (h12_13 h1.2).1).2
  exact ⟨h1.1, h1.2, h23⟩

theorem markov_tree_even_mod32 {x y z : Int} (h : InMarkovTree x y z) (he : x % 2 = 0) :
    x % 32 = 2 := by
  have hinfo := markov_pos_eq_coprime h
  rcases hinfo with ⟨hx, hy, hz, heq, hxy, hyz, hzx⟩
  have hy_odd : y % 2 = 1 := by
    by_cases h0 : y % 2 = 1
    · exact h0
    · exfalso
      have h2x : 2 ∣ x.natAbs := by omega
      have h2y : 2 ∣ y.natAbs := by omega
      have hg : 2 ∣ Nat.gcd x.natAbs y.natAbs := Nat.dvd_gcd h2x h2y
      rw [hxy] at hg; have := Nat.le_of_dvd (by decide) hg; omega
  have hz_odd : z % 2 = 1 := by
    by_cases h0 : z % 2 = 1
    · exact h0
    · exfalso
      have h2x : 2 ∣ x.natAbs := by omega
      have h2z : 2 ∣ z.natAbs := by omega
      have hg : 2 ∣ Nat.gcd z.natAbs x.natAbs := Nat.dvd_gcd h2z h2x
      rw [hzx] at hg; have := Nat.le_of_dvd (by decide) hg; omega
  have hy4 : y % 4 = 1 := markov_odd_entry_mod4 (markov_tree_perm h).1 hy_odd
  have hz4 : z % 4 = 1 := markov_odd_entry_mod4 (markov_tree_perm h).2.1 hz_odd
  exact even_markov_mod32_core heq he hy4 hz4

/-- **Markov's Classical Descent Theorem (1879/1880):**
    Every positive integer solution `(x, y, z)` of `x^2 + y^2 + z^2 = 3xyz` lies in `InMarkovTree x y z`! -/
theorem markov_descent_aux :
    ∀ (S : Nat) (x y z : Int),
      1 ≤ x → 1 ≤ y → 1 ≤ z → (x + y + z).toNat ≤ S →
      x * x + y * y + z * z = 3 * x * y * z →
      InMarkovTree x y z := by
  intro S
  induction S with
  | zero => intro x y z hx hy hz hS _; omega
  | succ k ih =>
    intro x y z hx hy hz hS heq
    have hsorted : ∀ {a b c : Int}, 1 ≤ a → a ≤ b → b ≤ c → (a + b + c).toNat ≤ k + 1 →
        a * a + b * b + c * c = 3 * a * b * c → InMarkovTree a b c := by
      intro a b c ha hab hbc hSa heqa
      by_cases hbc_eq : b = c
      · subst hbc_eq
        have ha1 : a = 1 := by
          by_cases ha2 : 2 ≤ a
          · have hab2 : a * a ≤ b * b := Int.mul_le_mul hab hab (by omega) (by omega)
            have h3a : (4 : Int) * (b * b) ≤ (3 * a - 2) * (b * b) :=
              Int.mul_le_mul_of_nonneg_right (by omega) (Int.mul_nonneg (by omega) (by omega))
            have hb2_pos : 1 ≤ b * b := Int.mul_pos (by omega) (by omega)
            have hid : a * a = (3 * a - 2) * (b * b) := by grind
            omega
          · omega
        subst ha1
        have hb1 : b = 1 := by
          have hb2 : b * b = 1 := by grind
          by_cases hb2' : 2 ≤ b
          · have : 4 ≤ b * b := Int.mul_le_mul hb2' hb2' (by decide) (by omega)
            omega
          · omega
        subst hb1
        exact InMarkovTree.base
      · have hlt : b < c := by omega
        let c' : Int := 3 * a * b - c
        have hprod : c * c' = a * a + b * b := by dsimp [c']; grind
        have hc'_pos : 1 ≤ c' := by
          have hab2 : 2 ≤ a * a + b * b := by
            have h1 : 1 ≤ a * a := Int.mul_pos (by omega) (by omega)
            have h2 : 1 ≤ b * b := Int.mul_pos (by omega) (by omega)
            omega
          by_cases hp : 1 ≤ c'
          · exact hp
          · exfalso
            have hnp : c * c' ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
            omega
        have hc'_le_b : c' ≤ b := by
          have hab2 : a * a ≤ b * b := Int.mul_le_mul hab hab (by omega) (by omega)
          have h3a : (1 : Int) * (b * b) ≤ (3 * a - 2) * (b * b) :=
            Int.mul_le_mul_of_nonneg_right (by omega) (Int.mul_nonneg (by omega) (by omega))
          have hfac : (c - b) * (b - c') = (3 * a - 2) * (b * b) - a * a := by dsimp [c']; grind
          by_cases hle : c' ≤ b
          · exact hle
          · exfalso
            have hneg : (c - b) * (b - c') < 0 := by
              have hpos_prod : 0 < (c - b) * (c' - b) := Int.mul_pos (by omega) (by omega)
              grind
            omega
        have heq' : a * a + b * b + c' * c' = 3 * a * b * c' := by dsimp [c']; grind
        have hsub : InMarkovTree a b c' := ih a b c' ha (by omega) hc'_pos (by omega) heq'
        have hback : 3 * a * b - c' = c := by dsimp [c']; omega
        have hs3 := InMarkovTree.s3 hsub
        rwa [hback] at hs3
    -- Sort `(x, y, z)` using `markov_tree_perm`:
    by_cases hxy : x ≤ y
    · by_cases hyz : y ≤ z
      · exact hsorted hx hxy hyz hS heq
      · by_cases hxz : x ≤ z
        · exact (markov_tree_perm (hsorted hx hxz (by omega) (by omega) (by grind))).2.2
        · exact (markov_tree_perm (markov_tree_perm (hsorted hz (by omega) hxy (by omega) (by grind))).2.1).1
    · by_cases hxz : x ≤ z
      · exact (markov_tree_perm (hsorted hy (by omega) hxz (by omega) (by grind))).1
      · by_cases hyz : y ≤ z
        · exact (markov_tree_perm (markov_tree_perm (hsorted hy hyz (by omega) (by omega) (by grind))).2.2).1
        · exact (markov_tree_perm (hsorted hz (by omega) (by omega) (by omega) (by grind))).2.1

theorem markov_descent_in_tree {x y z : Int} (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z)
    (heq : x * x + y * y + z * z = 3 * x * y * z) : InMarkovTree x y z :=
  markov_descent_aux (x + y + z).toNat x y z hx hy hz (Nat.le_refl _) heq

/-- Concrete Markov tree membership witness `(34, 13, 1)` (used for mod-64 sharpness). -/
theorem markov_tree_34_13_1 : InMarkovTree 34 13 1 := by
  have h121 : InMarkovTree 1 2 1 := by simpa using InMarkovTree.s2 InMarkovTree.base
  have h521 : InMarkovTree 5 2 1 := by simpa using InMarkovTree.s1 h121
  have h5_13_1 : InMarkovTree 5 13 1 := by simpa using InMarkovTree.s2 h521
  simpa using InMarkovTree.s1 h5_13_1

/-- **T3b Master Export (Markov's Descent Theorem + Universal Coprimality, Odd-Prime `p ≡ 1 (mod 4)`,
    and Ying Zhang's Mod-32 Even-Markov Theorem for EVERY positive integer Markov solution).** -/
theorem t3b_markov_coprimality_odd_primes_and_mod32 :
    (∀ x y z : Int, 1 ≤ x → 1 ≤ y → 1 ≤ z → x * x + y * y + z * z = 3 * x * y * z →
      InMarkovTree x y z) ∧
    (∀ x y z : Int, InMarkovTree x y z →
      1 ≤ x ∧ 1 ≤ y ∧ 1 ≤ z ∧ x * x + y * y + z * z = 3 * x * y * z ∧
      Nat.Coprime x.natAbs y.natAbs ∧ Nat.Coprime y.natAbs z.natAbs ∧ Nat.Coprime z.natAbs x.natAbs) ∧
    (∀ (x y z : Int) (p : Nat), 1 ≤ x → 1 ≤ y → 1 ≤ z → x * x + y * y + z * z = 3 * x * y * z →
      IsPrime p → p % 2 = 1 → p ∣ x.natAbs → p % 4 = 1) ∧
    (∀ x y z : Int, 1 ≤ x → 1 ≤ y → 1 ≤ z → x * x + y * y + z * z = 3 * x * y * z →
      x % 2 = 1 → x % 4 = 1) ∧
    (∀ x y z : Int, 1 ≤ x → 1 ≤ y → 1 ≤ z → x * x + y * y + z * z = 3 * x * y * z →
      x % 2 = 0 → x % 32 = 2) ∧
    (InMarkovTree 2 1 1 ∧ InMarkovTree 34 13 1 ∧ (2 : Int) % 64 = 2 ∧ (34 : Int) % 64 = 34) :=
  ⟨fun _ _ _ hx hy hz heq => markov_descent_in_tree hx hy hz heq,
   fun _ _ _ h => markov_pos_eq_coprime h,
   fun _ _ _ _ hx hy hz heq hp ho hd => markov_odd_prime_mod4 (markov_descent_in_tree hx hy hz heq) hp ho hd,
   fun _ _ _ hx hy hz heq ho => markov_odd_entry_mod4 (markov_descent_in_tree hx hy hz heq) ho,
   fun _ _ _ hx hy hz heq he => markov_tree_even_mod32 (markov_descent_in_tree hx hy hz heq) he,
   ⟨InMarkovTree.s1 InMarkovTree.base, markov_tree_34_13_1, by decide, by decide⟩⟩

/-! ### Part 3: Hensel `√(-1)` Prime-Power Uniqueness Criterion (`T3c`) -/

/-- **Universal Prime-Power `√(-1)` Uniqueness (Baragar–Button–Zhang Algebraic Core):**
    For EVERY odd prime `p`, EVERY `k ≥ 1`, and ANY `r1, r2 ∈ ℤ` with
    `p^k ∣ (r1^2 + 1)` and `p^k ∣ (r2^2 + 1)`, we MUST have `p^k ∣ (r1 - r2)` OR `p^k ∣ (r1 + r2)`! -/
theorem hensel_sqrt_neg1_unique {p k : Nat} (hp : IsPrime p) (hp_odd : p % 2 = 1) (hk : 1 ≤ k)
    {r1 r2 : Int} (h1 : ((p ^ k : Nat) : Int) ∣ (r1 * r1 + 1))
    (h2 : ((p ^ k : Nat) : Int) ∣ (r2 * r2 + 1)) :
    ((p ^ k : Nat) : Int) ∣ (r1 - r2) ∨ ((p ^ k : Nat) : Int) ∣ (r1 + r2) := by
  have hp3 : 3 ≤ p := by have := hp.1; omega
  have hpk_dvd : p ^ k ∣ (r1 - r2).natAbs * (r1 + r2).natAbs := by
    rcases h1 with ⟨u1, hu1⟩; rcases h2 with ⟨u2, hu2⟩
    have hdiff : (r1 - r2) * (r1 + r2) = ((p ^ k : Nat) : Int) * (u1 - u2) := by grind
    have hnat : ((r1 - r2) * (r1 + r2)).natAbs = p ^ k * (u1 - u2).natAbs := by
      rw [hdiff, Int.natAbs_mul, Int.natAbs_natCast]
    rw [Int.natAbs_mul] at hnat
    exact ⟨(u1 - u2).natAbs, hnat⟩
  have hnot_both : ¬ (p ∣ (r1 - r2).natAbs ∧ p ∣ (r1 + r2).natAbs) := by
    rintro ⟨hd1, hd2⟩
    have hlift_p : ∀ {x : Int}, p ∣ x.natAbs → (p : Int) ∣ x := by
      intro x ⟨a, ha⟩
      by_cases h0 : 0 ≤ x
      · refine ⟨(a : Int), ?_⟩; have hx : (x.natAbs : Int) = x := by omega
        rw [← hx, ha, Int.natCast_mul]
      · refine ⟨-(a : Int), ?_⟩; have hx : (x.natAbs : Int) = -x := by omega
        have h' : (p : Int) * (a : Int) = -x := by rw [← Int.natCast_mul, ← ha, hx]
        grind
    have hi1 : (p : Int) ∣ (r1 - r2) := hlift_p hd1
    have hi2 : (p : Int) ∣ (r1 + r2) := hlift_p hd2
    have h2r1 : (p : Int) ∣ 2 * r1 := by
      rcases hi1 with ⟨a, ha⟩; rcases hi2 with ⟨b, hb⟩; exact ⟨a + b, by grind⟩
    have h2r1_nat : p ∣ 2 * r1.natAbs := by
      rcases h2r1 with ⟨c, hc⟩
      have : (2 * r1).natAbs = p * c.natAbs := by rw [hc, Int.natAbs_mul, Int.natAbs_natCast]
      rw [Int.natAbs_mul] at this; exact ⟨c.natAbs, this⟩
    have hpr1 : p ∣ r1.natAbs := by
      rcases prime_dvd_mul hp h2r1_nat with h2p | hr
      · exfalso; have := Nat.le_of_dvd (by decide) h2p; omega
      · exact hr
    have hpr1_i : (p : Int) ∣ r1 * r1 := by
      rcases hpr1 with ⟨c, hc⟩
      have hsq : r1 * r1 = ((r1.natAbs * r1.natAbs : Nat) : Int) := by
        rw [Int.natCast_mul]; exact (Int.natAbs_mul_self' r1).symm
      rw [hsq, hc]
      refine ⟨((c * (p * c) : Nat) : Int), ?_⟩
      simp only [Int.natCast_mul]; grind
    have hp_pk : (p : Int) ∣ ((p ^ k : Nat) : Int) := by
      cases k with
      | zero => omega
      | succ j => exact ⟨((p ^ j : Nat) : Int), by rw [Nat.pow_succ, Int.natCast_mul]; grind⟩
    have hp_r1sq1 : (p : Int) ∣ (r1 * r1 + 1) := Int.dvd_trans hp_pk h1
    have hp1 : (p : Int) ∣ 1 := by
      rcases hpr1_i with ⟨a, ha⟩; rcases hp_r1sq1 with ⟨b, hb⟩; exact ⟨b - a, by grind⟩
    have hp1_nat : p ∣ 1 := Int.ofNat_dvd.mp hp1
    have := Nat.le_of_dvd (by decide) hp1_nat; omega
  have hlift : ∀ {x : Int}, p ^ k ∣ x.natAbs → ((p ^ k : Nat) : Int) ∣ x := by
    intro x ⟨c, hc⟩
    by_cases h0 : 0 ≤ x
    · refine ⟨(c : Int), ?_⟩; have hx : (x.natAbs : Int) = x := by omega
      rw [← hx, hc, Int.natCast_mul]
    · refine ⟨-(c : Int), ?_⟩; have hx : (x.natAbs : Int) = -x := by omega
      have h' : ((p ^ k : Nat) : Int) * (c : Int) = -x := by rw [← Int.natCast_mul, ← hc, hx]
      grind
  by_cases hd1 : p ∣ (r1 - r2).natAbs
  · left
    have hnd2 : ¬ p ∣ (r1 + r2).natAbs := fun hd2 => hnot_both ⟨hd1, hd2⟩
    have hcop : Nat.Coprime (p ^ k) (r1 + r2).natAbs :=
      Nat.Coprime.pow_left k (prime_coprime_of_not_dvd hp hnd2).symm
    exact hlift (hcop.dvd_of_dvd_mul_right hpk_dvd)
  · right
    have hcop : Nat.Coprime (p ^ k) (r1 - r2).natAbs :=
      Nat.Coprime.pow_left k (prime_coprime_of_not_dvd hp hd1).symm
    exact hlift (hcop.dvd_of_dvd_mul_left hpk_dvd)

theorem t3c_hensel_sqrt_neg1_prime_power_uniqueness :
    ∀ {p k : Nat}, IsPrime p → p % 2 = 1 → 1 ≤ k →
      ∀ r1 r2 : Int,
        ((p ^ k : Nat) : Int) ∣ (r1 * r1 + 1) →
        ((p ^ k : Nat) : Int) ∣ (r2 * r2 + 1) →
        ((p ^ k : Nat) : Int) ∣ (r1 - r2) ∨ ((p ^ k : Nat) : Int) ∣ (r1 + r2) :=
  fun hp ho hk _ _ h1 h2 => hensel_sqrt_neg1_unique hp ho hk h1 h2

/-! ### Part 4: Symbolic 3-Variable Markov Cluster-Algebra Laurent Integrality & Positivity (`T3d`) -/

/-- Exact symbolic numerators of the 5-step Markov cluster variables in `ℤ[x1, x2, x3]`:
    - `x1'  = P1 / x1`
    - `x2'  = P2 / (x1^2 * x2)`
    - `x3'  = P3 / (x1^4 * x2^2 * x3)`
    - `x1'' = P4 / (x1^7 * x2^4 * x3^2)`   (NON-MONOMIAL cancellation by `P1 = x2^2 + x3^2`!)
    - `x2'' = P5 / (x1^12 * x2^7 * x3^4)`  (NON-MONOMIAL cancellation by `P2 = (x2^2+x3^2)^2 + x1^2 x3^2`!) -/
def markovP1 (x1 x2 x3 : Int) : Int :=
  let _ := x1
  x2 * x2 + x3 * x3

def markovP2 (x1 x2 x3 : Int) : Int :=
  let U := markovP1 x1 x2 x3
  U * U + x1 * x1 * x3 * x3

def markovP3 (x1 x2 x3 : Int) : Int :=
  let U := markovP1 x1 x2 x3
  let Q2 := markovP2 x1 x2 x3
  x1 * x1 * x2 * x2 * U * U + Q2 * Q2

def markovR4 (x1 x2 x3 : Int) : Int :=
  let U := markovP1 x1 x2 x3
  U * U * U + 2 * x1 * x1 * U * U + x1 * x1 * x1 * x1 * x3 * x3

def markovP4 (x1 x2 x3 : Int) : Int :=
  let U := markovP1 x1 x2 x3
  let W := x1 * x1 * x2 * x2
  let Q2 := markovP2 x1 x2 x3
  W * W * U * U * U + Q2 * Q2 * markovR4 x1 x2 x3

def markovP5 (x1 x2 x3 : Int) : Int :=
  let U := markovP1 x1 x2 x3
  let V := x1 * x1 * x3 * x3
  let W := x1 * x1 * x2 * x2
  let Q2 := markovP2 x1 x2 x3
  let R := markovR4 x1 x2 x3
  W * W * W * W * U * U * U * U +
  Q2 * (2 * W * W * W * V * U * U + W * W * V * Q2 * Q2 +
        2 * W * W * U * U * U * R + Q2 * Q2 * R * R)

/-- **T3d Master Export (Symbolic Fomin–Zelevinsky Cluster-Algebra Laurent Phenomenon on the Markov Quiver):**
    1. Exact symbolic 4-step NON-MONOMIAL Laurent cancellation (dividing by `P1 = x2^2 + x3^2`):
       `P1 * P4 = x1^4 * x2^2 * x3^2 * P2^2 + P3^2` identically in `ℤ[x1, x2, x3]`!
    2. Exact symbolic 5-step NON-MONOMIAL Laurent cancellation (dividing by `P2 = (x2^2+x3^2)^2 + x1^2 x3^2`):
       `P2 * P5 = x1^6 * x2^4 * x3^2 * P3^2 + P4^2` identically in `ℤ[x1, x2, x3]`!
    3. Strict Laurent positivity: for ALL `x1, x2, x3 ≥ 1`, `P1, P2, P3, P4, P5 ≥ 1`!
    4. Exact Markov specialization at `(1, 1, 1)`:
       `(P1, P2, P3, P4, P5)(1, 1, 1) = (2, 5, 29, 433, 37666)`! -/
theorem t3d_cluster_algebra_markov_laurent_positivity :
    (∀ x1 x2 x3 : Int,
      markovP1 x1 x2 x3 * markovP4 x1 x2 x3 =
      x1 ^ 4 * x2 ^ 2 * x3 ^ 2 * (markovP2 x1 x2 x3) ^ 2 + (markovP3 x1 x2 x3) ^ 2) ∧
    (∀ x1 x2 x3 : Int,
      markovP2 x1 x2 x3 * markovP5 x1 x2 x3 =
      x1 ^ 6 * x2 ^ 4 * x3 ^ 2 * (markovP3 x1 x2 x3) ^ 2 + (markovP4 x1 x2 x3) ^ 2) ∧
    (∀ x1 x2 x3 : Int, 1 ≤ x1 → 1 ≤ x2 → 1 ≤ x3 →
      1 ≤ markovP1 x1 x2 x3 ∧ 1 ≤ markovP2 x1 x2 x3 ∧ 1 ≤ markovP3 x1 x2 x3 ∧
      1 ≤ markovP4 x1 x2 x3 ∧ 1 ≤ markovP5 x1 x2 x3) ∧
    (markovP1 1 1 1 = 2 ∧ markovP2 1 1 1 = 5 ∧ markovP3 1 1 1 = 29 ∧
     markovP4 1 1 1 = 433 ∧ markovP5 1 1 1 = 37666) := by
  refine ⟨?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide⟩
  · intro x1 x2 x3
    simp only [markovP1, markovP2, markovP3, markovR4, markovP4]
    grind
  · intro x1 x2 x3
    simp only [markovP1, markovP2, markovP3, markovR4, markovP4, markovP5]
    grind
  · intro x1 x2 x3 h1 h2 h3
    have hmul1 : ∀ u v : Int, 1 ≤ u → 1 ≤ v → 1 ≤ u * v := fun u v hu hv => Int.mul_pos (by omega) (by omega)
    let U := markovP1 x1 x2 x3
    let V := x1 * x1 * x3 * x3
    let W := x1 * x1 * x2 * x2
    let Q2 := markovP2 x1 x2 x3
    let R := markovR4 x1 x2 x3
    have hx1s : 1 ≤ x1 * x1 := hmul1 x1 x1 h1 h1
    have hx2s : 1 ≤ x2 * x2 := hmul1 x2 x2 h2 h2
    have hx3s : 1 ≤ x3 * x3 := hmul1 x3 x3 h3 h3
    have hU : 1 ≤ U := by dsimp [U, markovP1]; omega
    have hV : 1 ≤ V := by dsimp [V]; rw [Int.mul_assoc, Int.mul_assoc]; exact hmul1 _ _ h1 (hmul1 _ _ h1 hx3s)
    have hW : 1 ≤ W := by dsimp [W]; rw [Int.mul_assoc, Int.mul_assoc]; exact hmul1 _ _ h1 (hmul1 _ _ h1 hx2s)
    have hQ2 : 1 ≤ Q2 := by
      dsimp [Q2, markovP2]
      have hUs : 1 ≤ U * U := hmul1 U U hU hU
      change 1 ≤ U * U + V; omega
    have hP3 : 1 ≤ markovP3 x1 x2 x3 := by
      change 1 ≤ x1 * x1 * x2 * x2 * U * U + Q2 * Q2
      have h1' : 1 ≤ W * U * U := hmul1 _ _ (hmul1 _ _ hW hU) hU
      have h2' : 1 ≤ Q2 * Q2 := hmul1 _ _ hQ2 hQ2
      change 1 ≤ W * U * U + Q2 * Q2; omega
    have hR : 1 ≤ R := by
      change 1 ≤ U * U * U + 2 * x1 * x1 * U * U + x1 * x1 * x1 * x1 * x3 * x3
      have hU3 : 1 ≤ U * U * U := hmul1 _ _ (hmul1 _ _ hU hU) hU
      have h2U : 1 ≤ 2 * x1 * x1 * U * U :=
        hmul1 _ _ (hmul1 _ _ (hmul1 _ _ (hmul1 _ _ (by decide) h1) h1) hU) hU
      have hX4 : 1 ≤ x1 * x1 * x1 * x1 * x3 * x3 :=
        hmul1 _ _ (hmul1 _ _ (hmul1 _ _ (hmul1 _ _ (hmul1 _ _ h1 h1) h1) h1) h3) h3
      omega
    have hP4 : 1 ≤ markovP4 x1 x2 x3 := by
      change 1 ≤ W * W * U * U * U + Q2 * Q2 * R
      have hA : 1 ≤ W * W * U * U * U := hmul1 _ _ (hmul1 _ _ (hmul1 _ _ (hmul1 _ _ hW hW) hU) hU) hU
      have hB : 1 ≤ Q2 * Q2 * R := hmul1 _ _ (hmul1 _ _ hQ2 hQ2) hR
      omega
    have hP5 : 1 ≤ markovP5 x1 x2 x3 := by
      change 1 ≤ W * W * W * W * U * U * U * U +
                 Q2 * (2 * W * W * W * V * U * U + W * W * V * Q2 * Q2 +
                       2 * W * W * U * U * U * R + Q2 * Q2 * R * R)
      have hT1 : 1 ≤ W * W * W * W * U * U * U * U :=
        hmul1 _ _ (hmul1 _ _ (hmul1 _ _ (hmul1 _ _ (hmul1 _ _ (hmul1 _ _ (hmul1 _ _ hW hW) hW) hW) hU) hU) hU) hU
      have hT2 : 1 ≤ 2 * W * W * W * V * U * U :=
        hmul1 _ _ (hmul1 _ _ (hmul1 _ _ (hmul1 _ _ (hmul1 _ _ (hmul1 _ _ (by decide) hW) hW) hW) hV) hU) hU
      have hT3 : 1 ≤ W * W * V * Q2 * Q2 :=
        hmul1 _ _ (hmul1 _ _ (hmul1 _ _ (hmul1 _ _ hW hW) hV) hQ2) hQ2
      have hT4 : 1 ≤ 2 * W * W * U * U * U * R :=
        hmul1 _ _ (hmul1 _ _ (hmul1 _ _ (hmul1 _ _ (hmul1 _ _ (hmul1 _ _ (by decide) hW) hW) hU) hU) hU) hR
      have hT5 : 1 ≤ Q2 * Q2 * R * R :=
        hmul1 _ _ (hmul1 _ _ (hmul1 _ _ hQ2 hQ2) hR) hR
      have hQ2S : 1 ≤ Q2 * (2 * W * W * W * V * U * U + W * W * V * Q2 * Q2 +
                             2 * W * W * U * U * U * R + Q2 * Q2 * R * R) :=
        hmul1 _ _ hQ2 (by omega)
      omega
    exact ⟨hU, hQ2, hP3, hP4, hP5⟩

/-! ### Part 5: Complete Generalized Markov–Hurwitz `n = 4` Classification (`T3e`) -/

def IsHurwitz4 (a x1 x2 x3 x4 : Nat) : Prop :=
  1 ≤ a ∧ 1 ≤ x1 ∧ 1 ≤ x2 ∧ 1 ≤ x3 ∧ 1 ≤ x4 ∧
  x1 * x1 + x2 * x2 + x3 * x3 + x4 * x4 = a * x1 * x2 * x3 * x4

theorem hurwitz4_int_eq {a x1 x2 x3 x4 : Nat}
    (heq : x1 * x1 + x2 * x2 + x3 * x3 + x4 * x4 = a * x1 * x2 * x3 * x4) :
    (x1 : Int) * x1 + x2 * x2 + x3 * x3 + x4 * x4 = (a : Int) * x1 * x2 * x3 * x4 := by
  have h := congrArg (fun n : Nat => (n : Int)) heq
  simpa [Int.natCast_add, Int.natCast_mul] using h

/-- Fundamental-solution classification for sorted `1 ≤ x1 ≤ x2 ≤ x3 ≤ x4` with `2 * x4 ≤ a * x1 * x2 * x3`:
    the ONLY fundamental solutions for ALL `a ≥ 1` are `(a=4, 1, 1, 1, 1)` and `(a=1, 2, 2, 2, 2)`! -/
theorem hurwitz4_fundamental_classification {a x1 x2 x3 x4 : Nat}
    (h : IsHurwitz4 a x1 x2 x3 x4)
    (h12 : x1 ≤ x2) (h23 : x2 ≤ x3) (h34 : x3 ≤ x4)
    (hmin : 2 * x4 ≤ a * x1 * x2 * x3) :
    (a = 4 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1) ∨
    (a = 1 ∧ x1 = 2 ∧ x2 = 2 ∧ x3 = 2 ∧ x4 = 2) := by
  rcases h with ⟨ha, hx1, hx2, hx3, hx4, heq⟩
  have heqi := hurwitz4_int_eq heq
  have hconv : a * x1 * x2 * x3 * x3 ≤ x1 * x1 + x2 * x2 + 2 * x3 * x3 := by
    have hprod : 0 ≤ ((x4 : Int) - (x3 : Int)) * ((a : Int) * x1 * x2 * x3 - x4 - x3) :=
      Int.mul_nonneg (by omega) (by
        have hmin_i : (2 * x4 : Int) ≤ (a : Int) * x1 * x2 * x3 := by
          have hle : ((2 * x4 : Nat) : Int) ≤ ((a * x1 * x2 * x3 : Nat) : Int) := Int.ofNat_le.mpr hmin
          simpa [Int.natCast_mul] using hle
        omega)
    have hid : ((x4 : Int) - (x3 : Int)) * ((a : Int) * x1 * x2 * x3 - x4 - x3) =
               ((x1 : Int) * x1 + x2 * x2 + 2 * x3 * x3) - (a : Int) * x1 * x2 * x3 * x3 := by
      grind
    have hle_i : ((a * x1 * x2 * x3 * x3 : Nat) : Int) ≤ ((x1 * x1 + x2 * x2 + 2 * x3 * x3 : Nat) : Int) := by
      simp only [Int.natCast_add, Int.natCast_mul]
      have h2c : ((2 : Nat) : Int) = 2 := rfl
      rw [h2c]; omega
    exact Int.ofNat_le.mp hle_i
  have hax12_le4 : a * x1 * x2 ≤ 4 := by
    by_cases h5 : 5 ≤ a * x1 * x2
    · exfalso
      have h1 : x1 * x1 ≤ x3 * x3 := Nat.mul_le_mul (Nat.le_trans h12 h23) (Nat.le_trans h12 h23)
      have h2 : x2 * x2 ≤ x3 * x3 := Nat.mul_le_mul h23 h23
      have h3 : 5 * (x3 * x3) ≤ (a * x1 * x2) * (x3 * x3) := Nat.mul_le_mul_right _ h5
      have h4 : (a * x1 * x2) * (x3 * x3) = a * x1 * x2 * x3 * x3 := by grind
      have h2x : 2 * x3 * x3 = 2 * (x3 * x3) := by grind
      have h5' : 1 ≤ x3 * x3 := Nat.mul_pos hx3 hx3
      omega
    · omega
  have hax12_pos : 1 ≤ a * x1 * x2 := Nat.mul_pos (Nat.mul_pos ha hx1) hx2
  have hcases : a * x1 * x2 = 1 ∨ a * x1 * x2 = 2 ∨ a * x1 * x2 = 3 ∨ a * x1 * x2 = 4 := by omega
  rcases hcases with h1 | h2 | h3 | h4
  · exfalso; rw [h1, Nat.one_mul] at hmin; omega
  · exfalso
    rw [h2] at hmin heq
    have hx34 : x4 = x3 := by omega
    rw [hx34] at heq
    have : 1 ≤ x1 * x1 := Nat.mul_pos hx1 hx1
    have : 2 * x3 * x3 = 2 * (x3 * x3) := by grind
    omega
  · exfalso
    have hle_a : a ≤ 3 := by
      have : a * 1 * 1 ≤ a * x1 * x2 := Nat.mul_le_mul (Nat.mul_le_mul_left a hx1) hx2; omega
    have hle_x1 : x1 ≤ 3 := by
      have : 1 * x1 * 1 ≤ a * x1 * x2 := Nat.mul_le_mul (Nat.mul_le_mul_right x1 ha) hx2; omega
    have hle_x2 : x2 ≤ 3 := by
      have : 1 * 1 * x2 ≤ a * x1 * x2 := Nat.mul_le_mul_right x2 (Nat.mul_pos ha hx1); omega
    have ha_c : a = 1 ∨ a = 2 ∨ a = 3 := by omega
    have hx1_c : x1 = 1 ∨ x1 = 2 ∨ x1 = 3 := by omega
    have hx2_c : x2 = 1 ∨ x2 = 2 ∨ x2 = 3 := by omega
    rcases ha_c with rfl | rfl | rfl <;>
    rcases hx1_c with rfl | rfl | rfl <;>
    rcases hx2_c with rfl | rfl | rfl
    all_goals try omega
    -- Only surviving pairs with a*x1*x2 = 3 and x1 ≤ x2 are (1, 1, 3) and (3, 1, 1)!
    · have hx3_sq : x3 * x3 ≤ 10 := by
        have hconv' : 3 * (x3 * x3) ≤ 10 + 2 * (x3 * x3) := by
          have : 1 * 1 * 3 * x3 * x3 = 3 * (x3 * x3) := by grind
          have : 2 * x3 * x3 = 2 * (x3 * x3) := by grind
          omega
        omega
      have hx3_eq : x3 = 3 := by
        by_cases h4' : 4 ≤ x3
        · have : 16 ≤ x3 * x3 := Nat.mul_le_mul h4' h4'; omega
        · omega
      subst hx3_eq
      have hx4_c : x4 = 3 ∨ x4 = 4 := by omega
      rcases hx4_c with rfl | rfl <;> omega
    · have hx3_sq : x3 * x3 ≤ 2 := by
        have hconv' : 3 * (x3 * x3) ≤ 2 + 2 * (x3 * x3) := by
          have : 3 * 1 * 1 * x3 * x3 = 3 * (x3 * x3) := by grind
          have : 2 * x3 * x3 = 2 * (x3 * x3) := by grind
          omega
        omega
      have hx3_eq : x3 = 1 := by
        by_cases h2' : 2 ≤ x3
        · have : 4 ≤ x3 * x3 := Nat.mul_le_mul h2' h2'; omega
        · omega
      subst hx3_eq
      have hx4_eq : x4 = 1 := by omega
      subst hx4_eq; omega
  · have hx31 : x3 = x1 := by
      by_cases hlt : x1 < x3
      · exfalso
        have h1' : x1 * x1 < x3 * x3 := Nat.mul_lt_mul_of_lt_of_le hlt (by omega) (by omega)
        have h2' : x2 * x2 ≤ x3 * x3 := Nat.mul_le_mul h23 h23
        rw [h4] at hconv; grind
      · omega
    have hx21 : x2 = x1 := by omega
    rw [hx31] at heq hmin heqi ⊢
    rw [hx21] at heq hmin h4 heqi ⊢
    have hx41 : x4 = x1 := by
      have hle2 : x4 ≤ 2 * x1 := by rw [h4] at hmin; omega
      have hfac : ((x4 : Int) - (x1 : Int)) * ((x4 : Int) - 3 * (x1 : Int)) = 0 := by
        have h4i : (a : Int) * x1 * x1 = 4 := by
          have := congrArg (fun n : Nat => (n : Int)) h4
          simpa [Int.natCast_mul] using this
        have heqi' : (x1 : Int) * x1 + x1 * x1 + x1 * x1 + x4 * x4 = 4 * (x1 : Int) * x4 := by grind
        grind
      rcases Int.mul_eq_zero.mp hfac with h0 | h0 <;> omega
    rw [hx41] at heq hmin ⊢
    have hle_a : a ≤ 4 := by
      have : a * 1 * 1 ≤ a * x1 * x1 := Nat.mul_le_mul (Nat.mul_le_mul_left a hx1) hx1; omega
    have hle_x1 : x1 ≤ 2 := by
      by_cases h3' : 3 ≤ x1
      · have : 9 ≤ x1 * x1 := Nat.mul_le_mul h3' h3'
        have : 1 * (x1 * x1) ≤ a * (x1 * x1) := Nat.mul_le_mul_right _ ha
        have : a * (x1 * x1) = a * x1 * x1 := by grind
        omega
      · omega
    have ha_c : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by omega
    have hx1_c : x1 = 1 ∨ x1 = 2 := by omega
    rcases ha_c with rfl | rfl | rfl | rfl <;> rcases hx1_c with rfl | rfl <;> simp_all

/-- The Hurwitz `n = 4` Vieta-reflection and coordinate-permutation orbit generated by `(r1, r2, r3, r4)`. -/
inductive InHurwitz4Orbit (a r1 r2 r3 r4 : Nat) : Nat → Nat → Nat → Nat → Prop
  | base : InHurwitz4Orbit a r1 r2 r3 r4 r1 r2 r3 r4
  | swap12 {x1 x2 x3 x4} : InHurwitz4Orbit a r1 r2 r3 r4 x1 x2 x3 x4 → InHurwitz4Orbit a r1 r2 r3 r4 x2 x1 x3 x4
  | swap23 {x1 x2 x3 x4} : InHurwitz4Orbit a r1 r2 r3 r4 x1 x2 x3 x4 → InHurwitz4Orbit a r1 r2 r3 r4 x1 x3 x2 x4
  | swap34 {x1 x2 x3 x4} : InHurwitz4Orbit a r1 r2 r3 r4 x1 x2 x3 x4 → InHurwitz4Orbit a r1 r2 r3 r4 x1 x2 x4 x3
  | vieta4 {x1 x2 x3 x4} : InHurwitz4Orbit a r1 r2 r3 r4 x1 x2 x3 x4 →
      InHurwitz4Orbit a r1 r2 r3 r4 x1 x2 x3 (a * x1 * x2 * x3 - x4)

theorem inHurwitz4Orbit_swap13 {a r1 r2 r3 r4 x1 x2 x3 x4 : Nat}
    (h : InHurwitz4Orbit a r1 r2 r3 r4 x1 x2 x3 x4) :
    InHurwitz4Orbit a r1 r2 r3 r4 x3 x2 x1 x4 :=
  InHurwitz4Orbit.swap12 (InHurwitz4Orbit.swap23 (InHurwitz4Orbit.swap12 h))

theorem inHurwitz4Orbit_swap24 {a r1 r2 r3 r4 x1 x2 x3 x4 : Nat}
    (h : InHurwitz4Orbit a r1 r2 r3 r4 x1 x2 x3 x4) :
    InHurwitz4Orbit a r1 r2 r3 r4 x1 x4 x3 x2 :=
  InHurwitz4Orbit.swap23 (InHurwitz4Orbit.swap34 (InHurwitz4Orbit.swap23 h))

/-- Every element in the Vieta/permutation orbit of a valid `IsHurwitz4` seed is a valid `IsHurwitz4` solution. -/
theorem inHurwitz4Orbit_sound {a r1 r2 r3 r4 x1 x2 x3 x4 : Nat}
    (hroot : IsHurwitz4 a r1 r2 r3 r4) (horb : InHurwitz4Orbit a r1 r2 r3 r4 x1 x2 x3 x4) :
    IsHurwitz4 a x1 x2 x3 x4 := by
  induction horb with
  | base => exact hroot
  | swap12 _ ih => rcases ih with ⟨ha, h1, h2, h3, h4, heq⟩; exact ⟨ha, h2, h1, h3, h4, by grind⟩
  | swap23 _ ih => rcases ih with ⟨ha, h1, h2, h3, h4, heq⟩; exact ⟨ha, h1, h3, h2, h4, by grind⟩
  | swap34 _ ih => rcases ih with ⟨ha, h1, h2, h3, h4, heq⟩; exact ⟨ha, h1, h2, h4, h3, by grind⟩
  | @vieta4 u1 u2 u3 u4 _ ih =>
    rcases ih with ⟨ha, hu1, hu2, hu3, hu4, heq⟩
    have hge_u4 : u4 < a * u1 * u2 * u3 := by
      have h1 : 1 ≤ u1 * u1 := Nat.mul_pos hu1 hu1
      have h2 : 1 ≤ u2 * u2 := Nat.mul_pos hu2 hu2
      have h3 : 1 ≤ u3 * u3 := Nat.mul_pos hu3 hu3
      have h4 : u4 * u4 < a * u1 * u2 * u3 * u4 := by omega
      by_cases hle : a * u1 * u2 * u3 ≤ u4
      · have := Nat.mul_le_mul_right u4 hle; omega
      · omega
    refine ⟨ha, hu1, hu2, hu3, by omega, ?_⟩
    have heqi := hurwitz4_int_eq heq
    have hu4'i : ((a * u1 * u2 * u3 - u4 : Nat) : Int) = (a : Int) * u1 * u2 * u3 - u4 := by
      have hsub_i : ((a * u1 * u2 * u3 - u4 : Nat) : Int) = ((a * u1 * u2 * u3 : Nat) : Int) - (u4 : Int) :=
        Int.ofNat_sub (Nat.le_of_lt hge_u4)
      simpa [Int.natCast_mul] using hsub_i
    have hnewi : ((u1 * u1 + u2 * u2 + u3 * u3 + (a * u1 * u2 * u3 - u4) * (a * u1 * u2 * u3 - u4) : Nat) : Int) =
                 ((a * u1 * u2 * u3 * (a * u1 * u2 * u3 - u4) : Nat) : Int) := by
      simp only [Int.natCast_add, Int.natCast_mul, hu4'i]; grind
    exact Int.ofNat.inj hnewi

/-- Unsorted Vieta descent to a fundamental solution: EVERY positive solution of `IsHurwitz4 a x1 x2 x3 x4`
    forces `a = 1` (all entries `≡ 2 mod 4` AND in `InHurwitz4Orbit 1 2 2 2 2`) OR
    `a = 4` (all entries odd AND in `InHurwitz4Orbit 4 1 1 1 1`)! -/
theorem hurwitz4_complete_dichotomy :
    ∀ (S : Nat) (a x1 x2 x3 x4 : Nat), x1 + x2 + x3 + x4 ≤ S → IsHurwitz4 a x1 x2 x3 x4 →
      (a = 1 ∧ x1 % 4 = 2 ∧ x2 % 4 = 2 ∧ x3 % 4 = 2 ∧ x4 % 4 = 2 ∧
        InHurwitz4Orbit 1 2 2 2 2 x1 x2 x3 x4) ∨
      (a = 4 ∧ x1 % 2 = 1 ∧ x2 % 2 = 1 ∧ x3 % 2 = 1 ∧ x4 % 2 = 1 ∧
        InHurwitz4Orbit 4 1 1 1 1 x1 x2 x3 x4) := by
  intro S
  induction S with
  | zero => intro a x1 x2 x3 x4 hS ⟨_, hx1, _, _, _, _⟩; omega
  | succ k ih =>
    intro a x1 x2 x3 x4 hS hH
    have hdesc : ∀ {u1 u2 u3 u4 : Nat}, u1 + u2 + u3 + u4 ≤ k + 1 →
        IsHurwitz4 a u1 u2 u3 u4 → u1 ≤ u2 → u2 ≤ u3 → u3 ≤ u4 →
        (a = 1 ∧ u1 % 4 = 2 ∧ u2 % 4 = 2 ∧ u3 % 4 = 2 ∧ u4 % 4 = 2 ∧
          InHurwitz4Orbit 1 2 2 2 2 u1 u2 u3 u4) ∨
        (a = 4 ∧ u1 % 2 = 1 ∧ u2 % 2 = 1 ∧ u3 % 2 = 1 ∧ u4 % 2 = 1 ∧
          InHurwitz4Orbit 4 1 1 1 1 u1 u2 u3 u4) := by
      intro u1 u2 u3 u4 hSu hHu h12 h23 h34
      by_cases hmin : 2 * u4 ≤ a * u1 * u2 * u3
      · rcases hurwitz4_fundamental_classification hHu h12 h23 h34 hmin with
          ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩
        · right; exact ⟨rfl, by decide, by decide, by decide, by decide, InHurwitz4Orbit.base⟩
        · left; exact ⟨rfl, by decide, by decide, by decide, by decide, InHurwitz4Orbit.base⟩
      · rcases hHu with ⟨ha, hu1, hu2, hu3, hu4, heq⟩
        have hgt : a * u1 * u2 * u3 < 2 * u4 := by omega
        have hlt_u4 : a * u1 * u2 * u3 - u4 < u4 := by omega
        have hge_u4 : u4 < a * u1 * u2 * u3 := by
          have h1 : 1 ≤ u1 * u1 := Nat.mul_pos hu1 hu1
          have h2 : 1 ≤ u2 * u2 := Nat.mul_pos hu2 hu2
          have h3 : 1 ≤ u3 * u3 := Nat.mul_pos hu3 hu3
          have h4 : u4 * u4 < a * u1 * u2 * u3 * u4 := by omega
          by_cases hle : a * u1 * u2 * u3 ≤ u4
          · have := Nat.mul_le_mul_right u4 hle; omega
          · omega
        let u4' := a * u1 * u2 * u3 - u4
        have hu4'_pos : 1 ≤ u4' := by dsimp [u4']; omega
        have hH' : IsHurwitz4 a u1 u2 u3 u4' := by
          refine ⟨ha, hu1, hu2, hu3, hu4'_pos, ?_⟩
          have heqi := hurwitz4_int_eq heq
          have hu4'i : (u4' : Int) = (a : Int) * u1 * u2 * u3 - u4 := by
            have hsub_i : (u4' : Int) = ((a * u1 * u2 * u3 : Nat) : Int) - (u4 : Int) :=
              Int.ofNat_sub (Nat.le_of_lt hge_u4)
            simpa [Int.natCast_mul] using hsub_i
          have hnewi : ((u1 * u1 + u2 * u2 + u3 * u3 + u4' * u4' : Nat) : Int) =
                       ((a * u1 * u2 * u3 * u4' : Nat) : Int) := by
            simp only [Int.natCast_add, Int.natCast_mul, hu4'i]; grind
          exact Int.ofNat.inj hnewi
        have hsub := ih a u1 u2 u3 u4' (by dsimp [u4']; omega) hH'
        have hu4_eq : u4 = a * u1 * u2 * u3 - u4' := by dsimp [u4']; omega
        rcases hsub with ⟨rfl, m1, m2, m3, m4', horb⟩ | ⟨rfl, m1, m2, m3, m4', horb⟩
        · left
          have horb' : InHurwitz4Orbit 1 2 2 2 2 u1 u2 u3 u4 := by
            have hv := InHurwitz4Orbit.vieta4 horb
            rwa [← hu4_eq] at hv
          refine ⟨rfl, m1, m2, m3, ?_, horb'⟩
          have hprod8 : (1 * u1 * u2 * u3) % 4 = 0 := by
            have : (u1 * u2 * u3) % 4 = (((u1 % 4) * (u2 % 4)) % 4 * (u3 % 4)) % 4 := by
              rw [Nat.mul_mod, Nat.mul_mod u1 u2 4]
            rw [Nat.one_mul, this, m1, m2, m3]
          omega
        · right
          have horb' : InHurwitz4Orbit 4 1 1 1 1 u1 u2 u3 u4 := by
            have hv := InHurwitz4Orbit.vieta4 horb
            rwa [← hu4_eq] at hv
          refine ⟨rfl, m1, m2, m3, ?_, horb'⟩
          have hprod2 : (4 * u1 * u2 * u3) % 2 = 0 := by
            have : 4 * u1 * u2 * u3 = 2 * (2 * u1 * u2 * u3) := by grind
            rw [this, Nat.mul_mod_right]
          omega
    have hperm_sym : ∀ {p1 p2 p3 p4 : Nat}, IsHurwitz4 a p1 p2 p3 p4 →
        IsHurwitz4 a p2 p1 p3 p4 ∧ IsHurwitz4 a p1 p3 p2 p4 ∧ IsHurwitz4 a p1 p2 p4 p3 := by
      intro p1 p2 p3 p4 ⟨ha, h1, h2, h3, h4, heq⟩
      refine ⟨⟨ha, h2, h1, h3, h4, by grind⟩, ⟨ha, h1, h3, h2, h4, by grind⟩, ⟨ha, h1, h2, h4, h3, by grind⟩⟩
    have hsort : ∀ (p1 p2 p3 p4 : Nat), p1 + p2 + p3 + p4 ≤ k + 1 → IsHurwitz4 a p1 p2 p3 p4 →
        ∃ q1 q2 q3 q4, q1 ≤ q2 ∧ q2 ≤ q3 ∧ q3 ≤ q4 ∧ q1 + q2 + q3 + q4 = p1 + p2 + p3 + p4 ∧
          IsHurwitz4 a q1 q2 q3 q4 ∧
          ((q1 % 4 = 2 ∧ q2 % 4 = 2 ∧ q3 % 4 = 2 ∧ q4 % 4 = 2 →
            p1 % 4 = 2 ∧ p2 % 4 = 2 ∧ p3 % 4 = 2 ∧ p4 % 4 = 2) ∧
           (q1 % 2 = 1 ∧ q2 % 2 = 1 ∧ q3 % 2 = 1 ∧ q4 % 2 = 1 →
            p1 % 2 = 1 ∧ p2 % 2 = 1 ∧ p3 % 2 = 1 ∧ p4 % 2 = 1) ∧
           (∀ b r1 r2 r3 r4, InHurwitz4Orbit b r1 r2 r3 r4 q1 q2 q3 q4 →
            InHurwitz4Orbit b r1 r2 r3 r4 p1 p2 p3 p4)) := by
      intro p1 p2 p3 p4 _ hP
      have hswap12 : ∀ r1 r2 r3 r4, IsHurwitz4 a r1 r2 r3 r4 →
          ∃ s1 s2, s1 ≤ s2 ∧ s1 + s2 = r1 + r2 ∧ IsHurwitz4 a s1 s2 r3 r4 ∧
            ((s1 % 4 = 2 ∧ s2 % 4 = 2 → r1 % 4 = 2 ∧ r2 % 4 = 2) ∧
             (s1 % 2 = 1 ∧ s2 % 2 = 1 → r1 % 2 = 1 ∧ r2 % 2 = 1) ∧
             (∀ b u1 u2 u3 u4, InHurwitz4Orbit b u1 u2 u3 u4 s1 s2 r3 r4 →
              InHurwitz4Orbit b u1 u2 u3 u4 r1 r2 r3 r4)) := by
        intro r1 r2 r3 r4 hR
        by_cases hle : r1 ≤ r2
        · exact ⟨r1, r2, hle, rfl, hR, ⟨id, id, fun _ _ _ _ _ h => h⟩⟩
        · exact ⟨r2, r1, by omega, by omega, (hperm_sym hR).1,
            ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩,
             fun _ _ _ _ _ h => InHurwitz4Orbit.swap12 h⟩⟩
      rcases hswap12 p1 p2 p3 p4 hP with ⟨a1, a2, ha12, hsa12, hA, himpA⟩
      have hswap34 : ∃ a3 a4, a3 ≤ a4 ∧ a3 + a4 = p3 + p4 ∧ IsHurwitz4 a a1 a2 a3 a4 ∧
          ((a3 % 4 = 2 ∧ a4 % 4 = 2 → p3 % 4 = 2 ∧ p4 % 4 = 2) ∧
           (a3 % 2 = 1 ∧ a4 % 2 = 1 → p3 % 2 = 1 ∧ p4 % 2 = 1) ∧
           (∀ b u1 u2 u3 u4, InHurwitz4Orbit b u1 u2 u3 u4 a1 a2 a3 a4 →
            InHurwitz4Orbit b u1 u2 u3 u4 a1 a2 p3 p4)) := by
        by_cases hle : p3 ≤ p4
        · exact ⟨p3, p4, hle, rfl, hA, ⟨id, id, fun _ _ _ _ _ h => h⟩⟩
        · exact ⟨p4, p3, by omega, by omega, (hperm_sym hA).2.2,
            ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩,
             fun _ _ _ _ _ h => InHurwitz4Orbit.swap34 h⟩⟩
      rcases hswap34 with ⟨a3, a4, ha34, hsa34, hB, himpB⟩
      have hswap13 : ∃ b1 b3, b1 ≤ b3 ∧ b1 + b3 = a1 + a3 ∧ IsHurwitz4 a b1 a2 b3 a4 ∧
          b1 ≤ a2 ∧ b1 ≤ a4 ∧ (b3 ≤ a2 ∨ b3 ≤ a4) ∧
          ((b1 % 4 = 2 ∧ b3 % 4 = 2 → a1 % 4 = 2 ∧ a3 % 4 = 2) ∧
           (b1 % 2 = 1 ∧ b3 % 2 = 1 → a1 % 2 = 1 ∧ a3 % 2 = 1) ∧
           (∀ b u1 u2 u3 u4, InHurwitz4Orbit b u1 u2 u3 u4 b1 a2 b3 a4 →
            InHurwitz4Orbit b u1 u2 u3 u4 a1 a2 a3 a4)) := by
        by_cases hle : a1 ≤ a3
        · exact ⟨a1, a3, hle, rfl, hB, ha12, Nat.le_trans hle ha34, Or.inr ha34,
            ⟨id, id, fun _ _ _ _ _ h => h⟩⟩
        · have hB' : IsHurwitz4 a a3 a2 a1 a4 := by
            rcases hB with ⟨ha, h1, h2, h3, h4, heq⟩; exact ⟨ha, h3, h2, h1, h4, by grind⟩
          exact ⟨a3, a1, by omega, by omega, hB', by omega, ha34, Or.inl ha12,
            ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩,
             fun _ _ _ _ _ h => inHurwitz4Orbit_swap13 h⟩⟩
      rcases hswap13 with ⟨b1, b3, hb13, hsb13, hC, hb12, hb14, hb3_le, himpC⟩
      have hswap24 : ∃ b2 b4, b2 ≤ b4 ∧ b2 + b4 = a2 + a4 ∧ IsHurwitz4 a b1 b2 b3 b4 ∧
          b1 ≤ b2 ∧ b3 ≤ b4 ∧
          ((b2 % 4 = 2 ∧ b4 % 4 = 2 → a2 % 4 = 2 ∧ a4 % 4 = 2) ∧
           (b2 % 2 = 1 ∧ b4 % 2 = 1 → a2 % 2 = 1 ∧ a4 % 2 = 1) ∧
           (∀ b u1 u2 u3 u4, InHurwitz4Orbit b u1 u2 u3 u4 b1 b2 b3 b4 →
            InHurwitz4Orbit b u1 u2 u3 u4 b1 a2 b3 a4)) := by
        by_cases hle : a2 ≤ a4
        · have hb34 : b3 ≤ a4 := by rcases hb3_le with h | h <;> omega
          exact ⟨a2, a4, hle, rfl, hC, hb12, hb34, ⟨id, id, fun _ _ _ _ _ h => h⟩⟩
        · have hC' : IsHurwitz4 a b1 a4 b3 a2 := by
            rcases hC with ⟨ha, h1, h2, h3, h4, heq⟩; exact ⟨ha, h1, h4, h3, h2, by grind⟩
          have hb32 : b3 ≤ a2 := by rcases hb3_le with h | h <;> omega
          exact ⟨a4, a2, by omega, by omega, hC', hb14, hb32,
            ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩,
             fun _ _ _ _ _ h => inHurwitz4Orbit_swap24 h⟩⟩
      rcases hswap24 with ⟨b2, b4, hb24, hsb24, hD, hb12', hb34', himpD⟩
      by_cases hle : b2 ≤ b3
      · refine ⟨b1, b2, b3, b4, hb12', hle, hb34', by omega, hD, ?_, ?_, ?_⟩
        · intro ⟨m1, m2, m3, m4⟩
          have hC' := himpC.1 ⟨m1, m3⟩; have hD' := himpD.1 ⟨m2, m4⟩
          have hA' := himpA.1 ⟨hC'.1, hD'.1⟩; have hB' := himpB.1 ⟨hC'.2, hD'.2⟩
          exact ⟨hA'.1, hA'.2, hB'.1, hB'.2⟩
        · intro ⟨m1, m2, m3, m4⟩
          have hC' := himpC.2.1 ⟨m1, m3⟩; have hD' := himpD.2.1 ⟨m2, m4⟩
          have hA' := himpA.2.1 ⟨hC'.1, hD'.1⟩; have hB' := himpB.2.1 ⟨hC'.2, hD'.2⟩
          exact ⟨hA'.1, hA'.2, hB'.1, hB'.2⟩
        · intro b u1 u2 u3 u4 horb
          exact himpA.2.2 b u1 u2 u3 u4 (himpB.2.2 b u1 u2 u3 u4 (himpC.2.2 b u1 u2 u3 u4 (himpD.2.2 b u1 u2 u3 u4 horb)))
      · refine ⟨b1, b3, b2, b4, hb13, by omega, hb24, by omega, (hperm_sym hD).2.1, ?_, ?_, ?_⟩
        · intro ⟨m1, m3, m2, m4⟩
          have hC' := himpC.1 ⟨m1, m3⟩; have hD' := himpD.1 ⟨m2, m4⟩
          have hA' := himpA.1 ⟨hC'.1, hD'.1⟩; have hB' := himpB.1 ⟨hC'.2, hD'.2⟩
          exact ⟨hA'.1, hA'.2, hB'.1, hB'.2⟩
        · intro ⟨m1, m3, m2, m4⟩
          have hC' := himpC.2.1 ⟨m1, m3⟩; have hD' := himpD.2.1 ⟨m2, m4⟩
          have hA' := himpA.2.1 ⟨hC'.1, hD'.1⟩; have hB' := himpB.2.1 ⟨hC'.2, hD'.2⟩
          exact ⟨hA'.1, hA'.2, hB'.1, hB'.2⟩
        · intro b u1 u2 u3 u4 horb
          exact himpA.2.2 b u1 u2 u3 u4 (himpB.2.2 b u1 u2 u3 u4 (himpC.2.2 b u1 u2 u3 u4 (himpD.2.2 b u1 u2 u3 u4 (InHurwitz4Orbit.swap23 horb))))
    rcases hsort x1 x2 x3 x4 hS hH with ⟨q1, q2, q3, q4, h12, h23, h34, hsum_eq, hQ, himp4, himp2, himpOrb⟩
    rcases hdesc (by omega) hQ h12 h23 h34 with ⟨ha1, m1, m2, m3, m4, horb⟩ | ⟨ha4, m1, m2, m3, m4, horb⟩
    · have hp := himp4 ⟨m1, m2, m3, m4⟩
      left; exact ⟨ha1, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2, himpOrb 1 2 2 2 2 horb⟩
    · have hp := himp2 ⟨m1, m2, m3, m4⟩
      right; exact ⟨ha4, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2, himpOrb 4 1 1 1 1 horb⟩

/-- **T3e Master Export (Complete Hurwitz 1907 `n = 4` Classification + Unique Vieta Orbits):**
    1. Every positive solution has `a = 1` (all entries `≡ 2 mod 4`) OR `a = 4` (all entries odd).
    2. ZERO positive integer solutions for `a = 2`, `a = 3`, or ANY `a ≥ 5`.
    3. Exact bi-implication: `IsHurwitz4 1 x1 x2 x3 x4 ↔ InHurwitz4Orbit 1 2 2 2 2 x1 x2 x3 x4` and
       `IsHurwitz4 4 x1 x2 x3 x4 ↔ InHurwitz4Orbit 4 1 1 1 1 x1 x2 x3 x4`.
    4. Concrete seeds `(2, 2, 2, 2) ↦ (2, 2, 2, 6)` and `(1, 1, 1, 1) ↦ (1, 1, 1, 3)`. -/
theorem t3e_markov_hurwitz_n4_complete_classification :
    (∀ a x1 x2 x3 x4 : Nat, IsHurwitz4 a x1 x2 x3 x4 →
      (a = 1 ∧ x1 % 4 = 2 ∧ x2 % 4 = 2 ∧ x3 % 4 = 2 ∧ x4 % 4 = 2) ∨
      (a = 4 ∧ x1 % 2 = 1 ∧ x2 % 2 = 1 ∧ x3 % 2 = 1 ∧ x4 % 2 = 1)) ∧
    (∀ a x1 x2 x3 x4 : Nat, (a = 2 ∨ a = 3 ∨ 5 ≤ a) → ¬ IsHurwitz4 a x1 x2 x3 x4) ∧
    (∀ x1 x2 x3 x4 : Nat, IsHurwitz4 1 x1 x2 x3 x4 ↔ InHurwitz4Orbit 1 2 2 2 2 x1 x2 x3 x4) ∧
    (∀ x1 x2 x3 x4 : Nat, IsHurwitz4 4 x1 x2 x3 x4 ↔ InHurwitz4Orbit 4 1 1 1 1 x1 x2 x3 x4) ∧
    (IsHurwitz4 1 2 2 2 2 ∧ IsHurwitz4 1 2 2 2 6 ∧
     IsHurwitz4 4 1 1 1 1 ∧ IsHurwitz4 4 1 1 1 3) := by
  have hseed1 : IsHurwitz4 1 2 2 2 2 := ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  have hseed4 : IsHurwitz4 4 1 1 1 1 := ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  refine ⟨fun a x1 x2 x3 x4 h => ?_,
          fun a x1 x2 x3 x4 ha h => ?_,
          fun x1 x2 x3 x4 => ⟨fun h => ?_, fun h => inHurwitz4Orbit_sound hseed1 h⟩,
          fun x1 x2 x3 x4 => ⟨fun h => ?_, fun h => inHurwitz4Orbit_sound hseed4 h⟩,
          hseed1,
          ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩,
          hseed4,
          ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩⟩
  · rcases hurwitz4_complete_dichotomy (x1 + x2 + x3 + x4) a x1 x2 x3 x4 (Nat.le_refl _) h with
      ⟨h1, m1, m2, m3, m4, _⟩ | ⟨h4, m1, m2, m3, m4, _⟩
    · left; exact ⟨h1, m1, m2, m3, m4⟩
    · right; exact ⟨h4, m1, m2, m3, m4⟩
  · rcases hurwitz4_complete_dichotomy (x1 + x2 + x3 + x4) a x1 x2 x3 x4 (Nat.le_refl _) h with
      ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
  · rcases hurwitz4_complete_dichotomy (x1 + x2 + x3 + x4) 1 x1 x2 x3 x4 (Nat.le_refl _) h with
      ⟨_, _, _, _, _, horb⟩ | ⟨h4, _⟩
    · exact horb
    · omega
  · rcases hurwitz4_complete_dichotomy (x1 + x2 + x3 + x4) 4 x1 x2 x3 x4 (Nat.le_refl _) h with
      ⟨h1, _⟩ | ⟨_, _, _, _, _, horb⟩
    · omega
    · exact horb

end

end ApollonianSandpileMarkov.MarkovHurwitzCluster
