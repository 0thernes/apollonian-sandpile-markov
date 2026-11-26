-- SPDX-License-Identifier: Apache-2.0
module

/-!
# Self-Contained Zero-Mathlib Legendre–Jacobi Symbol & Gauss Quadratic Reciprocity

Proves Fermat's Little Theorem, Euler's Criterion, Gauss's Lemma, the First and Second
Supplementary Laws, Eisenstein's 1844 Lattice-Point Proof of Gauss's Quadratic Reciprocity Law
for all distinct odd primes, and lifts every law to the full Jacobi symbol `jacobi : Int → Nat → Int`
for all odd `n ≥ 1`. Strictly zero Mathlib dependencies, zero `sorry`, zero `native_decide`.
-/

namespace ApollonianSandpileMarkov.JacobiReciprocity

@[expose] public section

/-- Primality predicate on `Nat`. -/
def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

/-- First supplementary sign `(-1)^((n-1)/2)` via `Bool` (avoids `Decidable` motive drift). -/
def signNeg1 (n : Nat) : Int :=
  if n % 4 == 1 then 1 else -1

/-- Second supplementary sign `(-1)^((n^2-1)/8)` via `Bool`. -/
def signTwo (n : Nat) : Int :=
  if n % 8 == 1 || n % 8 == 7 then 1 else -1

/-- Quadratic reciprocity sign `(-1)^(((m-1)/2)*((n-1)/2))` via `Bool`. -/
def signQR (m n : Nat) : Int :=
  if m % 4 == 3 && n % 4 == 3 then -1 else 1

/-- Multiplicative helpers for `signNeg1`, `signTwo`, `signQR` on odd `Nat`s. -/
theorem signNeg1_mul {a b : Nat} (ha : a % 2 = 1) (hb : b % 2 = 1) :
    signNeg1 (a * b) = signNeg1 a * signNeg1 b := by
  unfold signNeg1
  have hmul : (a * b) % 4 = ((a % 4) * (b % 4)) % 4 := Nat.mul_mod a b 4
  rw [hmul]
  have ha4 : a % 4 = 1 ∨ a % 4 = 3 := by omega
  have hb4 : b % 4 = 1 ∨ b % 4 = 3 := by omega
  rcases ha4 with h1 | h1 <;> rcases hb4 with h2 | h2 <;> simp [h1, h2]

theorem signTwo_mul {a b : Nat} (ha : a % 2 = 1) (hb : b % 2 = 1) :
    signTwo (a * b) = signTwo a * signTwo b := by
  unfold signTwo
  have hmul : (a * b) % 8 = ((a % 8) * (b % 8)) % 8 := Nat.mul_mod a b 8
  rw [hmul]
  have ha8 : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by omega
  have hb8 : b % 8 = 1 ∨ b % 8 = 3 ∨ b % 8 = 5 ∨ b % 8 = 7 := by omega
  rcases ha8 with h1 | h1 | h1 | h1 <;> rcases hb8 with h2 | h2 | h2 | h2 <;> simp [h1, h2]

theorem signQR_mul_right {a b c : Nat} (ha : a % 2 = 1) (hb : b % 2 = 1) (hc : c % 2 = 1) :
    signQR a (b * c) = signQR a b * signQR a c := by
  unfold signQR
  have hmul : (b * c) % 4 = ((b % 4) * (c % 4)) % 4 := Nat.mul_mod b c 4
  rw [hmul]
  have ha4 : a % 4 = 1 ∨ a % 4 = 3 := by omega
  have hb4 : b % 4 = 1 ∨ b % 4 = 3 := by omega
  have hc4 : c % 4 = 1 ∨ c % 4 = 3 := by omega
  rcases ha4 with h1 | h1 <;> rcases hb4 with h2 | h2 <;> rcases hc4 with h3 | h3 <;>
    simp [h1, h2, h3]

theorem signQR_mul_left {a b c : Nat} (ha : a % 2 = 1) (hb : b % 2 = 1) (hc : c % 2 = 1) :
    signQR (a * b) c = signQR a c * signQR b c := by
  unfold signQR
  have hmul : (a * b) % 4 = ((a % 4) * (b % 4)) % 4 := Nat.mul_mod a b 4
  rw [hmul]
  have ha4 : a % 4 = 1 ∨ a % 4 = 3 := by omega
  have hb4 : b % 4 = 1 ∨ b % 4 = 3 := by omega
  have hc4 : c % 4 = 1 ∨ c % 4 = 3 := by omega
  rcases ha4 with h1 | h1 <;> rcases hb4 with h2 | h2 <;> rcases hc4 with h3 | h3 <;>
    simp [h1, h2, h3]

/-- Euclid's Lemma from `Nat.gcd`. -/
theorem prime_dvd_mul {p a b : Nat} (hp : IsPrime p) (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  have hg : Nat.gcd p a ∣ p := Nat.gcd_dvd_left p a
  rcases hp.2 (Nat.gcd p a) hg with h1 | hp'
  · right; exact Nat.Coprime.dvd_of_dvd_mul_left h1 h
  · left; rw [← hp']; exact Nat.gcd_dvd_right p a

theorem prime_coprime_of_not_dvd {p a : Nat} (hp : IsPrime p) (hnd : ¬ p ∣ a) :
    Nat.Coprime a p := by
  have hg : Nat.gcd a p ∣ p := Nat.gcd_dvd_right a p
  rcases hp.2 (Nat.gcd a p) hg with h1 | hp'
  · exact h1
  · exfalso; apply hnd; rw [← hp']; exact Nat.gcd_dvd_left a p

theorem prime_not_dvd_of_lt {p a : Nat} (ha0 : 0 < a) (hal : a < p) : ¬ p ∣ a := by
  intro hd
  have hle := Nat.le_of_dvd ha0 hd
  omega

/-- Product of `f 1 * f 2 * ... * f n`. -/
def prodRange (n : Nat) (f : Nat → Nat) : Nat :=
  match n with
  | 0 => 1
  | k + 1 => prodRange k f * f (k + 1)

theorem prodRange_mod_eq (n p : Nat) (f g : Nat → Nat)
    (h : ∀ k, 1 ≤ k → k ≤ n → f k % p = g k % p) :
    prodRange n f % p = prodRange n g % p := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [prodRange]
    rw [Nat.mul_mod, ih (fun j hj1 hjk => h j hj1 (Nat.le_succ_of_le hjk)),
        h (k + 1) (Nat.succ_pos k) (Nat.le_refl _), ← Nat.mul_mod]

theorem prodRange_const_mul (n a : Nat) (f : Nat → Nat) :
    prodRange n (fun k => a * f k) = a ^ n * prodRange n f := by
  induction n with
  | zero => simp [prodRange]
  | succ k ih =>
    simp only [prodRange, ih, Nat.pow_succ]
    grind

theorem prodRange_id_not_dvd {p : Nat} (hp : IsPrime p) :
    ∀ n, n < p → ¬ p ∣ prodRange n (fun k => k) := by
  intro n
  induction n with
  | zero =>
    intro _ hd
    simp only [prodRange] at hd
    have hle := Nat.le_of_dvd (by decide) hd
    have hp2 := hp.1
    omega
  | succ k ih =>
    intro hlt hd
    simp only [prodRange] at hd
    rcases prime_dvd_mul hp hd with h1 | h2
    · exact ih (Nat.lt_of_succ_lt hlt) h1
    · exact prime_not_dvd_of_lt (Nat.succ_pos k) hlt h2

def listProd : List Nat → Nat
  | [] => 1
  | x :: xs => x * listProd xs

theorem listProd_append (l1 l2 : List Nat) :
    listProd (l1 ++ l2) = listProd l1 * listProd l2 := by
  induction l1 with
  | nil => simp [listProd]
  | cons x xs ih => simp [listProd, ih, Nat.mul_assoc]

theorem listProd_erase {x : Nat} {l : List Nat} (hx : x ∈ l) :
    x * listProd (l.erase x) = listProd l := by
  induction l with
  | nil => cases hx
  | cons y ys ih =>
    by_cases hxy : y = x
    · subst hxy; simp [List.erase, listProd]
    · have hbeq : (y == x) = false := beq_false_of_ne hxy
      simp only [List.erase, hbeq, listProd]
      have hxys : x ∈ ys := by
        cases hx with
        | head => exact absurd rfl hxy
        | tail _ h => exact h
      rw [← Nat.mul_assoc, Nat.mul_comm x y, Nat.mul_assoc, ih hxys]

theorem listProd_map_eq_of_inj {l1 l2 : List Nat} {f : Nat → Nat}
    (hlen : l1.length = l2.length) (hnodup : l1.Nodup)
    (hinj : ∀ x ∈ l1, ∀ y ∈ l1, f x = f y → x = y)
    (hmem : ∀ x ∈ l1, f x ∈ l2) :
    listProd (l1.map f) = listProd l2 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    simp only [List.map, listProd]
    have hfx : f x ∈ l2 := hmem x List.mem_cons_self
    have hxs_nodup : xs.Nodup := (List.nodup_cons.mp hnodup).2
    have hx_not_in : x ∉ xs := (List.nodup_cons.mp hnodup).1
    have hlen' : xs.length = (l2.erase (f x)).length := by
      rw [List.length_erase_of_mem hfx]; simp at hlen; omega
    have hmem' : ∀ y ∈ xs, f y ∈ l2.erase (f x) := by
      intro y hy
      have hne : f y ≠ f x := fun heq =>
        hx_not_in (hinj y (List.mem_cons_of_mem x hy) x List.mem_cons_self heq ▸ hy)
      exact (List.mem_erase_of_ne hne).mpr (hmem y (List.mem_cons_of_mem x hy))
    have hinj' : ∀ a ∈ xs, ∀ b ∈ xs, f a = f b → a = b :=
      fun a ha b hb => hinj a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb)
    rw [ih hlen' hxs_nodup hinj' hmem', listProd_erase hfx]

def range1 : Nat → List Nat
  | 0 => []
  | k + 1 => range1 k ++ [k + 1]

theorem mem_range1 {n x : Nat} : x ∈ range1 n ↔ 1 ≤ x ∧ x ≤ n := by
  induction n with
  | zero => simp [range1]; omega
  | succ k ih => simp only [range1, List.mem_append, List.mem_singleton, ih]; omega

theorem nodup_range1 (n : Nat) : (range1 n).Nodup := by
  induction n with
  | zero => simp [range1]
  | succ k ih =>
    rw [range1, List.nodup_append]
    refine ⟨ih, by simp, ?_⟩
    intro a ha b hb heq
    rw [List.mem_singleton] at hb
    rw [mem_range1] at ha
    omega

theorem listProd_map_range1 (n : Nat) (f : Nat → Nat) :
    listProd ((range1 n).map f) = prodRange n f := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [range1, List.map_append, List.map_cons, List.map_nil,
               listProd_append, listProd, Nat.mul_one, ih, prodRange]

theorem listProd_range1 (n : Nat) :
    listProd (range1 n) = prodRange n (fun k => k) := by
  simpa using listProd_map_range1 n (fun k => k)

/-- Exact helper: `(x - y) % p = 0` when `y ≤ x` and `x % p = y % p`. -/
theorem sub_mod_eq_zero_of_mod_eq {x y p : Nat} (hle : y ≤ x) (h : x % p = y % p) :
    (x - y) % p = 0 := by
  have hx := Nat.div_add_mod x p
  have hy := Nat.div_add_mod y p
  have hq : y / p ≤ x / p := by
    by_cases hp0 : p = 0
    · subst hp0; simp
    · exact Nat.div_le_div_right hle
  have hdiff : x - y = p * (x / p - y / p) := by
    rw [Nat.mul_sub]; omega
  rw [hdiff, Nat.mul_mod_right]

/-- Cancellation modulo a prime `p`. -/
theorem mod_cancel_right {p a b c : Nat} (hp : IsPrime p) (hnd : ¬ p ∣ c)
    (heq : (a * c) % p = (b * c) % p) : a % p = b % p := by
  have hp_pos : 0 < p := by have := hp.1; omega
  have hcp : Nat.Coprime c p := prime_coprime_of_not_dvd hp hnd
  have h1 : (a % p * c) % p = (b % p * c) % p := by
    rw [Nat.mod_mul_mod, Nat.mod_mul_mod]; exact heq
  have ha_lt : a % p < p := Nat.mod_lt a hp_pos
  have hb_lt : b % p < p := Nat.mod_lt b hp_pos
  by_cases hle : a % p ≤ b % p
  · have hd : p ∣ (b % p - a % p) * c := by
      rw [Nat.sub_mul]
      exact Nat.dvd_of_mod_eq_zero
        (sub_mod_eq_zero_of_mod_eq (Nat.mul_le_mul_right c hle) h1.symm)
    have hd2 : p ∣ (b % p - a % p) := hcp.symm.dvd_of_dvd_mul_right hd
    by_cases h0 : b % p - a % p = 0
    · omega
    · have := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hd2; omega
  · have hle' : b % p ≤ a % p := Nat.le_of_not_ge hle
    have hd : p ∣ (a % p - b % p) * c := by
      rw [Nat.sub_mul]
      exact Nat.dvd_of_mod_eq_zero
        (sub_mod_eq_zero_of_mod_eq (Nat.mul_le_mul_right c hle') h1)
    have hd2 : p ∣ (a % p - b % p) := hcp.symm.dvd_of_dvd_mul_right hd
    by_cases h0 : a % p - b % p = 0
    · omega
    · have := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hd2; omega

/-- Helper: `((p - 1) * (p - 1)) % p = 1` for `2 ≤ p`. -/
theorem sub_one_sq_mod {p : Nat} (hp : 2 ≤ p) : ((p - 1) * (p - 1)) % p = 1 := by
  have hid : (p - 1) * (p - 1) = p * (p - 2) + 1 := by
    cases p with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ k => grind
  rw [hid, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

/-- Helper: `((p - 1) ^ (2 * k)) % p = 1` for `2 ≤ p`. -/
theorem sub_one_pow_even_mod {p : Nat} (hp : 2 ≤ p) (k : Nat) :
    ((p - 1) ^ (2 * k)) % p = 1 := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt (by omega : 1 < p)]
  | succ j ih =>
    have heq : 2 * (j + 1) = 2 * j + 2 := by omega
    rw [heq, Nat.pow_add, Nat.mul_mod, ih, Nat.one_mul, Nat.mod_mod, Nat.pow_two]
    exact sub_one_sq_mod hp

/-- **Fermat's Little Theorem:** For prime `p` and `¬ p ∣ a`, `a ^ (p - 1) % p = 1`. -/
theorem fermat_little {p a : Nat} (hp : IsPrime p) (hnd : ¬ p ∣ a) :
    (a ^ (p - 1)) % p = 1 := by
  have hp2 : 2 ≤ p := hp.1
  have hp_pos : 0 < p := by omega
  have h1 : prodRange (p - 1) (fun k => (a * k) % p) = prodRange (p - 1) (fun k => k) := by
    rw [← listProd_map_range1, ← listProd_range1]
    apply listProd_map_eq_of_inj rfl (nodup_range1 _)
    · intro x hx y hy heq
      rw [mem_range1] at hx hy
      have h' : (x * a) % p = (y * a) % p := by
        rw [Nat.mul_comm x a, Nat.mul_comm y a]; exact heq
      have hmod := mod_cancel_right hp hnd h'
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
      exact hmod
    · intro x hx
      rw [mem_range1] at hx ⊢
      have hlt : (a * x) % p < p := Nat.mod_lt _ hp_pos
      have hne0 : (a * x) % p ≠ 0 := fun hz =>
        (prime_dvd_mul hp (Nat.dvd_of_mod_eq_zero hz)).elim hnd
          (prime_not_dvd_of_lt (by omega) (by omega))
      omega
  have h2 : (a ^ (p - 1) * prodRange (p - 1) (fun k => k)) % p =
            (1 * prodRange (p - 1) (fun k => k)) % p := by
    rw [Nat.one_mul, ← prodRange_const_mul]
    rw [prodRange_mod_eq (p - 1) p (fun k => a * k) (fun k => (a * k) % p)
          (fun k _ _ => (Nat.mod_mod _ _).symm), h1]
  have hnd_fact : ¬ p ∣ prodRange (p - 1) (fun k => k) :=
    prodRange_id_not_dvd hp (p - 1) (by omega)
  have hres := mod_cancel_right hp hnd_fact h2
  rw [Nat.mod_eq_of_lt (by omega : 1 < p)] at hres
  exact hres

/-- For odd prime `p` and `¬ p ∣ a`, `a ^ ((p - 1) / 2) % p` is either `1` or `p - 1`. -/
theorem euler_criterion_pm1 {p a : Nat} (hp : IsPrime p) (hodd : p % 2 = 1) (hnd : ¬ p ∣ a) :
    (a ^ ((p - 1) / 2)) % p = 1 ∨ (a ^ ((p - 1) / 2)) % p = p - 1 := by
  have hp3 : 3 ≤ p := by have := hp.1; omega
  let x := (a ^ ((p - 1) / 2)) % p
  have hx_lt : x < p := Nat.mod_lt _ (by omega)
  have hsq : (x * x) % p = 1 := by
    calc (x * x) % p
        = ((a ^ ((p - 1) / 2)) * (a ^ ((p - 1) / 2))) % p := (Nat.mul_mod _ _ p).symm
      _ = (a ^ ((p - 1) / 2 + (p - 1) / 2)) % p := by rw [← Nat.pow_add]
      _ = (a ^ (p - 1)) % p := by congr 2; omega
      _ = 1 := fermat_little hp hnd
  by_cases hx0 : x = 0
  · rw [hx0] at hsq; simp at hsq
  · have hd : p ∣ (x - 1) * (x + 1) := by
      have hmul : (x - 1) * (x + 1) = x * x - 1 := by
        cases hx : x with
        | zero => exact absurd hx hx0
        | succ k => grind
      rw [hmul]
      have hx1 : 1 ≤ x * x := Nat.mul_pos (Nat.pos_of_ne_zero hx0) (Nat.pos_of_ne_zero hx0)
      exact Nat.dvd_of_mod_eq_zero
        (sub_mod_eq_zero_of_mod_eq hx1 (by rw [hsq, Nat.mod_eq_of_lt (by omega : 1 < p)]))
    rcases prime_dvd_mul hp hd with h1 | h2
    · left
      by_cases hx1 : x = 1
      · exact hx1
      · have := Nat.le_of_dvd (by omega) h1; omega
    · right
      have := Nat.le_of_dvd (by omega) h2; omega

/-- Exact Legendre symbol on `Nat` via Euler's criterion. -/
def legendreNat (a p : Nat) : Int :=
  if a % p == 0 then 0
  else if (a ^ ((p - 1) / 2)) % p == 1 then 1
  else -1

theorem legendreNat_mod (a p : Nat) : legendreNat (a % p) p = legendreNat a p := by
  unfold legendreNat
  have h1 : (a % p) % p = a % p := Nat.mod_mod a p
  have h2 : ((a % p) ^ ((p - 1) / 2)) % p = (a ^ ((p - 1) / 2)) % p := by
    clear h1
    induction ((p - 1) / 2) with
    | zero => simp
    | succ k ih =>
      rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_mod, ih, Nat.mod_mod, ← Nat.mul_mod]
  rw [h1, h2]

theorem legendreNat_one {p : Nat} (hp : IsPrime p) : legendreNat 1 p = 1 := by
  have hp2 : 2 ≤ p := hp.1
  unfold legendreNat
  rw [Nat.one_pow, Nat.mod_eq_of_lt (by omega : 1 < p)]
  simp

theorem legendreNat_mul {p : Nat} (hp : IsPrime p) (hodd : p % 2 = 1) (a b : Nat) :
    legendreNat (a * b) p = legendreNat a p * legendreNat b p := by
  have hp3 : 3 ≤ p := by have := hp.1; omega
  by_cases ha : p ∣ a
  · have hab : p ∣ a * b := Nat.dvd_mul_right_of_dvd ha b
    simp [legendreNat, Nat.dvd_iff_mod_eq_zero.mp ha, Nat.dvd_iff_mod_eq_zero.mp hab]
  · by_cases hb : p ∣ b
    · have hab : p ∣ a * b := Nat.dvd_mul_left_of_dvd hb a
      simp [legendreNat, Nat.dvd_iff_mod_eq_zero.mp hb, Nat.dvd_iff_mod_eq_zero.mp hab]
    · have hab : ¬ p ∣ a * b := fun h => (prime_dvd_mul hp h).elim ha hb
      have ha0 : (a % p == 0) = false := beq_false_of_ne (fun h => ha (Nat.dvd_of_mod_eq_zero h))
      have hb0 : (b % p == 0) = false := beq_false_of_ne (fun h => hb (Nat.dvd_of_mod_eq_zero h))
      have hab0 : ((a * b) % p == 0) = false := beq_false_of_ne (fun h => hab (Nat.dvd_of_mod_eq_zero h))
      have hpow : ((a * b) ^ ((p - 1) / 2)) % p =
                  ((a ^ ((p - 1) / 2) % p) * (b ^ ((p - 1) / 2) % p)) % p := by
        rw [Nat.mul_pow, Nat.mul_mod]
      unfold legendreNat
      simp only [ha0, hb0, hab0, Bool.false_eq_true, ↓reduceIte]
      have hne1 : (p - 1 == 1) = false := beq_false_of_ne (by omega)
      rcases euler_criterion_pm1 hp hodd ha with ha1 | ham1 <;>
      rcases euler_criterion_pm1 hp hodd hb with hb1 | hbm1
      · rw [ha1, hb1, Nat.one_mul, Nat.mod_eq_of_lt (by omega : 1 < p)] at hpow
        simp [ha1, hb1, hpow]
      · rw [ha1, hbm1, Nat.one_mul, Nat.mod_eq_of_lt (by omega : p - 1 < p)] at hpow
        simp [ha1, hbm1, hpow, hne1]
      · rw [ham1, hb1, Nat.mul_one, Nat.mod_eq_of_lt (by omega : p - 1 < p)] at hpow
        simp [ham1, hb1, hpow, hne1]
      · rw [ham1, hbm1, sub_one_sq_mod (by omega)] at hpow
        simp [ham1, hbm1, hpow, hne1]

theorem legendreNat_sq {p : Nat} (hp : IsPrime p) (hodd : p % 2 = 1) {a : Nat} (hnd : ¬ p ∣ a) :
    legendreNat (a * a) p = 1 := by
  rw [legendreNat_mul hp hodd a a]
  have ha0 : (a % p == 0) = false := beq_false_of_ne (fun h => hnd (Nat.dvd_of_mod_eq_zero h))
  unfold legendreNat
  simp only [ha0, Bool.false_eq_true, ↓reduceIte]
  split <;> decide

theorem legendreNat_neg_one {p : Nat} (hp : IsPrime p) (hodd : p % 2 = 1) :
    legendreNat (p - 1) p = signNeg1 p := by
  have hp3 : 3 ≤ p := by have := hp.1; omega
  have hmod_ne : ((p - 1) % p == 0) = false := by
    rw [Nat.mod_eq_of_lt (by omega)]; exact beq_false_of_ne (by omega)
  unfold legendreNat signNeg1
  simp only [hmod_ne, Bool.false_eq_true, ↓reduceIte]
  by_cases h4 : p % 4 = 1
  · have hhalf : (p - 1) / 2 = 2 * ((p - 1) / 4) := by omega
    rw [hhalf, sub_one_pow_even_mod (by omega)]
    simp [h4]
  · have hhalf : (p - 1) / 2 = 2 * ((p - 1) / 4) + 1 := by omega
    rw [hhalf, Nat.pow_succ, Nat.mul_mod, sub_one_pow_even_mod (by omega), Nat.one_mul,
        Nat.mod_eq_of_lt (by omega : p - 1 < p), Nat.mod_eq_of_lt (by omega : p - 1 < p)]
    have hne : (p - 1 == 1) = false := beq_false_of_ne (by omega)
    have h4f : (p % 4 == 1) = false := beq_false_of_ne h4
    simp [hne, h4f]

/-- Sum of `f 1 + ... + f n`. -/
def sumRange (n : Nat) (f : Nat → Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => sumRange k f + f (k + 1)

theorem sumRange_add (n : Nat) (f g : Nat → Nat) :
    sumRange n (fun k => f k + g k) = sumRange n f + sumRange n g := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumRange, ih]; omega

theorem sumRange_const_mul (n c : Nat) (f : Nat → Nat) :
    sumRange n (fun k => c * f k) = c * sumRange n f := by
  induction n with
  | zero => simp [sumRange]
  | succ k ih => simp only [sumRange, ih, Nat.mul_add]

theorem sumRange_zero (n : Nat) : sumRange n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => simp [sumRange, ih]

/-- Gauss count via `sumRange` directly (avoids list-filter boilerplate). -/
def gaussCount (a p : Nat) : Nat :=
  sumRange ((p - 1) / 2) (fun k => if (p - 1) / 2 < (a * k) % p then 1 else 0)

def gaussFold (p r : Nat) : Nat :=
  if (p - 1) / 2 < r then p - r else r

theorem gauss_prod_mod (a p m : Nat) (hp : 3 ≤ p) (hodd : p % 2 = 1) (hm : m ≤ (p - 1) / 2) :
    (prodRange m (fun k => (a * k) % p)) % p =
    ((p - 1) ^ (sumRange m (fun k => if (p - 1) / 2 < (a * k) % p then 1 else 0)) *
      prodRange m (fun k => gaussFold p ((a * k) % p))) % p := by
  induction m with
  | zero => simp [prodRange, sumRange]
  | succ k ih =>
    simp only [prodRange, sumRange]
    rw [Nat.mul_mod, ih (Nat.le_of_succ_le hm)]
    let c := sumRange k (fun j => if (p - 1) / 2 < (a * j) % p then 1 else 0)
    let r := (a * (k + 1)) % p
    have hr_lt : r < p := Nat.mod_lt _ (by omega)
    change (((p - 1) ^ c * prodRange k (fun j => gaussFold p ((a * j) % p))) % p * (r % p)) % p =
      ((p - 1) ^ (c + if (p - 1) / 2 < r then 1 else 0) *
        (prodRange k (fun j => gaussFold p ((a * j) % p)) * gaussFold p r)) % p
    by_cases hgt : (p - 1) / 2 < r
    · have hgf : gaussFold p r = p - r := by unfold gaussFold; simp [hgt]
      simp only [hgt, ↓reduceIte]
      rw [hgf]
      have hpm : ((p - 1) * (p - r)) % p = r := by
        have hid : (p - 1) * (p - r) = p * (p - r - 1) + r := by
          have hr1 : 1 ≤ r := by omega
          have hpr1 : 1 ≤ p - r := by omega
          have h1 : (p - 1) * (p - r) + (p - r) = p * (p - r) := by
            rw [← Nat.succ_mul]; congr 1; omega
          have h2 : p * (p - r - 1) + p = p * (p - r) := by
            rw [← Nat.mul_succ]; congr 1; omega
          omega
        rw [hid, Nat.mul_add_mod, Nat.mod_eq_of_lt hr_lt]
      rw [Nat.pow_add, Nat.pow_one]
      have hrearr :
          ((p - 1) ^ c * (p - 1)) * (prodRange k (fun j => gaussFold p ((a * j) % p)) * (p - r)) =
          ((p - 1) ^ c * prodRange k (fun j => gaussFold p ((a * j) % p))) * ((p - 1) * (p - r)) := by
        grind
      rw [hrearr, Nat.mul_mod ((p - 1) ^ c * _), hpm, Nat.mod_eq_of_lt hr_lt]
    · have hgf : gaussFold p r = r := by unfold gaussFold; simp [hgt]
      simp only [hgt, ↓reduceIte, Nat.add_zero]
      rw [hgf, ← Nat.mul_assoc ((p - 1) ^ c), Nat.mul_mod ((p - 1) ^ c * _)]

/-- Shared injectivity lemma for Gauss's folding map on `{1, ..., (p - 1) / 2}`. -/
theorem gaussFold_inj {p a : Nat} (hp : IsPrime p) (hodd : p % 2 = 1) (hnd : ¬ p ∣ a) :
    ∀ x ∈ range1 ((p - 1) / 2), ∀ y ∈ range1 ((p - 1) / 2),
      gaussFold p ((a * x) % p) = gaussFold p ((a * y) % p) → x = y := by
  have hp3 : 3 ≤ p := by have := hp.1; omega
  intro x hx y hy heq
  rw [mem_range1] at hx hy
  have hrx_lt : (a * x) % p < p := Nat.mod_lt _ (by omega)
  have hry_lt : (a * y) % p < p := Nat.mod_lt _ (by omega)
  have hrx0 : (a * x) % p ≠ 0 := fun hz =>
    (prime_dvd_mul hp (Nat.dvd_of_mod_eq_zero hz)).elim hnd
      (prime_not_dvd_of_lt (by omega) (by omega))
  have hry0 : (a * y) % p ≠ 0 := fun hz =>
    (prime_dvd_mul hp (Nat.dvd_of_mod_eq_zero hz)).elim hnd
      (prime_not_dvd_of_lt (by omega) (by omega))
  have hcancel : (a * x) % p = (a * y) % p → x = y := by
    intro hreq
    have h' : (x * a) % p = (y * a) % p := by rw [Nat.mul_comm x a, Nat.mul_comm y a]; exact hreq
    have hm := mod_cancel_right hp hnd h'
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hm
    exact hm
  have hno_sum : (a * x) % p + (a * y) % p = p → False := by
    intro hsum
    have hd : p ∣ a * (x + y) := by
      rw [Nat.mul_add]
      exact Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, hsum, Nat.mod_self])
    exact (prime_dvd_mul hp hd).elim hnd (prime_not_dvd_of_lt (by omega) (by omega))
  unfold gaussFold at heq
  split at heq <;> split at heq
  · exact hcancel (by omega)
  · exact False.elim (hno_sum (by omega))
  · exact False.elim (hno_sum (by omega))
  · exact hcancel heq

theorem gaussFold_mem {p a : Nat} (hp : IsPrime p) (hodd : p % 2 = 1) (hnd : ¬ p ∣ a) :
    ∀ x ∈ range1 ((p - 1) / 2), gaussFold p ((a * x) % p) ∈ range1 ((p - 1) / 2) := by
  have hp3 : 3 ≤ p := by have := hp.1; omega
  intro x hx
  rw [mem_range1] at hx ⊢
  have hrx_lt : (a * x) % p < p := Nat.mod_lt _ (by omega)
  have hrx0 : (a * x) % p ≠ 0 := fun hz =>
    (prime_dvd_mul hp (Nat.dvd_of_mod_eq_zero hz)).elim hnd
      (prime_not_dvd_of_lt (by omega) (by omega))
  unfold gaussFold; split <;> omega

/-- **Gauss's Lemma:** `legendreNat a p = if gaussCount a p % 2 == 0 then 1 else -1`. -/
theorem gauss_lemma {p a : Nat} (hp : IsPrime p) (hodd : p % 2 = 1) (hnd : ¬ p ∣ a) :
    legendreNat a p = if gaussCount a p % 2 == 0 then 1 else -1 := by
  have hp3 : 3 ≤ p := by have := hp.1; omega
  let m := (p - 1) / 2
  have hperm : prodRange m (fun k => gaussFold p ((a * k) % p)) = prodRange m (fun k => k) := by
    rw [← listProd_map_range1, ← listProd_range1]
    exact listProd_map_eq_of_inj rfl (nodup_range1 m)
      (gaussFold_inj hp hodd hnd) (gaussFold_mem hp hodd hnd)
  have hmain : (a ^ m * prodRange m (fun k => k)) % p =
               ((p - 1) ^ (gaussCount a p) * prodRange m (fun k => k)) % p := by
    rw [← prodRange_const_mul,
        prodRange_mod_eq m p (fun k => a * k) (fun k => (a * k) % p) (fun _ _ _ => (Nat.mod_mod _ _).symm),
        gauss_prod_mod a p m hp3 hodd (Nat.le_refl m), hperm]
    rfl
  have hnd_fact : ¬ p ∣ prodRange m (fun k => k) := prodRange_id_not_dvd hp m (by omega)
  have hpow_eq : (a ^ m) % p = ((p - 1) ^ (gaussCount a p)) % p :=
    mod_cancel_right hp hnd_fact hmain
  have ha0 : (a % p == 0) = false := beq_false_of_ne (fun h => hnd (Nat.dvd_of_mod_eq_zero h))
  unfold legendreNat
  simp only [ha0, Bool.false_eq_true, ↓reduceIte]
  by_cases hev : gaussCount a p % 2 = 0
  · have hgc : gaussCount a p = 2 * (gaussCount a p / 2) := by omega
    rw [hgc, sub_one_pow_even_mod (by omega)] at hpow_eq
    change (if (a ^ m % p == 1) = true then 1 else -1) = _
    rw [hpow_eq]; simp [hev]
  · have hgc : gaussCount a p = 2 * (gaussCount a p / 2) + 1 := by omega
    rw [hgc, Nat.pow_succ, Nat.mul_mod, sub_one_pow_even_mod (by omega), Nat.one_mul,
        Nat.mod_eq_of_lt (by omega : p - 1 < p), Nat.mod_eq_of_lt (by omega : p - 1 < p)] at hpow_eq
    have hne : (p - 1 == 1) = false := beq_false_of_ne (by omega)
    have hevf : (gaussCount a p % 2 == 0) = false := beq_false_of_ne hev
    change (if (a ^ m % p == 1) = true then 1 else -1) = _
    rw [hpow_eq]; simp [hne, hevf]

/-- **Second Supplementary Law:** `legendreNat 2 p = signTwo p` for all odd primes `p`. -/
theorem legendreNat_two {p : Nat} (hp : IsPrime p) (hodd : p % 2 = 1) :
    legendreNat 2 p = signTwo p := by
  have hp3 : 3 ≤ p := by have := hp.1; omega
  have hnd2 : ¬ p ∣ 2 := prime_not_dvd_of_lt (by decide) (by omega)
  rw [gauss_lemma hp hodd hnd2]
  unfold gaussCount signTwo
  have hcount : ∀ n, n ≤ (p - 1) / 2 →
      sumRange n (fun k => if (p - 1) / 2 < (2 * k) % p then 1 else 0) =
      if (p - 1) / 4 < n then n - (p - 1) / 4 else 0 := by
    intro n
    induction n with
    | zero => intro _; simp [sumRange]
    | succ k ih =>
      intro hle
      simp only [sumRange, ih (Nat.le_of_succ_le hle)]
      have h2k : (2 * (k + 1)) % p = 2 * (k + 1) := Nat.mod_eq_of_lt (by omega)
      rw [h2k]
      by_cases h1 : (p - 1) / 2 < 2 * (k + 1) <;>
      by_cases h2 : (p - 1) / 4 < k <;>
      by_cases h3 : (p - 1) / 4 < k + 1 <;>
        simp [h1, h2, h3] <;> omega
  rw [hcount ((p - 1) / 2) (Nat.le_refl _)]
  have hp8 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
  rcases hp8 with h | h | h | h
  · have hc : (if (p - 1) / 4 < (p - 1) / 2 then (p - 1) / 2 - (p - 1) / 4 else 0) % 2 = 0 := by split <;> omega
    simp [h, hc]
  · have hc : (if (p - 1) / 4 < (p - 1) / 2 then (p - 1) / 2 - (p - 1) / 4 else 0) % 2 = 1 := by split <;> omega
    simp [h, hc]
  · have hc : (if (p - 1) / 4 < (p - 1) / 2 then (p - 1) / 2 - (p - 1) / 4 else 0) % 2 = 1 := by split <;> omega
    simp [h, hc]
  · have hc : (if (p - 1) / 4 < (p - 1) / 2 then (p - 1) / 2 - (p - 1) / 4 else 0) % 2 = 0 := by split <;> omega
    simp [h, hc]

def listSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + listSum xs

theorem listSum_append (l1 l2 : List Nat) :
    listSum (l1 ++ l2) = listSum l1 + listSum l2 := by
  induction l1 with
  | nil => simp [listSum]
  | cons x xs ih => simp [listSum, ih, Nat.add_assoc]

theorem listSum_erase {x : Nat} {l : List Nat} (hx : x ∈ l) :
    x + listSum (l.erase x) = listSum l := by
  induction l with
  | nil => cases hx
  | cons y ys ih =>
    by_cases hxy : y = x
    · subst hxy; simp [List.erase, listSum]
    · have hbeq : (y == x) = false := beq_false_of_ne hxy
      simp only [List.erase, hbeq, listSum]
      have hxys : x ∈ ys := by
        cases hx with
        | head => exact absurd rfl hxy
        | tail _ h => exact h
      rw [← Nat.add_assoc, Nat.add_comm x y, Nat.add_assoc, ih hxys]

theorem listSum_map_eq_of_inj {l1 l2 : List Nat} {f : Nat → Nat}
    (hlen : l1.length = l2.length) (hnodup : l1.Nodup)
    (hinj : ∀ x ∈ l1, ∀ y ∈ l1, f x = f y → x = y)
    (hmem : ∀ x ∈ l1, f x ∈ l2) :
    listSum (l1.map f) = listSum l2 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    simp only [List.map, listSum]
    have hfx : f x ∈ l2 := hmem x List.mem_cons_self
    have hxs_nodup : xs.Nodup := (List.nodup_cons.mp hnodup).2
    have hx_not_in : x ∉ xs := (List.nodup_cons.mp hnodup).1
    have hlen' : xs.length = (l2.erase (f x)).length := by
      rw [List.length_erase_of_mem hfx]; simp at hlen; omega
    have hmem' : ∀ y ∈ xs, f y ∈ l2.erase (f x) := by
      intro y hy
      have hne : f y ≠ f x := fun heq =>
        hx_not_in (hinj y (List.mem_cons_of_mem x hy) x List.mem_cons_self heq ▸ hy)
      exact (List.mem_erase_of_ne hne).mpr (hmem y (List.mem_cons_of_mem x hy))
    have hinj' : ∀ a ∈ xs, ∀ b ∈ xs, f a = f b → a = b :=
      fun a ha b hb => hinj a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb)
    rw [ih hlen' hxs_nodup hinj' hmem', listSum_erase hfx]

theorem listSum_map_range1 (n : Nat) (f : Nat → Nat) :
    listSum ((range1 n).map f) = sumRange n f := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [range1, List.map_append, List.map_cons, List.map_nil,
               listSum_append, listSum, Nat.add_zero, ih, sumRange]

theorem listSum_range1 (n : Nat) :
    listSum (range1 n) = sumRange n (fun k => k) := by
  simpa using listSum_map_range1 n (fun k => k)

/-- **Eisenstein's Parity Lemma:** `gaussCount a p % 2 = (∑_{k=1}^{(p-1)/2} ⌊a*k/p⌋) % 2`. -/
theorem eisenstein_parity {p a : Nat} (hp : IsPrime p) (hp_odd : p % 2 = 1)
    (ha_odd : a % 2 = 1) (hnd : ¬ p ∣ a) :
    gaussCount a p % 2 = (sumRange ((p - 1) / 2) (fun k => (a * k) / p)) % 2 := by
  have hp3 : 3 ≤ p := by have := hp.1; omega
  let m := (p - 1) / 2
  have hsum_fold : sumRange m (fun k => gaussFold p ((a * k) % p)) = sumRange m (fun k => k) := by
    rw [← listSum_map_range1, ← listSum_range1]
    exact listSum_map_eq_of_inj rfl (nodup_range1 m)
      (gaussFold_inj hp hp_odd hnd) (gaussFold_mem hp hp_odd hnd)
  have hterm : ∀ n, (sumRange n (fun k => a * k) + sumRange n (fun k => gaussFold p ((a * k) % p))) % 2 =
      (sumRange n (fun k => (a * k) / p) +
       sumRange n (fun k => if (p - 1) / 2 < (a * k) % p then 1 else 0)) % 2 := by
    intro n
    induction n with
    | zero => simp [sumRange]
    | succ k ih =>
      simp only [sumRange]
      have hdiv : a * (k + 1) = p * ((a * (k + 1)) / p) + (a * (k + 1)) % p :=
        (Nat.div_add_mod (a * (k + 1)) p).symm
      have hlt : (a * (k + 1)) % p < p := Nat.mod_lt _ (by omega)
      have hgf_case : (a * (k + 1) + gaussFold p ((a * (k + 1)) % p)) % 2 =
                      ((a * (k + 1)) / p + if (p - 1) / 2 < (a * (k + 1)) % p then 1 else 0) % 2 := by
        unfold gaussFold
        by_cases hgt : (p - 1) / 2 < (a * (k + 1)) % p
        · simp only [hgt, ↓reduceIte]
          have : a * (k + 1) + (p - (a * (k + 1)) % p) = p * ((a * (k + 1)) / p) + p := by omega
          rw [this, Nat.add_mod, Nat.mul_mod, hp_odd]; omega
        · simp only [hgt, ↓reduceIte]
          have : a * (k + 1) + (a * (k + 1)) % p = p * ((a * (k + 1)) / p) + 2 * ((a * (k + 1)) % p) := by omega
          rw [this, Nat.add_mod, Nat.mul_mod, hp_odd]; omega
      have hre1 : (sumRange k (fun j => a * j) + a * (k + 1) +
                   (sumRange k (fun j => gaussFold p ((a * j) % p)) + gaussFold p ((a * (k + 1)) % p))) =
                  (sumRange k (fun j => a * j) + sumRange k (fun j => gaussFold p ((a * j) % p))) +
                  (a * (k + 1) + gaussFold p ((a * (k + 1)) % p)) := by omega
      have hre2 : (sumRange k (fun j => (a * j) / p) + (a * (k + 1)) / p +
                   (sumRange k (fun j => if (p - 1) / 2 < (a * j) % p then 1 else 0) +
                    if (p - 1) / 2 < (a * (k + 1)) % p then 1 else 0)) =
                  (sumRange k (fun j => (a * j) / p) +
                   sumRange k (fun j => if (p - 1) / 2 < (a * j) % p then 1 else 0)) +
                  ((a * (k + 1)) / p + if (p - 1) / 2 < (a * (k + 1)) % p then 1 else 0) := by omega
      rw [hre1, hre2, Nat.add_mod, Nat.add_mod (sumRange k _ + _), ih, hgf_case]
  have hmain := hterm m
  rw [sumRange_const_mul, hsum_fold] at hmain
  have hadd : a * sumRange m (fun k => k) + sumRange m (fun k => k) =
              (a + 1) * sumRange m (fun k => k) := by rw [Nat.add_mul, Nat.one_mul]
  rw [hadd] at hmain
  have hev : ((a + 1) * sumRange m (fun k => k)) % 2 = 0 := by
    have : (a + 1) % 2 = 0 := by omega
    rw [Nat.mul_mod, this]; simp
  rw [hev] at hmain
  change (sumRange m (fun k => if (p - 1) / 2 < (a * k) % p then 1 else 0)) % 2 =
         (sumRange m (fun k => (a * k) / p)) % 2
  omega

/-- Swap double `sumRange` order. -/
theorem sumRange_swap (A B : Nat) (P : Nat → Nat → Nat) :
    sumRange A (fun x => sumRange B (fun y => P x y)) =
    sumRange B (fun y => sumRange A (fun x => P x y)) := by
  induction A with
  | zero =>
    simp only [sumRange]
    exact (sumRange_zero B).symm
  | succ a iha =>
    simp only [sumRange, iha, sumRange_add]

/-- Count `y ∈ {1..n}` with `d * y < c` equals `c / d` when `c / d ≤ n` and `c % d ≠ 0`. -/
theorem sumRange_lt_div (n c d : Nat) (hd : 0 < d) (hle : c / d ≤ n) (hmod : c % d ≠ 0) :
    sumRange n (fun y => if d * y < c then 1 else 0) = c / d := by
  induction n with
  | zero =>
    have : c / d = 0 := Nat.eq_zero_of_le_zero hle
    simp [sumRange, this]
  | succ k ihk =>
    simp only [sumRange]
    by_cases hck : c / d ≤ k
    · have hgt : ¬ (d * (k + 1) < c) := by
        have hdm := Nat.div_add_mod c d
        have hlt : c % d < d := Nat.mod_lt c hd
        have h1 : d * (k + 1) = d * k + d := Nat.mul_succ d k
        have h2 : d * (c / d) ≤ d * k := Nat.mul_le_mul_left d hck
        omega
      simp [hgt, ihk hck]
    · have heq : c / d = k + 1 := by omega
      have hdm := Nat.div_add_mod c d
      have hlt_k : d * (k + 1) < c := by rw [← heq]; omega
      have hall : ∀ m, (∀ y, 1 ≤ y → y ≤ m → d * y < c) →
          sumRange m (fun y => if d * y < c then 1 else 0) = m := by
        intro m
        induction m with
        | zero => intro _; rfl
        | succ r ihr =>
          intro hltm
          simp only [sumRange, ihr (fun y hy1 hyr => hltm y hy1 (Nat.le_succ_of_le hyr)),
                     hltm (r + 1) (Nat.succ_pos r) (Nat.le_refl _), ↓reduceIte]
      have hprev : sumRange k (fun y => if d * y < c then 1 else 0) = k :=
        hall k (fun y _ hy => by
          have : d * y ≤ d * (k + 1) := Nat.mul_le_mul_left d (Nat.le_succ_of_le hy)
          omega)
      simp [hlt_k, hprev, heq]

/-- **Eisenstein's Rectangle Lattice-Point Identity** for distinct odd primes `p ≠ q`. -/
theorem eisenstein_rectangle {p q : Nat} (hp : IsPrime p) (hq : IsPrime q)
    (hp_odd : p % 2 = 1) (hq_odd : q % 2 = 1) (hne : p ≠ q) :
    sumRange ((p - 1) / 2) (fun x => (q * x) / p) +
    sumRange ((q - 1) / 2) (fun y => (p * y) / q) =
    ((p - 1) / 2) * ((q - 1) / 2) := by
  have hp3 : 3 ≤ p := by have := hp.1; omega
  have hq3 : 3 ≤ q := by have := hq.1; omega
  let X := (p - 1) / 2
  let Y := (q - 1) / 2
  have hnod : ∀ x y, 1 ≤ x → x ≤ X → 1 ≤ y → y ≤ Y → q * x ≠ p * y := by
    intro x y hx1 hx2 hy1 hy2 heq
    have hd : p ∣ q * x := ⟨y, heq⟩
    have hndq : ¬ p ∣ q := fun hdq => (hq.2 p hdq).elim (by omega) hne
    exact (prime_dvd_mul hp hd).elim hndq (prime_not_dvd_of_lt (by omega) (by omega))
  have hleX : ∀ x, 1 ≤ x → x ≤ X → (q * x) / p ≤ Y := by
    intro x _ hx
    have hmul : q * x ≤ q * X := Nat.mul_le_mul_left q hx
    have hbd : q * X < p * (Y + 1) := by
      have hp2 : 2 * X = p - 1 := by omega
      have hq2 : 2 * Y = q - 1 := by omega
      have hL : 2 * (q * X) = q * (p - 1) := by
        rw [← Nat.mul_assoc, Nat.mul_comm 2 q, Nat.mul_assoc, hp2]
      have hR : 2 * (p * (Y + 1)) = p * (q + 1) := by
        have : 2 * (Y + 1) = q + 1 := by omega
        rw [← Nat.mul_assoc, Nat.mul_comm 2 p, Nat.mul_assoc, this]
      have h1 : q * (p - 1) + q = q * p := by
        cases p with | zero => omega | succ k => grind
      have h2 : p * (q + 1) = p * q + p := by grind
      have h3 : q * p = p * q := Nat.mul_comm q p
      omega
    exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (by omega)).mpr (by
      rw [Nat.mul_comm (Y + 1) p]; exact Nat.lt_of_le_of_lt hmul hbd))
  have hleY : ∀ y, 1 ≤ y → y ≤ Y → (p * y) / q ≤ X := by
    intro y _ hy
    have hmul : p * y ≤ p * Y := Nat.mul_le_mul_left p hy
    have hbd : p * Y < q * (X + 1) := by
      have hp2 : 2 * X = p - 1 := by omega
      have hq2 : 2 * Y = q - 1 := by omega
      have hL : 2 * (p * Y) = p * (q - 1) := by
        rw [← Nat.mul_assoc, Nat.mul_comm 2 p, Nat.mul_assoc, hq2]
      have hR : 2 * (q * (X + 1)) = q * (p + 1) := by
        have : 2 * (X + 1) = p + 1 := by omega
        rw [← Nat.mul_assoc, Nat.mul_comm 2 q, Nat.mul_assoc, this]
      have h1 : p * (q - 1) + p = p * q := by
        cases q with | zero => omega | succ k => grind
      have h2 : q * (p + 1) = q * p + q := by grind
      have h3 : q * p = p * q := Nat.mul_comm q p
      omega
    exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (by omega)).mpr (by
      rw [Nat.mul_comm (X + 1) q]; exact Nat.lt_of_le_of_lt hmul hbd))
  have h1 : sumRange X (fun x => (q * x) / p) =
      sumRange X (fun x => sumRange Y (fun y => if p * y < q * x then 1 else 0)) := by
    have hstep : ∀ n, n ≤ X →
        sumRange n (fun x => (q * x) / p) =
        sumRange n (fun x => sumRange Y (fun y => if p * y < q * x then 1 else 0)) := by
      intro n
      induction n with
      | zero => intro _; rfl
      | succ k ihk =>
        intro hnk
        simp only [sumRange, ihk (Nat.le_of_succ_le hnk)]
        congr 1
        have hmod_ne : (q * (k + 1)) % p ≠ 0 := by
          intro hz
          have hd : p ∣ q * (k + 1) := Nat.dvd_of_mod_eq_zero hz
          have hndq : ¬ p ∣ q := fun hdq => (hq.2 p hdq).elim (by omega) hne
          exact (prime_dvd_mul hp hd).elim hndq (prime_not_dvd_of_lt (Nat.succ_pos k) (by omega))
        exact (sumRange_lt_div Y (q * (k + 1)) p (by omega) (hleX (k + 1) (Nat.succ_pos k) hnk) hmod_ne).symm
    exact hstep X (Nat.le_refl _)
  have h2 : sumRange Y (fun y => (p * y) / q) =
      sumRange Y (fun y => sumRange X (fun x => if q * x < p * y then 1 else 0)) := by
    have hstep : ∀ n, n ≤ Y →
        sumRange n (fun y => (p * y) / q) =
        sumRange n (fun y => sumRange X (fun x => if q * x < p * y then 1 else 0)) := by
      intro n
      induction n with
      | zero => intro _; rfl
      | succ k ihk =>
        intro hnk
        simp only [sumRange, ihk (Nat.le_of_succ_le hnk)]
        congr 1
        have hmod_ne : (p * (k + 1)) % q ≠ 0 := by
          intro hz
          have hd : q ∣ p * (k + 1) := Nat.dvd_of_mod_eq_zero hz
          have hndp : ¬ q ∣ p := fun hdp => (hp.2 q hdp).elim (by omega) hne.symm
          exact (prime_dvd_mul hq hd).elim hndp (prime_not_dvd_of_lt (Nat.succ_pos k) (by omega))
        exact (sumRange_lt_div X (p * (k + 1)) q (by omega) (hleY (k + 1) (Nat.succ_pos k) hnk) hmod_ne).symm
    exact hstep Y (Nat.le_refl _)
  change sumRange X (fun x => (q * x) / p) + sumRange Y (fun y => (p * y) / q) = X * Y
  rw [h1, h2, sumRange_swap Y X (fun y x => if q * x < p * y then 1 else 0), ← sumRange_add]
  have htot : ∀ n, n ≤ X →
      sumRange n (fun x => sumRange Y (fun y => if p * y < q * x then 1 else 0) +
                           sumRange Y (fun y => if q * x < p * y then 1 else 0)) = n * Y := by
    intro n
    induction n with
    | zero => intro _; simp [sumRange]
    | succ k ihk =>
      intro hnk
      simp only [sumRange]
      rw [ihk (Nat.le_of_succ_le hnk), ← sumRange_add]
      have hinner : ∀ m, m ≤ Y →
          sumRange m (fun y => (if p * y < q * (k + 1) then 1 else 0) +
                               (if q * (k + 1) < p * y then 1 else 0)) = m := by
        intro m
        induction m with
        | zero => intro _; rfl
        | succ j ihj =>
          intro hmj
          simp only [sumRange, ihj (Nat.le_of_succ_le hmj)]
          have hne1 := hnod (k + 1) (j + 1) (Nat.succ_pos k) hnk (Nat.succ_pos j) hmj
          by_cases hlt : p * (j + 1) < q * (k + 1)
          · have hnot : ¬ (q * (k + 1) < p * (j + 1)) := by omega
            simp [hlt, hnot]
          · have hgt : q * (k + 1) < p * (j + 1) := by omega
            simp [hlt, hgt]
      rw [hinner Y (Nat.le_refl Y), Nat.succ_mul]
  exact htot X (Nat.le_refl _)

/-- **GAUSS'S QUADRATIC RECIPROCITY LAW (Prime Form):**
    For distinct odd primes `p ≠ q`, `legendreNat q p * legendreNat p q = signQR p q`. -/
theorem quadratic_reciprocity_prime {p q : Nat} (hp : IsPrime p) (hq : IsPrime q)
    (hp_odd : p % 2 = 1) (hq_odd : q % 2 = 1) (hne : p ≠ q) :
    legendreNat q p * legendreNat p q = signQR p q := by
  have hp3 : 3 ≤ p := by have := hp.1; omega
  have hq3 : 3 ≤ q := by have := hq.1; omega
  have hnd_pq : ¬ p ∣ q := fun hd => (hq.2 p hd).elim (by omega) hne
  have hnd_qp : ¬ q ∣ p := fun hd => (hp.2 q hd).elim (by omega) hne.symm
  rw [gauss_lemma hp hp_odd hnd_pq, gauss_lemma hq hq_odd hnd_qp]
  have he1 := eisenstein_parity hp hp_odd hq_odd hnd_pq
  have he2 := eisenstein_parity hq hq_odd hp_odd hnd_qp
  have hrect := eisenstein_rectangle hp hq hp_odd hq_odd hne
  have hsum_par : (gaussCount q p + gaussCount p q) % 2 = (((p - 1) / 2) * ((q - 1) / 2)) % 2 := by
    rw [Nat.add_mod, he1, he2, ← Nat.add_mod, hrect]
  unfold signQR
  have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
  have hq4 : q % 4 = 1 ∨ q % 4 = 3 := by omega
  have hgc1 : gaussCount q p % 2 = 0 ∨ gaussCount q p % 2 = 1 := by omega
  have hgc2 : gaussCount p q % 2 = 0 ∨ gaussCount p q % 2 = 1 := by omega
  have hmul_eq : (((p - 1) / 2) * ((q - 1) / 2)) % 2 =
                 ((((p - 1) / 2) % 2) * (((q - 1) / 2) % 2)) % 2 := Nat.mul_mod _ _ 2
  rw [hmul_eq] at hsum_par
  rcases hp4 with hp4 | hp4 <;> rcases hq4 with hq4 | hq4
  · have h1 : ((p - 1) / 2) % 2 = 0 := by omega
    have h2 : ((q - 1) / 2) % 2 = 0 := by omega
    rw [h1, h2] at hsum_par
    rcases hgc1 with c1 | c1 <;> rcases hgc2 with c2 | c2 <;>
      (rw [Nat.add_mod, c1, c2] at hsum_par; simp [hp4, hq4, c1, c2] at hsum_par ⊢)
  · have h1 : ((p - 1) / 2) % 2 = 0 := by omega
    have h2 : ((q - 1) / 2) % 2 = 1 := by omega
    rw [h1, h2] at hsum_par
    rcases hgc1 with c1 | c1 <;> rcases hgc2 with c2 | c2 <;>
      (rw [Nat.add_mod, c1, c2] at hsum_par; simp [hp4, hq4, c1, c2] at hsum_par ⊢)
  · have h1 : ((p - 1) / 2) % 2 = 1 := by omega
    have h2 : ((q - 1) / 2) % 2 = 0 := by omega
    rw [h1, h2] at hsum_par
    rcases hgc1 with c1 | c1 <;> rcases hgc2 with c2 | c2 <;>
      (rw [Nat.add_mod, c1, c2] at hsum_par; simp [hp4, hq4, c1, c2] at hsum_par ⊢)
  · have h1 : ((p - 1) / 2) % 2 = 1 := by omega
    have h2 : ((q - 1) / 2) % 2 = 1 := by omega
    rw [h1, h2] at hsum_par
    rcases hgc1 with c1 | c1 <;> rcases hgc2 with c2 | c2 <;>
      (rw [Nat.add_mod, c1, c2] at hsum_par; simp [hp4, hq4, c1, c2] at hsum_par ⊢)

/-! ### Prime Factorization & Full Jacobi Symbol `jacobi : Int → Nat → Int` -/

def smallestFactorAux (n d fuel : Nat) : Nat :=
  match fuel with
  | 0 => n
  | fuel' + 1 =>
    if d * d > n then n
    else if n % d = 0 then d
    else smallestFactorAux n (d + 1) fuel'

def smallestFactor (n : Nat) : Nat :=
  if n ≤ 1 then n else smallestFactorAux n 2 n

theorem smallestFactorAux_dvd (n d fuel : Nat) :
    smallestFactorAux n d fuel ∣ n := by
  induction fuel generalizing d with
  | zero => exact Nat.dvd_refl n
  | succ f ih =>
    simp only [smallestFactorAux]
    split
    · exact Nat.dvd_refl n
    · split
      · rename_i hmod; exact Nat.dvd_of_mod_eq_zero hmod
      · exact ih (d + 1)

theorem smallestFactorAux_ge (n d fuel : Nat) (hd2 : 2 ≤ d) (hd : d ≤ n) :
    d ≤ smallestFactorAux n d fuel := by
  induction fuel generalizing d with
  | zero => exact hd
  | succ f ih =>
    simp only [smallestFactorAux]
    split
    · exact hd
    · split
      · exact Nat.le_refl d
      · rename_i hng _
        have hsq : d * d ≤ n := Nat.le_of_not_lt hng
        have hle : d + 1 ≤ n := by
          have : d + 1 ≤ d * d := by
            cases d with
            | zero => omega
            | succ k =>
              cases k with
              | zero => omega
              | succ j => grind
          omega
        exact Nat.le_trans (Nat.le_succ d) (ih (d + 1) (by omega) hle)

theorem smallestFactorAux_min (n d fuel : Nat) (hd : 2 ≤ d) (hfuel : n ≤ d + fuel)
    (hno : ∀ k, 2 ≤ k → k < d → ¬ k ∣ n) :
    ∀ k, 2 ≤ k → k < smallestFactorAux n d fuel → ¬ k ∣ n := by
  induction fuel generalizing d with
  | zero =>
    intro k hk1 hk2 hkn
    simp only [smallestFactorAux] at hk2
    exact hno k hk1 (by omega) hkn
  | succ f ih =>
    simp only [smallestFactorAux]
    split
    · rename_i hgt
      intro k hk1 hk2 hkn
      by_cases hkd : k < d
      · exact hno k hk1 hkd hkn
      · rcases hkn with ⟨q, hq⟩
        have hq2 : 2 ≤ q := by
          cases q with
          | zero => simp at hq; omega
          | succ m =>
            cases m with
            | zero => simp at hq; omega
            | succ _ => omega
        have hqd : q < d := by
          by_cases hlt : q < d
          · exact hlt
          · exfalso
            have h1 : d ≤ k := Nat.le_of_not_lt hkd
            have h2 : d ≤ q := Nat.le_of_not_lt hlt
            have h3 : d * d ≤ k * q := Nat.mul_le_mul h1 h2
            omega
        exact hno q hq2 hqd ⟨k, by rw [Nat.mul_comm]; exact hq⟩
    · split
      · exact hno
      · rename_i hng hnm
        apply ih (d + 1) (by omega) (by omega)
        intro k hk1 hkd hkn
        by_cases hke : k = d
        · subst hke; exact hnm (Nat.mod_eq_zero_of_dvd hkn)
        · exact hno k hk1 (by omega) hkn

theorem smallestFactor_isPrime {n : Nat} (hn : 2 ≤ n) : IsPrime (smallestFactor n) := by
  have h1 : ¬ n ≤ 1 := by omega
  simp only [smallestFactor, h1, ↓reduceIte]
  have hdvd : smallestFactorAux n 2 n ∣ n := smallestFactorAux_dvd n 2 n
  have hge2 : 2 ≤ smallestFactorAux n 2 n := smallestFactorAux_ge n 2 n (by decide) hn
  have hmin := smallestFactorAux_min n 2 n (by decide) (by omega) (fun k hk1 hk2 => by omega)
  refine ⟨hge2, ?_⟩
  intro d hd
  by_cases hd0 : d = 0
  · subst hd0; rcases hd with ⟨q, hq⟩; simp at hq; omega
  · by_cases hd1 : d = 1
    · left; exact hd1
    · right
      have hle := Nat.le_of_dvd (by omega) hd
      by_cases hlt : d < smallestFactorAux n 2 n
      · exfalso; exact hmin d (by omega) hlt (Nat.dvd_trans hd hdvd)
      · omega

theorem smallestFactor_dvd {n : Nat} (hn : 2 ≤ n) : smallestFactor n ∣ n := by
  have h1 : ¬ n ≤ 1 := by omega
  simp only [smallestFactor, h1, ↓reduceIte]
  exact smallestFactorAux_dvd n 2 n

def primeFactorsAux (n fuel : Nat) : List Nat :=
  match fuel with
  | 0 => []
  | fuel' + 1 =>
    if n ≤ 1 then []
    else
      let p := smallestFactor n
      p :: primeFactorsAux (n / p) fuel'

def primeFactors (n : Nat) : List Nat :=
  primeFactorsAux n n

theorem primeFactorsAux_spec (n fuel : Nat) (hn1 : 1 ≤ n) (hfuel : n ≤ fuel) :
    listProd (primeFactorsAux n fuel) = n ∧
    ∀ p ∈ primeFactorsAux n fuel, IsPrime p := by
  induction fuel generalizing n with
  | zero => omega
  | succ f ih =>
    simp only [primeFactorsAux]
    by_cases h1 : n ≤ 1
    · have hn : n = 1 := by omega
      subst hn
      simp only [Nat.le_refl, ↓reduceIte, listProd]
      exact ⟨trivial, fun _ h => nomatch h⟩
    · simp only [h1, ↓reduceIte]
      have hn2 : 2 ≤ n := by omega
      have hp : IsPrime (smallestFactor n) := smallestFactor_isPrime hn2
      have hdvd : smallestFactor n ∣ n := smallestFactor_dvd hn2
      have hdiv_pos : 1 ≤ n / smallestFactor n := by
        rcases hdvd with ⟨q, hq⟩
        have hqpos : 1 ≤ q := by
          cases q with
          | zero => simp at hq; omega
          | succ _ => omega
        have hqp : n / smallestFactor n = q := by
          have hsf2 : 2 ≤ smallestFactor n := hp.1
          exact Nat.div_eq_of_eq_mul_right (by omega) hq
        rw [hqp]; exact hqpos
      have hlt : n / smallestFactor n < n :=
        Nat.div_lt_self (by omega) (Nat.lt_of_lt_of_le (by decide) hp.1)
      have hsub := ih (n / smallestFactor n) hdiv_pos (by omega)
      refine ⟨?_, ?_⟩
      · simp only [listProd, hsub.1]
        exact Nat.mul_div_cancel' hdvd
      · intro q hq
        cases hq with
        | head => exact hp
        | tail _ h => exact hsub.2 q h

theorem primeFactors_spec {n : Nat} (hn : 1 ≤ n) :
    listProd (primeFactors n) = n ∧ ∀ p ∈ primeFactors n, IsPrime p :=
  primeFactorsAux_spec n n hn (Nat.le_refl n)

def legendreListProd (a : Nat) : List Nat → Int
  | [] => 1
  | p :: ps => legendreNat a p * legendreListProd a ps

def jacobiNat (a n : Nat) : Int :=
  legendreListProd a (primeFactors n)

def jacobi (a : Int) (n : Nat) : Int :=
  if n == 0 then 0 else jacobiNat (a % (n : Int)).toNat n

theorem legendreListProd_append (a : Nat) (l1 l2 : List Nat) :
    legendreListProd a (l1 ++ l2) = legendreListProd a l1 * legendreListProd a l2 := by
  induction l1 with
  | nil => simp [legendreListProd]
  | cons p ps ih => simp [legendreListProd, ih, Int.mul_assoc]

theorem legendreListProd_erase (a x : Nat) {l : List Nat} (hx : x ∈ l) :
    legendreNat a x * legendreListProd a (l.erase x) = legendreListProd a l := by
  induction l with
  | nil => cases hx
  | cons y ys ih =>
    by_cases hxy : y = x
    · subst hxy; simp [List.erase, legendreListProd]
    · have hbeq : (y == x) = false := beq_false_of_ne hxy
      simp only [List.erase, hbeq, legendreListProd]
      have hxys : x ∈ ys := by
        cases hx with
        | head => exact absurd rfl hxy
        | tail _ h => exact h
      rw [← Int.mul_assoc, Int.mul_comm (legendreNat a x), Int.mul_assoc, ih hxys]

theorem prime_mem_of_dvd_listProd {p : Nat} (hp : IsPrime p) {l : List Nat}
    (hall : ∀ q ∈ l, IsPrime q) (hdvd : p ∣ listProd l) : p ∈ l := by
  induction l with
  | nil =>
    simp only [listProd] at hdvd
    have := Nat.le_of_dvd (by decide) hdvd
    have := hp.1
    omega
  | cons q qs ih =>
    simp only [listProd] at hdvd
    rcases prime_dvd_mul hp hdvd with h1 | h2
    · have hq : IsPrime q := hall q List.mem_cons_self
      rcases hq.2 p h1 with h1' | heq
      · have := hp.1; omega
      · subst heq; exact List.mem_cons_self
    · exact List.mem_cons_of_mem q (ih (fun r hr => hall r (List.mem_cons_of_mem q hr)) h2)

theorem listProd_pos_of_primes {l : List Nat} (h : ∀ p ∈ l, IsPrime p) : 1 ≤ listProd l := by
  induction l with
  | nil => decide
  | cons p ps ih =>
    simp only [listProd]
    have hp := (h p List.mem_cons_self).1
    have hps := ih (fun q hq => h q (List.mem_cons_of_mem p hq))
    exact Nat.mul_pos (by omega) hps

theorem listProd_odd_of_all_odd {l : List Nat} (h : ∀ p ∈ l, p % 2 = 1) : listProd l % 2 = 1 := by
  induction l with
  | nil => decide
  | cons p ps ih =>
    simp only [listProd]
    rw [Nat.mul_mod, h p List.mem_cons_self, ih (fun q hq => h q (List.mem_cons_of_mem p hq))]

theorem legendreListProd_eq_of_listProd_eq (a : Nat) {l1 l2 : List Nat}
    (h1 : ∀ p ∈ l1, IsPrime p) (h2 : ∀ p ∈ l2, IsPrime p)
    (heq : listProd l1 = listProd l2) :
    legendreListProd a l1 = legendreListProd a l2 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => rfl
    | cons q qs =>
      simp only [listProd] at heq
      have hq := (h2 q List.mem_cons_self).1
      have hpos := listProd_pos_of_primes (fun r hr => h2 r (List.mem_cons_of_mem q hr))
      have : 2 ≤ q * listProd qs := Nat.le_trans hq (Nat.le_mul_of_pos_right q hpos)
      omega
  | cons p ps ih =>
    have hp : IsPrime p := h1 p List.mem_cons_self
    have hdvd : p ∣ listProd l2 := ⟨listProd ps, heq.symm⟩
    have hmem : p ∈ l2 := prime_mem_of_dvd_listProd hp h2 hdvd
    have her : listProd ps = listProd (l2.erase p) := by
      have hmul : p * listProd (l2.erase p) = listProd l2 := listProd_erase hmem
      have hmul2 : p * listProd ps = p * listProd (l2.erase p) := by
        simp only [listProd] at heq; rw [heq, hmul]
      exact Nat.eq_of_mul_eq_mul_left (by have := hp.1; omega) hmul2
    have h2' : ∀ q ∈ l2.erase p, IsPrime q := fun q hq => h2 q (List.mem_of_mem_erase hq)
    simp only [legendreListProd]
    rw [ih (fun q hq => h1 q (List.mem_cons_of_mem p hq)) h2' her,
        legendreListProd_erase a p hmem]

theorem odd_mem_of_odd_listProd {l : List Nat} (hodd : listProd l % 2 = 1) :
    ∀ p ∈ l, p % 2 = 1 := by
  induction l with
  | nil => intro _ h; cases h
  | cons q qs ih =>
    simp only [listProd] at hodd
    have hq : q % 2 = 1 := by
      by_cases h : q % 2 = 1
      · exact h
      · have h0 : q % 2 = 0 := by omega
        rw [Nat.mul_mod, h0] at hodd; simp at hodd
    have hqs : listProd qs % 2 = 1 := by
      by_cases h : listProd qs % 2 = 1
      · exact h
      · have h0 : listProd qs % 2 = 0 := by omega
        rw [Nat.mul_mod, h0] at hodd; simp at hodd
    intro p hp
    cases hp with
    | head => exact hq
    | tail _ h => exact ih hqs p h

theorem jacobiNat_mul_right (a : Nat) {m n : Nat} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    jacobiNat a (m * n) = jacobiNat a m * jacobiNat a n := by
  unfold jacobiNat
  have hspec_mn := primeFactors_spec (Nat.mul_pos hm hn)
  have hspec_m := primeFactors_spec hm
  have hspec_n := primeFactors_spec hn
  rw [← legendreListProd_append]
  apply legendreListProd_eq_of_listProd_eq a hspec_mn.2
  · intro p hp
    rcases List.mem_append.mp hp with h1 | h2
    · exact hspec_m.2 p h1
    · exact hspec_n.2 p h2
  · rw [listProd_append, hspec_mn.1, hspec_m.1, hspec_n.1]

theorem jacobiNat_mul_left {n : Nat} (hn : 1 ≤ n) (hodd : n % 2 = 1) (a b : Nat) :
    jacobiNat (a * b) n = jacobiNat a n * jacobiNat b n := by
  unfold jacobiNat
  have hspec := primeFactors_spec hn
  have hodd_l : ∀ p ∈ primeFactors n, p % 2 = 1 :=
    odd_mem_of_odd_listProd (by rw [hspec.1]; exact hodd)
  have haux : ∀ (ls : List Nat), (∀ p ∈ ls, IsPrime p) → (∀ p ∈ ls, p % 2 = 1) →
      legendreListProd (a * b) ls = legendreListProd a ls * legendreListProd b ls := by
    intro ls
    induction ls with
    | nil => intro _ _; simp [legendreListProd]
    | cons p ps ih =>
      intro hpr hod
      have hp := hpr p List.mem_cons_self
      have hpo := hod p List.mem_cons_self
      simp only [legendreListProd, legendreNat_mul hp hpo a b,
                 ih (fun q hq => hpr q (List.mem_cons_of_mem p hq))
                    (fun q hq => hod q (List.mem_cons_of_mem p hq))]
      grind
  exact haux (primeFactors n) hspec.2 hodd_l

theorem jacobiNat_one (n : Nat) (hn : 1 ≤ n) : jacobiNat 1 n = 1 := by
  unfold jacobiNat
  have hspec := primeFactors_spec hn
  have haux : ∀ ls : List Nat, (∀ p ∈ ls, IsPrime p) → legendreListProd 1 ls = 1 := by
    intro ls
    induction ls with
    | nil => intro _; rfl
    | cons p ps ih =>
      intro hpr
      simp only [legendreListProd, legendreNat_one (hpr p List.mem_cons_self),
                 ih (fun q hq => hpr q (List.mem_cons_of_mem p hq)), Int.one_mul]
  exact haux (primeFactors n) hspec.2

theorem jacobiNat_mod (a : Nat) {n : Nat} (hn : 1 ≤ n) :
    jacobiNat (a % n) n = jacobiNat a n := by
  unfold jacobiNat
  have hspec := primeFactors_spec hn
  have haux : ∀ ls : List Nat, (∀ p ∈ ls, p ∣ n) →
      legendreListProd (a % n) ls = legendreListProd a ls := by
    intro ls
    induction ls with
    | nil => intro _; rfl
    | cons p ps ih =>
      intro hd
      have hpn : p ∣ n := hd p List.mem_cons_self
      have hmod : (a % n) % p = a % p := Nat.mod_mod_of_dvd a hpn
      simp only [legendreListProd]
      rw [← legendreNat_mod (a % n) p, hmod, legendreNat_mod a p,
          ih (fun q hq => hd q (List.mem_cons_of_mem p hq))]
  apply haux (primeFactors n)
  intro p hp
  have her := listProd_erase hp
  rw [hspec.1] at her
  exact ⟨listProd ((primeFactors n).erase p), her.symm⟩

theorem jacobiNat_eq_of_mod_eq {a b n : Nat} (hn : 1 ≤ n) (h : a % n = b % n) :
    jacobiNat a n = jacobiNat b n := by
  rw [← jacobiNat_mod a hn, h, jacobiNat_mod b hn]

theorem jacobiNat_sq {a n : Nat} (hn : 1 ≤ n) (hodd : n % 2 = 1) (hcop : Nat.Coprime a n) :
    jacobiNat (a * a) n = 1 := by
  unfold jacobiNat
  have hspec := primeFactors_spec hn
  have hodd_l : ∀ p ∈ primeFactors n, p % 2 = 1 :=
    odd_mem_of_odd_listProd (by rw [hspec.1]; exact hodd)
  have haux : ∀ ls : List Nat, (∀ p ∈ ls, IsPrime p) → (∀ p ∈ ls, p % 2 = 1) →
      (∀ p ∈ ls, ¬ p ∣ a) → legendreListProd (a * a) ls = 1 := by
    intro ls
    induction ls with
    | nil => intro _ _ _; rfl
    | cons p ps ih =>
      intro hpr hod hnd
      simp only [legendreListProd,
                 legendreNat_sq (hpr p List.mem_cons_self) (hod p List.mem_cons_self) (hnd p List.mem_cons_self),
                 ih (fun q hq => hpr q (List.mem_cons_of_mem p hq))
                    (fun q hq => hod q (List.mem_cons_of_mem p hq))
                    (fun q hq => hnd q (List.mem_cons_of_mem p hq)), Int.one_mul]
  apply haux (primeFactors n) hspec.2 hodd_l
  intro p hp hdva
  have hp_pr := hspec.2 p hp
  have hdvn : p ∣ n := by
    have her := listProd_erase hp; rw [hspec.1] at her; exact ⟨_, her.symm⟩
  have hdg : p ∣ Nat.gcd a n := Nat.dvd_gcd hdva hdvn
  rw [hcop] at hdg
  have := Nat.le_of_dvd (by decide) hdg
  have := hp_pr.1
  omega

theorem jacobi_neg_one {n : Nat} (hn : 1 ≤ n) (hodd : n % 2 = 1) :
    jacobi (-1) n = signNeg1 n := by
  have hn0 : (n == 0) = false := beq_false_of_ne (by omega)
  unfold jacobi
  simp only [hn0, Bool.false_eq_true, ↓reduceIte]
  have hmod : ((-1 : Int) % (n : Int)).toNat = n - 1 := by
    have h1 : (-1 : Int) % (n : Int) = (n : Int) - 1 := by
      have hadd : (-1 : Int) + 1 * (n : Int) = (n : Int) - 1 := by omega
      rw [← Int.add_mul_emod_self_right (-1) 1 (n : Int), hadd,
          Int.emod_eq_of_lt (by omega) (by omega)]
    rw [h1]; omega
  rw [hmod]
  unfold jacobiNat
  have hspec := primeFactors_spec hn
  have hodd_l : ∀ p ∈ primeFactors n, p % 2 = 1 :=
    odd_mem_of_odd_listProd (by rw [hspec.1]; exact hodd)
  have haux : ∀ ls : List Nat, (∀ p ∈ ls, IsPrime p) → (∀ p ∈ ls, p % 2 = 1) →
      (∀ p ∈ ls, p ∣ n) → legendreListProd (n - 1) ls = signNeg1 (listProd ls) := by
    intro ls
    induction ls with
    | nil => intro _ _ _; simp [legendreListProd, listProd, signNeg1]
    | cons p ps ih =>
      intro hpr hod hdvd
      have hp := hpr p List.mem_cons_self
      have hpo := hod p List.mem_cons_self
      have hpn := hdvd p List.mem_cons_self
      have hp3 : 3 ≤ p := by have := hp.1; omega
      have hnm : (n - 1) % p = p - 1 := by
        rcases hpn with ⟨q, hq⟩
        have hqpos : 1 ≤ q := by
          cases q with | zero => simp at hq; omega | succ _ => omega
        have hsub : n - 1 = p * (q - 1) + (p - 1) := by
          have : p * (q - 1) + p = p * q := by rw [← Nat.mul_succ]; congr 1; omega
          omega
        rw [hsub, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
      simp only [legendreListProd, listProd]
      rw [← legendreNat_mod (n - 1) p, hnm, legendreNat_neg_one hp hpo,
          ih (fun q hq => hpr q (List.mem_cons_of_mem p hq))
             (fun q hq => hod q (List.mem_cons_of_mem p hq))
             (fun q hq => hdvd q (List.mem_cons_of_mem p hq))]
      have hps_odd := listProd_odd_of_all_odd (fun q hq => hod q (List.mem_cons_of_mem p hq))
      exact (signNeg1_mul hpo hps_odd).symm
  rw [haux (primeFactors n) hspec.2 hodd_l (fun p hp => by
    have her := listProd_erase hp; rw [hspec.1] at her; exact ⟨_, her.symm⟩), hspec.1]

theorem jacobiNat_two {n : Nat} (hn : 1 ≤ n) (hodd : n % 2 = 1) :
    jacobiNat 2 n = signTwo n := by
  unfold jacobiNat
  have hspec := primeFactors_spec hn
  have hodd_l : ∀ p ∈ primeFactors n, p % 2 = 1 :=
    odd_mem_of_odd_listProd (by rw [hspec.1]; exact hodd)
  have haux : ∀ ls : List Nat, (∀ p ∈ ls, IsPrime p) → (∀ p ∈ ls, p % 2 = 1) →
      legendreListProd 2 ls = signTwo (listProd ls) := by
    intro ls
    induction ls with
    | nil => intro _ _; decide
    | cons p ps ih =>
      intro hpr hod
      have hp := hpr p List.mem_cons_self
      have hpo := hod p List.mem_cons_self
      simp only [legendreListProd, listProd, legendreNat_two hp hpo,
                 ih (fun q hq => hpr q (List.mem_cons_of_mem p hq))
                    (fun q hq => hod q (List.mem_cons_of_mem p hq))]
      have hps_odd := listProd_odd_of_all_odd (fun q hq => hod q (List.mem_cons_of_mem p hq))
      exact (signTwo_mul hpo hps_odd).symm
  rw [haux (primeFactors n) hspec.2 hodd_l, hspec.1]

/-- **FULL GAUSS QUADRATIC RECIPROCITY LAW FOR THE JACOBI SYMBOL:**
    `jacobiNat m n * jacobiNat n m = signQR m n` for all odd coprime `m ≥ 1, n ≥ 1`. -/
theorem jacobiNat_quadratic_reciprocity {m n : Nat} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hm_odd : m % 2 = 1) (hn_odd : n % 2 = 1) (hcop : Nat.Coprime m n) :
    jacobiNat m n * jacobiNat n m = signQR m n := by
  have hspec_m := primeFactors_spec hm
  have hspec_n := primeFactors_spec hn
  have hodd_m : ∀ p ∈ primeFactors m, p % 2 = 1 :=
    odd_mem_of_odd_listProd (by rw [hspec_m.1]; exact hm_odd)
  have hodd_n : ∀ q ∈ primeFactors n, q % 2 = 1 :=
    odd_mem_of_odd_listProd (by rw [hspec_n.1]; exact hn_odd)
  have haux : ∀ (lm ln : List Nat),
      (∀ p ∈ lm, IsPrime p) → (∀ q ∈ ln, IsPrime q) →
      (∀ p ∈ lm, p % 2 = 1) → (∀ q ∈ ln, q % 2 = 1) →
      (∀ p ∈ lm, ∀ q ∈ ln, p ≠ q) →
      legendreListProd (listProd lm) ln * legendreListProd (listProd ln) lm =
      signQR (listProd lm) (listProd ln) := by
    intro lm
    induction lm with
    | nil =>
      intro ln _ hqn _ hodn hdisj
      clear hodn hdisj
      simp only [listProd, legendreListProd, Int.mul_one]
      have h1 : legendreListProd 1 ln = 1 := by
        clear hspec_m hspec_n hodd_m hodd_n
        induction ln with
        | nil => rfl
        | cons q qs ihq =>
          simp only [legendreListProd, legendreNat_one (hqn q List.mem_cons_self), Int.one_mul]
          exact ihq (fun r hr => hqn r (List.mem_cons_of_mem q hr))
      rw [h1]; unfold signQR; simp
    | cons p ps ihp =>
      intro ln hpm hqn hodm hodn hdisj
      have hp := hpm p List.mem_cons_self
      have hpo := hodm p List.mem_cons_self
      have hps_pr : ∀ r ∈ ps, IsPrime r := fun r hr => hpm r (List.mem_cons_of_mem p hr)
      have hps_odd_l : ∀ r ∈ ps, r % 2 = 1 := fun r hr => hodm r (List.mem_cons_of_mem p hr)
      have hdisj_ps : ∀ r ∈ ps, ∀ q ∈ ln, r ≠ q :=
        fun r hr q hq => hdisj r (List.mem_cons_of_mem p hr) q hq
      have hps_odd := listProd_odd_of_all_odd hps_odd_l
      have hln_odd := listProd_odd_of_all_odd hodn
      have hsingle : legendreListProd p ln * legendreNat (listProd ln) p = signQR p (listProd ln) := by
        clear ihp hps_pr hps_odd_l hdisj_ps hps_odd hln_odd
        induction ln with
        | nil => simp only [listProd, legendreListProd, legendreNat_one hp, Int.one_mul]; unfold signQR; simp
        | cons q qs ihq =>
          have hq := hqn q List.mem_cons_self
          have hqo := hodn q List.mem_cons_self
          have hpq : p ≠ q := hdisj p List.mem_cons_self q List.mem_cons_self
          have hqs_odd := listProd_odd_of_all_odd (fun r hr => hodn r (List.mem_cons_of_mem q hr))
          simp only [legendreListProd, listProd]
          rw [legendreNat_mul hp hpo q (listProd qs)]
          have hrearr :
              (legendreNat p q * legendreListProd p qs) * (legendreNat q p * legendreNat (listProd qs) p) =
              (legendreNat q p * legendreNat p q) * (legendreListProd p qs * legendreNat (listProd qs) p) := by
            grind
          rw [hrearr, quadratic_reciprocity_prime hp hq hpo hqo hpq,
              ihq (fun r hr => hqn r (List.mem_cons_of_mem q hr))
                  (fun r hr => hodn r (List.mem_cons_of_mem q hr))
                  (fun a ha b hb => hdisj a ha b (List.mem_cons_of_mem q hb))]
          exact (signQR_mul_right hpo hqo hqs_odd).symm
      have hsplit : legendreListProd (p * listProd ps) ln =
          legendreListProd p ln * legendreListProd (listProd ps) ln := by
        clear ihp hsingle hdisj hdisj_ps hln_odd
        induction ln with
        | nil => simp [legendreListProd]
        | cons q qs ihq =>
          have hq := hqn q List.mem_cons_self
          have hqo := hodn q List.mem_cons_self
          simp only [legendreListProd, legendreNat_mul hq hqo p (listProd ps),
                     ihq (fun r hr => hqn r (List.mem_cons_of_mem q hr))
                         (fun r hr => hodn r (List.mem_cons_of_mem q hr))]
          grind
      simp only [listProd, legendreListProd]
      rw [hsplit]
      have hrearr2 :
          (legendreListProd p ln * legendreListProd (listProd ps) ln) *
          (legendreNat (listProd ln) p * legendreListProd (listProd ln) ps) =
          (legendreListProd p ln * legendreNat (listProd ln) p) *
          (legendreListProd (listProd ps) ln * legendreListProd (listProd ln) ps) := by
        grind
      rw [hrearr2, hsingle, ihp ln hps_pr hqn hps_odd_l hodn hdisj_ps]
      exact (signQR_mul_left hpo hps_odd hln_odd).symm
  unfold jacobiNat
  have hdisj : ∀ p ∈ primeFactors m, ∀ q ∈ primeFactors n, p ≠ q := by
    intro p hp q hq heq
    subst heq
    have hpm : p ∣ m := by have her := listProd_erase hp; rw [hspec_m.1] at her; exact ⟨_, her.symm⟩
    have hpn : p ∣ n := by have her := listProd_erase hq; rw [hspec_n.1] at her; exact ⟨_, her.symm⟩
    have hdg : p ∣ Nat.gcd m n := Nat.dvd_gcd hpm hpn
    rw [hcop] at hdg
    have := Nat.le_of_dvd (by decide) hdg
    have := (hspec_m.2 p hp).1
    omega
  have hres := haux (primeFactors m) (primeFactors n) hspec_m.2 hspec_n.2 hodd_m hodd_n hdisj
  rw [hspec_m.1, hspec_n.1] at hres
  exact hres

/-! ### Clean `Int`-Signed Wrappers for `jacobi : Int → Nat → Int` -/

theorem jacobi_ofNat (a : Nat) {n : Nat} (hn : 1 ≤ n) :
    jacobi (a : Int) n = jacobiNat a n := by
  have hn0 : (n == 0) = false := beq_false_of_ne (by omega)
  unfold jacobi
  simp only [hn0, Bool.false_eq_true, ↓reduceIte]
  have hm : ((a : Int) % (n : Int)).toNat = a % n := by omega
  rw [hm, jacobiNat_mod a hn]

theorem jacobi_mod (a : Int) {n : Nat} (hn : 1 ≤ n) :
    jacobi (a % (n : Int)) n = jacobi a n := by
  have hn0 : (n == 0) = false := beq_false_of_ne (by omega)
  unfold jacobi
  simp only [hn0, Bool.false_eq_true, ↓reduceIte, Int.emod_emod]

theorem jacobi_eq_of_mod_eq {a b : Int} {n : Nat} (hn : 1 ≤ n)
    (h : a % (n : Int) = b % (n : Int)) : jacobi a n = jacobi b n := by
  rw [← jacobi_mod a hn, h, jacobi_mod b hn]

theorem jacobi_mul_left {n : Nat} (hn : 1 ≤ n) (hodd : n % 2 = 1) (a b : Int) :
    jacobi (a * b) n = jacobi a n * jacobi b n := by
  have hn0 : (n == 0) = false := beq_false_of_ne (by omega)
  unfold jacobi
  simp only [hn0, Bool.false_eq_true, ↓reduceIte]
  rw [← jacobiNat_mul_left hn hodd]
  apply jacobiNat_eq_of_mod_eq hn
  have ha0 : 0 ≤ a % (n : Int) := Int.emod_nonneg a (by omega)
  have hb0 : 0 ≤ b % (n : Int) := Int.emod_nonneg b (by omega)
  have hab0 : 0 ≤ (a * b) % (n : Int) := Int.emod_nonneg (a * b) (by omega)
  have h1 : (((a % (n : Int)).toNat * (b % (n : Int)).toNat : Nat) : Int) % (n : Int) =
            ((a * b) % (n : Int)) := by
    rw [Int.natCast_mul, Int.toNat_of_nonneg ha0, Int.toNat_of_nonneg hb0, ← Int.mul_emod]
  have h2 : (((a % (n : Int)).toNat * (b % (n : Int)).toNat % n : Nat) : Int) =
            (((a * b) % (n : Int)).toNat : Int) := by
    rw [Int.natCast_emod, h1, Int.toNat_of_nonneg hab0]
  have h3 : ((a * b) % (n : Int)).toNat % n = ((a * b) % (n : Int)).toNat := by
    apply Nat.mod_eq_of_lt
    have := Int.emod_lt_of_pos (a * b) (by omega : (0 : Int) < n)
    omega
  rw [h3]; omega

theorem jacobi_mul_right (a : Int) {m n : Nat} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    jacobi a (m * n) = jacobi a m * jacobi a n := by
  have hm0 : (m == 0) = false := beq_false_of_ne (by omega)
  have hn0 : (n == 0) = false := beq_false_of_ne (by omega)
  have hmn0 : (m * n == 0) = false := beq_false_of_ne (Nat.mul_ne_zero (by omega) (by omega))
  unfold jacobi
  simp only [hm0, hn0, hmn0, Bool.false_eq_true, ↓reduceIte]
  rw [jacobiNat_mul_right _ hm hn]
  have hmn_ne : ((m * n : Nat) : Int) ≠ 0 := by
    have : 1 ≤ m * n := Nat.mul_pos hm hn; omega
  congr 1
  · apply jacobiNat_eq_of_mod_eq hm
    have h0 : 0 ≤ a % ((m * n : Nat) : Int) := Int.emod_nonneg a hmn_ne
    have h1 : 0 ≤ a % (m : Int) := Int.emod_nonneg a (by omega)
    have h2 : (a % ((m * n : Nat) : Int)) % (m : Int) = a % (m : Int) :=
      Int.emod_emod_of_dvd a ⟨n, by rw [Int.natCast_mul]⟩
    have h3 : (((a % ((m * n : Nat) : Int)).toNat % m : Nat) : Int) = ((a % (m : Int)).toNat : Int) := by
      rw [Int.natCast_emod, Int.toNat_of_nonneg h0, h2, Int.toNat_of_nonneg h1]
    have h4 : (a % (m : Int)).toNat % m = (a % (m : Int)).toNat := by
      apply Nat.mod_eq_of_lt
      have := Int.emod_lt_of_pos a (by omega : (0 : Int) < m); omega
    rw [h4]; omega
  · apply jacobiNat_eq_of_mod_eq hn
    have h0 : 0 ≤ a % ((m * n : Nat) : Int) := Int.emod_nonneg a hmn_ne
    have h1 : 0 ≤ a % (n : Int) := Int.emod_nonneg a (by omega)
    have h2 : (a % ((m * n : Nat) : Int)) % (n : Int) = a % (n : Int) :=
      Int.emod_emod_of_dvd a ⟨m, by rw [Int.natCast_mul, Int.mul_comm]⟩
    have h3 : (((a % ((m * n : Nat) : Int)).toNat % n : Nat) : Int) = ((a % (n : Int)).toNat : Int) := by
      rw [Int.natCast_emod, Int.toNat_of_nonneg h0, h2, Int.toNat_of_nonneg h1]
    have h4 : (a % (n : Int)).toNat % n = (a % (n : Int)).toNat := by
      apply Nat.mod_eq_of_lt
      have := Int.emod_lt_of_pos a (by omega : (0 : Int) < n); omega
    rw [h4]; omega

theorem jacobi_sq {a : Int} {n : Nat} (hn : 1 ≤ n) (hodd : n % 2 = 1)
    (hcop : Nat.Coprime a.natAbs n) : jacobi (a * a) n = 1 := by
  have ha : a * a = ((a.natAbs * a.natAbs : Nat) : Int) := by
    rw [Int.natCast_mul]
    exact (Int.natAbs_mul_self' a).symm
  rw [ha, jacobi_ofNat _ hn]
  exact jacobiNat_sq hn hodd hcop

theorem jacobi_neg {a : Int} {n : Nat} (hn : 1 ≤ n) (hodd : n % 2 = 1) :
    jacobi (-a) n = signNeg1 n * jacobi a n := by
  have h : -a = (-1) * a := by omega
  rw [h, jacobi_mul_left hn hodd (-1) a, jacobi_neg_one hn hodd]

theorem jacobi_two {n : Nat} (hn : 1 ≤ n) (hodd : n % 2 = 1) :
    jacobi 2 n = signTwo n := by
  rw [show (2 : Int) = ((2 : Nat) : Int) from rfl, jacobi_ofNat 2 hn]
  exact jacobiNat_two hn hodd

theorem jacobi_neg_two {n : Nat} (hn : 1 ≤ n) (hodd : n % 2 = 1) :
    jacobi (-2) n = if n % 8 == 1 || n % 8 == 3 then 1 else -1 := by
  rw [jacobi_neg hn hodd, jacobi_two hn hodd]
  unfold signNeg1 signTwo
  have h8 : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by omega
  rcases h8 with h | h | h | h
  · have h4 : n % 4 = 1 := by omega
    simp [h, h4]
  · have h4 : n % 4 = 3 := by omega
    simp [h, h4]
  · have h4 : n % 4 = 1 := by omega
    simp [h, h4]
  · have h4 : n % 4 = 3 := by omega
    simp [h, h4]

theorem jacobi_pm1_of_coprime {a : Int} {n : Nat} (hn : 1 ≤ n) (hodd : n % 2 = 1)
    (hcop : Nat.Coprime a.natAbs n) : jacobi a n = 1 ∨ jacobi a n = -1 := by
  have hsq : jacobi a n * jacobi a n = 1 := by
    rw [← jacobi_mul_left hn hodd, jacobi_sq hn hodd hcop]
  have h1 : (jacobi a n - 1) * (jacobi a n + 1) = 0 := by grind
  rcases Int.mul_eq_zero.mp h1 with h | h
  · left; omega
  · right; omega

/-- **T1b Master Export:** Complete Gauss Quadratic Reciprocity & Supplementary Laws for the
    Jacobi symbol over `Int × Nat` (zero Mathlib, zero `sorry`). -/
theorem t1b_jacobi_reciprocity_master :
    (∀ (n : Nat), 1 ≤ n → n % 2 = 1 → jacobi (-1) n = signNeg1 n) ∧
    (∀ (n : Nat), 1 ≤ n → n % 2 = 1 → jacobi 2 n = signTwo n) ∧
    (∀ (m n : Nat), 1 ≤ m → 1 ≤ n → m % 2 = 1 → n % 2 = 1 → Nat.Coprime m n →
      jacobi (m : Int) n * jacobi (n : Int) m = signQR m n) ∧
    (∀ (n : Nat) (a b : Int), 1 ≤ n → n % 2 = 1 → jacobi (a * b) n = jacobi a n * jacobi b n) ∧
    (∀ (n : Nat) (a : Int), 1 ≤ n → n % 2 = 1 → Nat.Coprime a.natAbs n → jacobi (a * a) n = 1) := by
  refine ⟨fun _ hn ho => jacobi_neg_one hn ho,
          fun _ hn ho => jacobi_two hn ho,
          fun m n hm hn hmo hno hcop => ?_,
          fun _ a b hn ho => jacobi_mul_left hn ho a b,
          fun _ a hn ho hcop => jacobi_sq hn ho hcop⟩
  rw [jacobi_ofNat m hn, jacobi_ofNat n hm]
  exact jacobiNat_quadratic_reciprocity hm hn hmo hno hcop

end

end ApollonianSandpileMarkov.JacobiReciprocity
