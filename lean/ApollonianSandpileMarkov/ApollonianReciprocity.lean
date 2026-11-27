-- SPDX-License-Identifier: Apache-2.0
module

public import ApollonianSandpileMarkov.JacobiReciprocity

/-!
# Pillar I: Thin Lorentzian Vieta Reflection Groups, Apollonian & Octahedral Congruence /
# Reciprocity Obstructions, and the `d ∈ {2, 3}` Soddy Divisibility Fact

Formalizes:
- `T1a`: Descartes Lorentzian quadratic form `Q_D`, all 4 Vieta reflections `S1..S4`, exact
  Gaussian sum-of-squares identity `(a + b)(a + c) = a^2 + k^2`, and Brahmagupta–Descartes
  binary quadratic form product identity.
- `T1c`: Zero-Mathlib constructive proof (zero GCD exceptions, via parabolic Dehn-twist CRT) of
  the Haag–Kertzer–Rickards–Stange (*Annals of Math.*, 2024, arXiv:2307.02749) square obstruction
  for the three primitive 4-even Apollonian packings `(-3, 5, 8, 8)`, `(-7, 17, 12, 20)`, and
  `(-11, 21, 24, 28)` — contrasted with the square-hitting packing `(-4, 8, 9, 9)` (which hits
  `9 = 3^2`, though HKRS list `3n^2, 6n^2, n^4, 4n^4` obstructions for it).
- `T1d`: Octahedral circle packing Lorentzian equations `IsOctahedral`, all 8 face reflections,
  exact `ℚ(√-2)` norm identity `(a + b)(a + c) = a^2 + 2 k^2`, mod-8 residue locking
  `(2, 2, 1, 0, 0, 1)` on the orbit of `(-6, 10, 17, 40, 24, 17)` excluding squares at `b1, b2`
  and twice-squares at `b3, b6` by congruence, plus five closed Jacobi evaluations and the strip
  contrast `(0, 0, 1, 2, 2, 1)` (cf. Shi, Shi, Whitehead, Williams-Tracy & Zhang, arXiv:2510.21702).
- `T1e`: General `d`-dimensional Soddy–Gosset integrality dichotomy (`soddyQ d` is preserved by an
  integer linear reflection `soddyRefl d α` iff `(d - 1) * α = 2`, hence iff `d = 2 ∨ d = 3`,
  formalizing Lagarias–Mallows–Wilks 2002), all five 3D Soddy involutions preserving `soddy3Q`, and
  the 3D reflection hitting `25 = 5^2`.
-/

namespace ApollonianSandpileMarkov.ApollonianReciprocity

open ApollonianSandpileMarkov.JacobiReciprocity

@[expose] public section

/-! ### Part 1: Descartes Lorentzian Form, Vieta Reflections & Algebraic Identities (`T1a`) -/

def descartesQ (a b c d : Int) : Int :=
  (a + b + c + d) * (a + b + c + d) - 2 * (a * a + b * b + c * c + d * d)

structure Quad where
  a : Int
  b : Int
  c : Int
  d : Int
deriving DecidableEq, Repr

def Quad.descartes (q : Quad) : Int := descartesQ q.a q.b q.c q.d

def refl1 (q : Quad) : Quad := ⟨2 * (q.b + q.c + q.d) - q.a, q.b, q.c, q.d⟩
def refl2 (q : Quad) : Quad := ⟨q.a, 2 * (q.a + q.c + q.d) - q.b, q.c, q.d⟩
def refl3 (q : Quad) : Quad := ⟨q.a, q.b, 2 * (q.a + q.b + q.d) - q.c, q.d⟩
def refl4 (q : Quad) : Quad := ⟨q.a, q.b, q.c, 2 * (q.a + q.b + q.c) - q.d⟩

inductive InApollonianOrbit (root : Quad) : Quad → Prop
  | base : InApollonianOrbit root root
  | s1 {q} : InApollonianOrbit root q → InApollonianOrbit root (refl1 q)
  | s2 {q} : InApollonianOrbit root q → InApollonianOrbit root (refl2 q)
  | s3 {q} : InApollonianOrbit root q → InApollonianOrbit root (refl3 q)
  | s4 {q} : InApollonianOrbit root q → InApollonianOrbit root (refl4 q)

theorem refl_involutions_and_descartes (q : Quad) :
    refl1 (refl1 q) = q ∧ refl2 (refl2 q) = q ∧ refl3 (refl3 q) = q ∧ refl4 (refl4 q) = q ∧
    (refl1 q).descartes = q.descartes ∧ (refl2 q).descartes = q.descartes ∧
    (refl3 q).descartes = q.descartes ∧ (refl4 q).descartes = q.descartes := by
  cases q with
  | mk a b c d =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (simp only [refl1, refl2, refl3, refl4, Quad.descartes, descartesQ]; grind)

theorem descartes_sum_even {a b c d : Int} (hQ : descartesQ a b c d = 0) :
    (a + b + c - d) % 2 = 0 := by
  unfold descartesQ at hQ
  have hsq : (a + b + c + d) * (a + b + c + d) = 2 * (a * a + b * b + c * c + d * d) := by omega
  have hpar : (a + b + c + d) % 2 = 0 := by
    by_cases h0 : (a + b + c + d) % 2 = 0
    · exact h0
    · have h1 : (a + b + c + d) % 2 = 1 := by omega
      have hsq1 : ((a + b + c + d) * (a + b + c + d)) % 2 = 1 := by
        rw [Int.mul_emod, h1]; decide
      rw [hsq] at hsq1
      omega
  omega

def halfK (a b c d : Int) : Int := (a + b + c - d) / 2

theorem two_mul_halfK {a b c d : Int} (hQ : descartesQ a b c d = 0) :
    2 * halfK a b c d = a + b + c - d := by
  have hev := descartes_sum_even hQ
  unfold halfK; omega

theorem descartes_gaussian_norm {a b c d : Int} (hQ : descartesQ a b c d = 0) :
    (a + b) * (a + c) = a * a + halfK a b c d * halfK a b c d := by
  have h2k := two_mul_halfK hQ
  unfold descartesQ at hQ
  have h4 : 4 * ((a + b) * (a + c) - a * a) = (a + b + c - d) * (a + b + c - d) := by grind
  have h4k : 4 * (halfK a b c d * halfK a b c d) = (a + b + c - d) * (a + b + c - d) := by grind
  omega

theorem descartes_vieta_identities {a b c d : Int} (hQ : descartesQ a b c d = 0) :
    a * (2 * (b + c + d) - a) = (c - d) * (c - d) + b * b - 2 * b * (c + d) ∧
    4 * c * b = (c + b - d) * (c + b - d) - a * (2 * (b + c + d) - a) := by
  unfold descartesQ at hQ
  constructor <;> grind

def bqf (a b c d x y : Int) : Int :=
  (a + b) * x * x + 2 * halfK a b c d * x * y + (a + c) * y * y

theorem bqf_product_sum_two_squares {a b c d : Int} (hQ : descartesQ a b c d = 0)
    (x1 y1 x2 y2 : Int) :
    bqf a b c d x1 y1 * bqf a b c d x2 y2 =
    ((a + b) * x1 * x2 + halfK a b c d * (x1 * y2 + x2 * y1) + (a + c) * y1 * y2) ^ 2 +
    a * a * (x1 * y2 - x2 * y1) ^ 2 := by
  have hnorm := descartes_gaussian_norm hQ
  unfold bqf
  grind

theorem t1a_descartes_lorentzian_and_gaussian_norm :
    (∀ q : Quad, refl1 (refl1 q) = q ∧ refl2 (refl2 q) = q ∧ refl3 (refl3 q) = q ∧ refl4 (refl4 q) = q ∧
      (refl1 q).descartes = q.descartes ∧ (refl2 q).descartes = q.descartes ∧
      (refl3 q).descartes = q.descartes ∧ (refl4 q).descartes = q.descartes) ∧
    (∀ a b c d : Int, descartesQ a b c d = 0 →
      (a + b) * (a + c) = a * a + halfK a b c d * halfK a b c d) ∧
    (∀ a b c d x1 y1 x2 y2 : Int, descartesQ a b c d = 0 →
      bqf a b c d x1 y1 * bqf a b c d x2 y2 =
      ((a + b) * x1 * x2 + halfK a b c d * (x1 * y2 + x2 * y1) + (a + c) * y1 * y2) ^ 2 +
      a * a * (x1 * y2 - x2 * y1) ^ 2) :=
  ⟨refl_involutions_and_descartes,
   fun _ _ _ _ hQ => descartes_gaussian_norm hQ,
   fun _ _ _ _ x1 y1 x2 y2 hQ => bqf_product_sum_two_squares hQ x1 y1 x2 y2⟩

/-! ### Part 2: Constructive Quadratic CRT & Exact Parity / Odd-Part Arithmetic -/

def dedupNat : List Nat → List Nat
  | [] => []
  | x :: xs => if x ∈ xs then dedupNat xs else x :: dedupNat xs

theorem mem_dedupNat {x : Nat} {l : List Nat} : x ∈ dedupNat l ↔ x ∈ l := by
  induction l with
  | nil => simp [dedupNat]
  | cons y ys ih =>
    simp only [dedupNat]
    by_cases hy : y ∈ ys
    · simp only [hy, ↓reduceIte, ih, List.mem_cons]
      constructor
      · intro h; right; exact h
      · rintro (rfl | h); exact hy; exact h
    · simp only [hy, ↓reduceIte, List.mem_cons, ih]

theorem nodup_dedupNat (l : List Nat) : (dedupNat l).Nodup := by
  induction l with
  | nil => simp [dedupNat]
  | cons y ys ih =>
    simp only [dedupNat]
    by_cases hy : y ∈ ys
    · simp [hy, ih]
    · simp only [hy, ↓reduceIte, List.nodup_cons, mem_dedupNat]
      exact ⟨not_false, ih⟩

theorem sq_nonneg (a : Int) : 0 ≤ a * a := by
  by_cases h : 0 ≤ a
  · exact Int.mul_nonneg h h
  · have : a * a = (-a) * (-a) := by grind
    rw [this]; exact Int.mul_nonneg (by omega) (by omega)

theorem nat_dvd_natAbs_iff {p : Nat} {x : Int} : p ∣ x.natAbs ↔ (p : Int) ∣ x := by
  constructor
  · rintro ⟨k, hk⟩
    by_cases hx : 0 ≤ x
    · refine ⟨(k : Int), ?_⟩
      have hx' : (x.natAbs : Int) = x := by omega
      rw [← hx', hk, Int.natCast_mul]
    · refine ⟨-(k : Int), ?_⟩
      have hx' : (x.natAbs : Int) = -x := by omega
      have h2 : (p : Int) * (k : Int) = -x := by rw [← Int.natCast_mul, ← hk, hx']
      grind
  · rintro ⟨k, hk⟩
    exact ⟨k.natAbs, by rw [hk, Int.natAbs_mul, Int.natAbs_natCast]⟩

theorem coprime_two_left_of_odd {n : Nat} (h : n % 2 = 1) : Nat.Coprime 2 n := by
  change Nat.gcd 2 n = 1
  rw [Nat.gcd_rec, h]
  decide

theorem coprime_zero_left_eq {n : Nat} (h : Nat.Coprime 0 n) : n = 1 := by
  simpa [Nat.Coprime] using h

theorem int_prime_dvd_mul {p : Nat} (hp : IsPrime p) {x y : Int}
    (h : (p : Int) ∣ x * y) : (p : Int) ∣ x ∨ (p : Int) ∣ y := by
  have hd : p ∣ x.natAbs * y.natAbs := by
    have h1 : p ∣ (x * y).natAbs := nat_dvd_natAbs_iff.mpr h
    rw [Int.natAbs_mul] at h1; exact h1
  rcases prime_dvd_mul hp hd with hx | hy
  · left; exact nat_dvd_natAbs_iff.mp hx
  · right; exact nat_dvd_natAbs_iff.mp hy

/-- Strip all factors of `2` from a natural number (structural `Nat`-fueled). -/
def oddPartAux (n fuel : Nat) : Nat :=
  match fuel with
  | 0 => n
  | f + 1 => if n % 2 == 0 then oddPartAux (n / 2) f else n

def oddPart (n : Nat) : Nat := oddPartAux n n

def val2Aux (n fuel : Nat) : Nat :=
  match fuel with
  | 0 => 0
  | f + 1 => if n % 2 == 0 then 1 + val2Aux (n / 2) f else 0

def val2 (n : Nat) : Nat := val2Aux n n

theorem oddPartAux_spec (n fuel : Nat) (hn : 1 ≤ n) (hf : n ≤ fuel) :
    2 ^ (val2Aux n fuel) * oddPartAux n fuel = n ∧
    oddPartAux n fuel % 2 = 1 ∧ 1 ≤ oddPartAux n fuel := by
  induction fuel generalizing n with
  | zero => omega
  | succ f ih =>
    simp only [val2Aux, oddPartAux]
    by_cases hev : n % 2 = 0
    · have hbeq : (n % 2 == 0) = true := beq_iff_eq.mpr hev
      simp only [hbeq, ↓reduceIte]
      have hsub := ih (n / 2) (by omega) (by omega)
      refine ⟨?_, hsub.2.1, hsub.2.2⟩
      rw [Nat.add_comm 1, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 2, ← Nat.mul_assoc]
      have h2 : 2 * (2 ^ val2Aux (n / 2) f * oddPartAux (n / 2) f) = 2 * (n / 2) := by
        rw [hsub.1]
      omega
    · have hbeq : (n % 2 == 0) = false := beq_false_of_ne hev
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte, Nat.pow_zero, Nat.one_mul]
      exact ⟨trivial, by omega, hn⟩

theorem oddPart_spec {n : Nat} (hn : 1 ≤ n) :
    2 ^ (val2 n) * oddPart n = n ∧ oddPart n % 2 = 1 ∧ 1 ≤ oddPart n :=
  oddPartAux_spec n n hn (Nat.le_refl n)

/-- Constructive quadratic CRT avoiding any finite list of odd primes `ps` AND making the shift
    arbitrarily large (`n ≥ N0`)! -/
theorem exists_quad_avoid_primes_large (A B C : Int) (ps : List Nat) (N0 : Int)
    (hpr : ∀ p ∈ ps, IsPrime p)
    (hodd : ∀ p ∈ ps, p % 2 = 1)
    (hnondeg : ∀ p ∈ ps, ¬ ((p : Int) ∣ A ∧ (p : Int) ∣ B ∧ (p : Int) ∣ C)) :
    ∃ n : Int, N0 ≤ n ∧ ∀ p ∈ ps, ¬ (p : Int) ∣ (A * n * n + B * n + C) := by
  have hbase : ∀ ls : List Nat, ls.Nodup →
      (∀ p ∈ ls, IsPrime p) → (∀ p ∈ ls, p % 2 = 1) →
      (∀ p ∈ ls, ¬ ((p : Int) ∣ A ∧ (p : Int) ∣ B ∧ (p : Int) ∣ C)) →
      ∃ n : Int, ∀ p ∈ ls, ¬ (p : Int) ∣ (A * n * n + B * n + C) := by
    intro ls
    induction ls with
    | nil => intro _ _ _ _; exact ⟨0, fun _ h => nomatch h⟩
    | cons p qs ih =>
      intro hnd hpr' hodd' hnondeg'
      have hnd_p : p ∉ qs := (List.nodup_cons.mp hnd).1
      have hnd_qs : qs.Nodup := (List.nodup_cons.mp hnd).2
      have hp : IsPrime p := hpr' p List.mem_cons_self
      have hpo : p % 2 = 1 := hodd' p List.mem_cons_self
      have hqs_pr : ∀ q ∈ qs, IsPrime q := fun q hq => hpr' q (List.mem_cons_of_mem p hq)
      rcases ih hnd_qs hqs_pr
        (fun q hq => hodd' q (List.mem_cons_of_mem p hq))
        (fun q hq => hnondeg' q (List.mem_cons_of_mem p hq)) with ⟨n0, hn0⟩
      let M : Int := (listProd qs : Int)
      have hM_dvd : ∀ q ∈ qs, (q : Int) ∣ M := by
        intro q hq
        have her := listProd_erase hq
        exact ⟨(listProd (qs.erase q) : Int), by change (listProd qs : Int) = _; rw [← her, Int.natCast_mul]⟩
      have hp_not_M : ¬ (p : Int) ∣ M := fun hd =>
        hnd_p (prime_mem_of_dvd_listProd hp hqs_pr (Int.ofNat_dvd.mp hd))
      have hshift_ok : ∀ t : Int, ∀ q ∈ qs,
          ¬ (q : Int) ∣ (A * (n0 + t * M) * (n0 + t * M) + B * (n0 + t * M) + C) := by
        intro t q hq hd
        rcases hM_dvd q hq with ⟨k, hk⟩
        rcases hd with ⟨u, hu⟩
        apply hn0 q hq
        refine ⟨u - k * t * (2 * A * n0 + A * t * M + B), ?_⟩
        rw [hk] at hu; grind
      by_cases h0 : ¬ (p : Int) ∣ (A * n0 * n0 + B * n0 + C)
      · exact ⟨n0, fun q hq => by cases hq with | head => exact h0 | tail _ h => exact hn0 q h⟩
      · by_cases h1 : ¬ (p : Int) ∣ (A * (n0 + M) * (n0 + M) + B * (n0 + M) + C)
        · exact ⟨n0 + M, fun q hq => by
            cases hq with
            | head => exact h1
            | tail _ h => simpa using hshift_ok 1 q h⟩
        · refine ⟨n0 + 2 * M, fun q hq => ?_⟩
          cases hq with
          | head =>
            intro h2
            have hd0 : (p : Int) ∣ (A * n0 * n0 + B * n0 + C) := Classical.byContradiction h0
            have hd1 : (p : Int) ∣ (A * (n0 + M) * (n0 + M) + B * (n0 + M) + C) := Classical.byContradiction h1
            rcases hd0 with ⟨u0, hu0⟩
            rcases hd1 with ⟨u1, hu1⟩
            rcases h2 with ⟨u2, hu2⟩
            have h2AM2 : (p : Int) ∣ (2 * A) * (M * M) := ⟨u2 - 2 * u1 + u0, by grind⟩
            have hdA : (p : Int) ∣ A := by
              rcases int_prime_dvd_mul hp h2AM2 with h2A | hM2
              · rcases int_prime_dvd_mul hp h2A with h2p | hAp
                · exfalso
                  have h2n : p ∣ 2 := Int.ofNat_dvd.mp h2p
                  have hle := Nat.le_of_dvd (by decide) h2n
                  have hp2 := hp.1; omega
                · exact hAp
              · exfalso; rcases int_prime_dvd_mul hp hM2 with hM1 | hM1 <;> exact hp_not_M hM1
            have hdB : (p : Int) ∣ B := by
              rcases hdA with ⟨uA, huA⟩
              have hBM : (p : Int) ∣ B * M :=
                ⟨u1 - u0 - uA * (2 * n0 * M + M * M), by grind⟩
              exact (int_prime_dvd_mul hp hBM).elim id (fun hm => False.elim (hp_not_M hm))
            have hdC : (p : Int) ∣ C := by
              rcases hdA with ⟨uA, huA⟩; rcases hdB with ⟨uB, huB⟩
              exact ⟨u0 - uA * n0 * n0 - uB * n0, by grind⟩
            exact hnondeg' p List.mem_cons_self ⟨hdA, hdB, hdC⟩
          | tail _ h => exact hshift_ok 2 q h
  let ls := dedupNat ps
  have hls_pr : ∀ p ∈ ls, IsPrime p := fun p hp => hpr p (mem_dedupNat.mp hp)
  rcases hbase ls (nodup_dedupNat ps) hls_pr
    (fun p hp => hodd p (mem_dedupNat.mp hp))
    (fun p hp => hnondeg p (mem_dedupNat.mp hp)) with ⟨n0, hn0⟩
  let M : Int := (listProd ls : Int)
  have hM_pos : 1 ≤ M := by
    have := listProd_pos_of_primes hls_pr; omega
  -- Shift n0 up by a nonnegative multiple of M so N0 ≤ n!
  let K : Int := if N0 ≤ n0 then 0 else N0 - n0
  have hK0 : 0 ≤ K := by dsimp [K]; split <;> omega
  have hN0_le : N0 ≤ n0 + K * M := by
    have hKM : K ≤ K * M := by
      have : K * (M - 1) ≥ 0 := Int.mul_nonneg hK0 (by omega)
      grind
    by_cases hle : N0 ≤ n0
    · simp only [K, hle, ↓reduceIte] at hKM ⊢; omega
    · simp only [K, hle, ↓reduceIte] at hKM ⊢; omega
  refine ⟨n0 + K * M, hN0_le, ?_⟩
  intro p hp
  have hp' : p ∈ ls := mem_dedupNat.mpr hp
  have hMp : (p : Int) ∣ M := by
    have her := listProd_erase hp'
    exact ⟨(listProd (ls.erase p) : Int), by change (listProd ls : Int) = _; rw [← her, Int.natCast_mul]⟩
  intro hd
  rcases hMp with ⟨k, hk⟩; rcases hd with ⟨u, hu⟩
  apply hn0 p hp'
  refine ⟨u - k * K * (2 * A * n0 + A * K * M + B), ?_⟩
  rw [hk] at hu; grind

theorem coprime_of_avoid_primeFactors {x : Int} {m : Nat} (hm : 1 ≤ m)
    (havoid : ∀ p ∈ primeFactors m, ¬ (p : Int) ∣ x) :
    Nat.Coprime x.natAbs m := by
  by_cases hg : Nat.gcd x.natAbs m = 1
  · exact hg
  · exfalso
    have hg_pos : 1 ≤ Nat.gcd x.natAbs m := by
      by_cases h0 : Nat.gcd x.natAbs m = 0
      · have := Nat.gcd_eq_zero_iff.mp h0; omega
      · omega
    have hg2 : 2 ≤ Nat.gcd x.natAbs m := by omega
    let p := smallestFactor (Nat.gcd x.natAbs m)
    have hp : IsPrime p := smallestFactor_isPrime hg2
    have hpg : p ∣ Nat.gcd x.natAbs m := smallestFactor_dvd hg2
    have hpx : p ∣ x.natAbs := Nat.dvd_trans hpg (Nat.gcd_dvd_left _ _)
    have hpm : p ∣ m := Nat.dvd_trans hpg (Nat.gcd_dvd_right _ _)
    have hspec := primeFactors_spec hm
    have hpmem : p ∈ primeFactors m :=
      prime_mem_of_dvd_listProd hp hspec.2 (by rw [hspec.1]; exact hpm)
    exact havoid p hpmem (nat_dvd_natAbs_iff.mp hpx)

/-! ### Part 3: The HKRS Apollonian Quadratic Reciprocity Obstruction (`T1c`) -/

/-- A primitive Descartes quadruple of the 4-even type:
    `a ≡ 1 (mod 4)`, `b ≡ 1 (mod 4)`, `c ≡ 0 (mod 4)`, `d ≡ 0 (mod 4)` (up to slot order:
    we keep `(o1, o2)` in slots `(a, b)` and `(e1, e2)` in slots `(c, d)`, which ALL 4 reflections preserve!). -/
def Is4EvenPrim (q : Quad) : Prop :=
  q.descartes = 0 ∧
  q.a % 4 = 1 ∧ q.b % 4 = 1 ∧ q.c % 4 = 0 ∧ q.d % 4 = 0 ∧
  0 < q.a + q.b ∧ 0 < q.a + q.c ∧ 0 < q.a + q.d ∧
  0 < q.b + q.c ∧ 0 < q.b + q.d ∧ 0 < q.c + q.d ∧
  (∀ p : Nat, IsPrime p → ¬ ((p : Int) ∣ q.a ∧ (p : Int) ∣ q.b ∧ (p : Int) ∣ q.c ∧ (p : Int) ∣ q.d))

theorem bqf_odd_mod4_and_mod8_odd_circle {o1 o2 e1 e2 : Int}
    (hQ : descartesQ o1 o2 e1 e2 = 0)
    (ho1 : o1 % 4 = 1) (ho2 : o2 % 4 = 1) (he1 : e1 % 4 = 0) (he2 : e2 % 4 = 0)
    (x y : Int) (hodd : bqf o1 e1 e2 o2 x y % 2 = 1) :
    bqf o1 e1 e2 o2 x y % 4 = 1 := by
  have hQ' : descartesQ o1 e1 e2 o2 = 0 := by unfold descartesQ at hQ ⊢; grind
  have h2k := two_mul_halfK hQ'
  have hk_ev : halfK o1 e1 e2 o2 % 2 = 0 := by omega
  unfold bqf at hodd ⊢
  have h1 : (o1 + e1) % 4 = 1 := by omega
  have h2 : (o1 + e2) % 4 = 1 := by omega
  have hx2 : (x * x) % 4 = 0 ∨ (x * x) % 4 = 1 := by
    have hx4 : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
    rcases hx4 with h | h | h | h <;> (rw [Int.mul_emod, h]; decide)
  have hy2 : (y * y) % 4 = 0 ∨ (y * y) % 4 = 1 := by
    have hy4 : y % 4 = 0 ∨ y % 4 = 1 ∨ y % 4 = 2 ∨ y % 4 = 3 := by omega
    rcases hy4 with h | h | h | h <;> (rw [Int.mul_emod, h]; decide)
  have h4k : (2 * halfK o1 e1 e2 o2 * x * y) % 4 = 0 := by
    have : (2 * halfK o1 e1 e2 o2) % 4 = 0 := by omega
    rw [Int.mul_emod, Int.mul_emod (2 * halfK o1 e1 e2 o2), this]; simp
  have hm1 : ((o1 + e1) * x * x) % 4 = (x * x) % 4 := by
    rw [Int.mul_assoc, Int.mul_emod, h1, Int.one_mul, Int.emod_emod]
  have hm2 : ((o1 + e2) * y * y) % 4 = (y * y) % 4 := by
    rw [Int.mul_assoc, Int.mul_emod, h2, Int.one_mul, Int.emod_emod]
  have hsum : ((o1 + e1) * x * x + 2 * halfK o1 e1 e2 o2 * x * y + (o1 + e2) * y * y) % 4 =
      (((x * x) % 4) + ((y * y) % 4)) % 4 := by
    rw [Int.add_emod, Int.add_emod ((o1 + e1) * x * x), hm1, h4k, hm2]
    omega
  omega

/-- For an EVEN circle `e1 ≡ 0 (mod 4)` in a 4-even quadruple `(o1, o2, e1, e2)`:
    ALL odd values of `bqf e1 o1 o2 e2 x y` share the EXACT SAME residue modulo `8`
    (namely `(e1 + o1) % 8`, which is `1` or `5`)! -/
theorem bqf_odd_mod8_even_circle {e1 o1 o2 e2 : Int}
    (hQ : descartesQ e1 o1 o2 e2 = 0)
    (he1 : e1 % 4 = 0) (he2 : e2 % 4 = 0) (ho1 : o1 % 4 = 1) (ho2 : o2 % 4 = 1)
    (x y : Int) (hodd : bqf e1 o1 o2 e2 x y % 2 = 1) :
    bqf e1 o1 o2 e2 x y % 8 = (e1 + o1) % 8 ∧ bqf e1 o1 o2 e2 x y % 4 = 1 := by
  have h2k := two_mul_halfK (a := e1) (b := o1) (c := o2) (d := e2) hQ
  have hnorm := descartes_gaussian_norm hQ
  have hk_odd : halfK e1 o1 o2 e2 % 2 = 1 := by omega
  have heq8 : (e1 + o1) % 8 = (e1 + o2) % 8 := by
    have hprod8 : ((e1 + o1) * (e1 + o2)) % 8 = 1 := by
      have he1sq : (e1 * e1) % 8 = 0 := by
        have : e1 = 4 * (e1 / 4) := by omega
        rw [this]; grind
      have hksq : (halfK e1 o1 o2 e2 * halfK e1 o1 o2 e2) % 8 = 1 := by
        have hk8 : halfK e1 o1 o2 e2 % 8 = 1 ∨ halfK e1 o1 o2 e2 % 8 = 3 ∨
                   halfK e1 o1 o2 e2 % 8 = 5 ∨ halfK e1 o1 o2 e2 % 8 = 7 := by omega
        rcases hk8 with h | h | h | h <;> (rw [Int.mul_emod, h]; decide)
      rw [hnorm, Int.add_emod, he1sq, hksq]; decide
    have h1 : (e1 + o1) % 8 = 1 ∨ (e1 + o1) % 8 = 5 := by omega
    have h2 : (e1 + o2) % 8 = 1 ∨ (e1 + o2) % 8 = 5 := by omega
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · omega
    · rw [Int.mul_emod, h1, h2] at hprod8; simp at hprod8
    · rw [Int.mul_emod, h1, h2] at hprod8; simp at hprod8
    · omega
  unfold bqf at hodd ⊢
  let a1 := e1 + o1
  let a2 := e1 + o2
  let k := halfK e1 o1 o2 e2
  have ha1_eq : a1 = 8 * (a1 / 8) + a1 % 8 := by omega
  have ha2_eq : a2 = 8 * (a2 / 8) + a1 % 8 := by dsimp [a1, a2] at heq8 ⊢; omega
  have hk_eq : k = 4 * (k / 4) + k % 4 := by omega
  have hx_eq : x = 4 * (x / 4) + x % 4 := by omega
  have hy_eq : y = 4 * (y / 4) + y % 4 := by omega
  have hmod8 : (a1 * x * x + 2 * k * x * y + a2 * y * y) % 8 =
      ((a1 % 8) * (x % 4) * (x % 4) + 2 * (k % 4) * (x % 4) * (y % 4) +
       (a1 % 8) * (y % 4) * (y % 4)) % 8 := by
    have hdiff : (a1 * x * x + 2 * k * x * y + a2 * y * y) -
        ((a1 % 8) * (x % 4) * (x % 4) + 2 * (k % 4) * (x % 4) * (y % 4) +
         (a1 % 8) * (y % 4) * (y % 4)) =
        8 * (
          (a1 / 8) * x * x + (a2 / 8) * y * y +
          (a1 % 8) * (2 * (x / 4) * (x / 4) + (x / 4) * (x % 4)) +
          (a1 % 8) * (2 * (y / 4) * (y / 4) + (y / 4) * (y % 4)) +
          (k / 4) * x * y + (k % 4) * (4 * (x / 4) * (y / 4) + (x / 4) * (y % 4) + (y / 4) * (x % 4))
        ) := by grind
    have hrepr : a1 * x * x + 2 * k * x * y + a2 * y * y =
        8 * (
          (a1 / 8) * x * x + (a2 / 8) * y * y +
          (a1 % 8) * (2 * (x / 4) * (x / 4) + (x / 4) * (x % 4)) +
          (a1 % 8) * (2 * (y / 4) * (y / 4) + (y / 4) * (y % 4)) +
          (k / 4) * x * y + (k % 4) * (4 * (x / 4) * (y / 4) + (x / 4) * (y % 4) + (y / 4) * (x % 4))
        ) + ((a1 % 8) * (x % 4) * (x % 4) + 2 * (k % 4) * (x % 4) * (y % 4) +
             (a1 % 8) * (y % 4) * (y % 4)) := by omega
    rw [hrepr, Int.mul_add_emod_self_left]
  have ha8 : a1 % 8 = 1 ∨ a1 % 8 = 5 := by dsimp [a1]; omega
  have hk4 : k % 4 = 1 ∨ k % 4 = 3 := by dsimp [k]; omega
  have hx4 : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
  have hy4 : y % 4 = 0 ∨ y % 4 = 1 ∨ y % 4 = 2 ∨ y % 4 = 3 := by omega
  have hodd8 : (((a1 % 8) * (x % 4) * (x % 4) + 2 * (k % 4) * (x % 4) * (y % 4) +
                 (a1 % 8) * (y % 4) * (y % 4)) % 8) % 2 = 1 := by
    rw [← hmod8]
    have h82 : ((a1 * x * x + 2 * k * x * y + a2 * y * y) % 8) % 2 =
               (a1 * x * x + 2 * k * x * y + a2 * y * y) % 2 :=
      Int.emod_emod_of_dvd _ ⟨4, by decide⟩
    rw [h82]; exact hodd
  have hres8 : (a1 * x * x + 2 * k * x * y + a2 * y * y) % 8 = a1 % 8 := by
    rw [hmod8]
    rcases ha8 with ha8 | ha8 <;> rcases hk4 with hk4 | hk4 <;>
    rcases hx4 with hx4 | hx4 | hx4 | hx4 <;> rcases hy4 with hy4 | hy4 | hy4 | hy4 <;>
      (rw [ha8, hk4, hx4, hy4] at hodd8 ⊢; revert hodd8; decide)
  refine ⟨hres8, ?_⟩
  have h84 : ((a1 * x * x + 2 * k * x * y + a2 * y * y) % 8) % 4 =
             (a1 * x * x + 2 * k * x * y + a2 * y * y) % 4 :=
    Int.emod_emod_of_dvd _ ⟨2, by decide⟩
  rw [← h84, hres8]
  dsimp [a1]; omega

/-- **Form-Invariance Lemma:** For ANY circle `u` in a `4`-even Descartes quadruple (whether `u` is
    odd or even!), `jacobi u t1 = jacobi u t2` for ALL odd positive `t1 = bqf u ... x1 y1` and
    `t2 = bqf u ... x2 y2` coprime to `u`! -/
theorem jacobi_bqf_invariant {u v w z : Int} (hQ : descartesQ u v w z = 0)
    (h4 : (u % 4 = 1 ∧ v % 4 = 0 ∧ w % 4 = 0 ∧ z % 4 = 1) ∨
          (u % 4 = 0 ∧ v % 4 = 1 ∧ w % 4 = 1 ∧ z % 4 = 0))
    {x1 y1 x2 y2 : Int}
    (ht1_pos : 0 < bqf u v w z x1 y1) (ht1_odd : bqf u v w z x1 y1 % 2 = 1)
    (ht1_cop : Nat.Coprime u.natAbs (bqf u v w z x1 y1).toNat)
    (ht2_pos : 0 < bqf u v w z x2 y2) (ht2_odd : bqf u v w z x2 y2 % 2 = 1)
    (ht2_cop : Nat.Coprime u.natAbs (bqf u v w z x2 y2).toNat) :
    jacobi u (bqf u v w z x1 y1).toNat = jacobi u (bqf u v w z x2 y2).toNat := by
  let t1 := (bqf u v w z x1 y1).toNat
  let t2 := (bqf u v w z x2 y2).toNat
  by_cases hu0 : u = 0
  · subst hu0
    have h1 : t1 = 1 := coprime_zero_left_eq ht1_cop
    have h2 : t2 = 1 := coprime_zero_left_eq ht2_cop
    change jacobi 0 t1 = jacobi 0 t2
    rw [h1, h2]
  · have ht1_eq : (t1 : Int) = bqf u v w z x1 y1 := Int.toNat_of_nonneg (by omega)
    have ht2_eq : (t2 : Int) = bqf u v w z x2 y2 := Int.toNat_of_nonneg (by omega)
    have ht1_ge1 : 1 ≤ t1 := by omega
    have ht2_ge1 : 1 ≤ t2 := by omega
    have ht1_o : t1 % 2 = 1 := by omega
    have ht2_o : t2 % 2 = 1 := by omega
    have ht12_ge1 : 1 ≤ t1 * t2 := Nat.mul_pos ht1_ge1 ht2_ge1
    have ht12_o : (t1 * t2) % 2 = 1 := by rw [Nat.mul_mod, ht1_o, ht2_o]
    have hprod := bqf_product_sum_two_squares hQ x1 y1 x2 y2
    let W : Int := (u + v) * x1 * x2 + halfK u v w z * (x1 * y2 + x2 * y1) + (u + w) * y1 * y2
    let Z : Int := x1 * y2 - x2 * y1
    have hprod' : ((t1 * t2 : Nat) : Int) = W * W + u * u * (Z * Z) := by
      rw [Int.natCast_mul, ht1_eq, ht2_eq, hprod]; grind
    have hpm1 := jacobi_pm1_of_coprime ht1_ge1 ht1_o ht1_cop
    have hpm2 := jacobi_pm1_of_coprime ht2_ge1 ht2_o ht2_cop
    suffices hmul1 : jacobi u (t1 * t2) = 1 by
      rw [jacobi_mul_right u ht1_ge1 ht2_ge1] at hmul1
      change jacobi u t1 = jacobi u t2
      rcases hpm1 with h1 | h1 <;> rcases hpm2 with h2 | h2 <;> simp [h1, h2] at hmul1 ⊢
    have hu_pos : 1 ≤ u.natAbs := by omega
    have hop := oddPart_spec hu_pos
    let m := oddPart u.natAbs
    let e := val2 u.natAbs
    have hm1 : 1 ≤ m := hop.2.2
    have hmo : m % 2 = 1 := hop.2.1
    have ht12_4 : (t1 * t2) % 4 = 1 ∧ (t1 % 4 = 1 ∧ t2 % 4 = 1) := by
      rcases h4 with ⟨hu4, hv4, hw4, hz4⟩ | ⟨hu4, hv4, hw4, hz4⟩
      · have hQ_uz : descartesQ u z v w = 0 := by unfold descartesQ at hQ ⊢; grind
        have h1 := bqf_odd_mod4_and_mod8_odd_circle hQ_uz hu4 hz4 hv4 hw4 x1 y1 ht1_odd
        have h2 := bqf_odd_mod4_and_mod8_odd_circle hQ_uz hu4 hz4 hv4 hw4 x2 y2 ht2_odd
        have ht14 : t1 % 4 = 1 := by omega
        have ht24 : t2 % 4 = 1 := by omega
        have hm4 : (t1 * t2) % 4 = 1 := by rw [Nat.mul_mod, ht14, ht24]
        exact ⟨hm4, ht14, ht24⟩
      · have h1 := (bqf_odd_mod8_even_circle hQ hu4 hz4 hv4 hw4 x1 y1 ht1_odd).2
        have h2 := (bqf_odd_mod8_even_circle hQ hu4 hz4 hv4 hw4 x2 y2 ht2_odd).2
        have ht14 : t1 % 4 = 1 := by omega
        have ht24 : t2 % 4 = 1 := by omega
        have hm4 : (t1 * t2) % 4 = 1 := by rw [Nat.mul_mod, ht14, ht24]
        exact ⟨hm4, ht14, ht24⟩
    have h2pow : jacobi ((2 ^ e : Nat) : Int) (t1 * t2) = 1 := by
      rcases h4 with ⟨hu4, _, _, _⟩ | ⟨hu4, hv4, hw4, hz4⟩
      · have he0 : e = 0 := by
          by_cases h0 : e = 0
          · exact h0
          · exfalso
            have h2dvd : 2 ∣ u.natAbs := by
              rw [← hop.1]
              change 2 ∣ 2 ^ e * m
              cases he : e with
              | zero => exact absurd he h0
              | succ k => rw [Nat.pow_succ]; exact ⟨2 ^ k * m, by grind⟩
            omega
        rw [he0, Nat.pow_zero, jacobi_ofNat 1 ht12_ge1, jacobiNat_one _ ht12_ge1]
      · have h1 := (bqf_odd_mod8_even_circle hQ hu4 hz4 hv4 hw4 x1 y1 ht1_odd).1
        have h2 := (bqf_odd_mod8_even_circle hQ hu4 hz4 hv4 hw4 x2 y2 ht2_odd).1
        have ht12_8 : (t1 * t2) % 8 = 1 := by
          have hmul8 : (t1 * t2) % 8 = ((t1 % 8) * (t2 % 8)) % 8 := Nat.mul_mod t1 t2 8
          have ht18 : t1 % 8 = 1 ∨ t1 % 8 = 5 := by omega
          have ht28 : t2 % 8 = t1 % 8 := by omega
          rcases ht18 with h | h <;> rw [hmul8, ht28, h] <;> decide
        have hj2 : jacobi 2 (t1 * t2) = 1 := by
          rw [jacobi_two ht12_ge1 ht12_o]; unfold signTwo; simp [ht12_8]
        clear hop
        induction e with
        | zero => rw [Nat.pow_zero, jacobi_ofNat 1 ht12_ge1, jacobiNat_one _ ht12_ge1]
        | succ k ihk =>
          rw [Nat.pow_succ, Int.natCast_mul, jacobi_mul_left ht12_ge1 ht12_o, ihk, Int.one_mul]
          exact hj2
    have hm_dvd_u : (m : Int) ∣ u := by
      have hd : m ∣ u.natAbs := ⟨2 ^ e, by rw [Nat.mul_comm]; exact hop.1.symm⟩
      exact nat_dvd_natAbs_iff.mp hd
    have hcop_m : Nat.Coprime m (t1 * t2) := by
      have hcop_u : Nat.Coprime u.natAbs (t1 * t2) := Nat.Coprime.mul_right ht1_cop ht2_cop
      rw [← hop.1] at hcop_u
      exact (Nat.coprime_mul_iff_left.mp hcop_u).2
    have hjm : jacobi (m : Int) (t1 * t2) = 1 := by
      have hqr := jacobiNat_quadratic_reciprocity hm1 ht12_ge1 hmo ht12_o hcop_m
      have hsq_sign : signQR m (t1 * t2) = 1 := by
        unfold signQR; have : ((t1 * t2) % 4 == 3) = false := beq_false_of_ne (by omega)
        simp [this]
      rw [hsq_sign] at hqr
      have hj_t12_m : jacobiNat (t1 * t2) m = 1 := by
        rw [← jacobi_ofNat (t1 * t2) hm1]
        have hmod_m : ((t1 * t2 : Nat) : Int) % (m : Int) = (W * W) % (m : Int) := by
          rcases hm_dvd_u with ⟨q, hq⟩
          rw [hprod', hq]
          have : W * W + (m : Int) * q * ((m : Int) * q) * (Z * Z) =
                 W * W + (m : Int) * (q * (m : Int) * q * (Z * Z)) := by grind
          rw [this, Int.add_mul_emod_self_left]
        rw [jacobi_eq_of_mod_eq hm1 hmod_m]
        have hcop_W : Nat.Coprime W.natAbs m := by
          apply coprime_of_avoid_primeFactors hm1
          intro p hp hdW
          have hspec := primeFactors_spec hm1
          have hpm : p ∣ m := by have her := listProd_erase hp; rw [hspec.1] at her; exact ⟨_, her.symm⟩
          have hpu : (p : Int) ∣ u := Int.dvd_trans (Int.ofNat_dvd.mpr hpm) hm_dvd_u
          have hpt : (p : Int) ∣ ((t1 * t2 : Nat) : Int) := by
            rw [hprod']
            rcases hdW with ⟨w1, hw1⟩; rcases hpu with ⟨u1, hu1⟩
            exact ⟨w1 * W + u1 * u * (Z * Z), by grind⟩
          have hpt' : p ∣ t1 * t2 := Int.ofNat_dvd.mp hpt
          have hg : p ∣ Nat.gcd m (t1 * t2) := Nat.dvd_gcd hpm hpt'
          rw [hcop_m] at hg
          have := Nat.le_of_dvd (by decide) hg
          have := (hspec.2 p hp).1
          omega
        exact jacobi_sq hm1 hmo hcop_W
      rw [jacobi_ofNat m ht12_ge1]
      rw [hj_t12_m, Int.mul_one] at hqr
      exact hqr
    have hsign_u : jacobi (if u < 0 then -1 else 1) (t1 * t2) = 1 := by
      split
      · rw [jacobi_neg_one ht12_ge1 ht12_o]; unfold signNeg1; simp [ht12_4.1]
      · change jacobi ((1 : Nat) : Int) (t1 * t2) = 1
        rw [jacobi_ofNat 1 ht12_ge1, jacobiNat_one _ ht12_ge1]
    have hu_fac : u = (if u < 0 then -1 else 1) * (((2 ^ e : Nat) : Int) * (m : Int)) := by
      have hnat : ((2 ^ e : Nat) : Int) * (m : Int) = (u.natAbs : Int) := by
        rw [← Int.natCast_mul, hop.1]
      rw [hnat]
      split <;> omega
    rw [hu_fac, jacobi_mul_left ht12_ge1 ht12_o, jacobi_mul_left ht12_ge1 ht12_o,
        hsign_u, h2pow, hjm]
    decide

/-- **The Global HKRS Obstruction Invariant** on a 4-even primitive quadruple `(o1, o2, e1, e2)`:
    For EVERY circle slot and EVERY odd positive coprime value of its BQF, `jacobi = -1`! -/
def HasHKRSObstruction (q : Quad) : Prop :=
  Is4EvenPrim q ∧
  (∀ x y : Int, 0 < bqf q.a q.c q.d q.b x y → bqf q.a q.c q.d q.b x y % 2 = 1 →
    Nat.Coprime q.a.natAbs (bqf q.a q.c q.d q.b x y).toNat →
    jacobi q.a (bqf q.a q.c q.d q.b x y).toNat = -1) ∧
  (∀ x y : Int, 0 < bqf q.b q.c q.d q.a x y → bqf q.b q.c q.d q.a x y % 2 = 1 →
    Nat.Coprime q.b.natAbs (bqf q.b q.c q.d q.a x y).toNat →
    jacobi q.b (bqf q.b q.c q.d q.a x y).toNat = -1) ∧
  (∀ x y : Int, 0 < bqf q.c q.a q.b q.d x y → bqf q.c q.a q.b q.d x y % 2 = 1 →
    Nat.Coprime q.c.natAbs (bqf q.c q.a q.b q.d x y).toNat →
    jacobi q.c (bqf q.c q.a q.b q.d x y).toNat = -1) ∧
  (∀ x y : Int, 0 < bqf q.d q.a q.b q.c x y → bqf q.d q.a q.b q.c x y % 2 = 1 →
    Nat.Coprime q.d.natAbs (bqf q.d q.a q.b q.c x y).toNat →
    jacobi q.d (bqf q.d q.a q.b q.c x y).toNat = -1)

/-- Helper: symmetry of `descartesQ` under permutations. -/
theorem descartesQ_perm (a b c d : Int) :
    descartesQ a b c d = descartesQ a c d b ∧
    descartesQ a b c d = descartesQ b c d a ∧
    descartesQ a b c d = descartesQ c a b d ∧
    descartesQ a b c d = descartesQ d a b c := by
  unfold descartesQ; refine ⟨by grind, by grind, by grind, by grind⟩

/-- Helper: primitivity preserved by all 4 reflections. -/
theorem prim_refl1 {q : Quad}
    (hprim : ∀ p : Nat, IsPrime p → ¬ ((p : Int) ∣ q.a ∧ (p : Int) ∣ q.b ∧ (p : Int) ∣ q.c ∧ (p : Int) ∣ q.d)) :
    ∀ p : Nat, IsPrime p →
      ¬ ((p : Int) ∣ (refl1 q).a ∧ (p : Int) ∣ (refl1 q).b ∧ (p : Int) ∣ (refl1 q).c ∧ (p : Int) ∣ (refl1 q).d) := by
  intro p hp ⟨ha', hb, hc, hd⟩
  apply hprim p hp
  refine ⟨?_, hb, hc, hd⟩
  rcases ha' with ⟨ua, hua⟩; rcases hb with ⟨ub, hub⟩; rcases hc with ⟨uc, huc⟩; rcases hd with ⟨ud, hud⟩
  exact ⟨2 * (ub + uc + ud) - ua, by simp only [refl1] at hua hub huc hud; grind⟩

/-- Helper: BQF coprime existence for ANY circle `u` in a `4`-even primitive quadruple! -/
theorem exists_bqf_witness {u v w z : Int} (hQ : descartesQ u v w z = 0)
    (huv : 0 < u + v) (_huw : 0 < u + w)
    (huv_odd : (u + v) % 2 = 1) (hu_ne : u ≠ 0)
    (hprim : ∀ p : Nat, IsPrime p → ¬ ((p : Int) ∣ u ∧ (p : Int) ∣ v ∧ (p : Int) ∣ w ∧ (p : Int) ∣ z)) :
    ∃ x y : Int, 0 < bqf u v w z x y ∧ bqf u v w z x y % 2 = 1 ∧
      Nat.Coprime u.natAbs (bqf u v w z x y).toNat := by
  have hu_pos : 1 ≤ u.natAbs := by omega
  have hop := oddPart_spec hu_pos
  let m := oddPart u.natAbs
  have hm1 : 1 ≤ m := hop.2.2
  have hmo : m % 2 = 1 := hop.2.1
  -- Set x = 2*r + 1, y = 2: bqf(2r+1, 2) = 4(u+v) r^2 + (4(u+v) + 8k) r + ((u+v) + 4k + 4(u+w))!
  let A : Int := 4 * (u + v)
  let B : Int := 4 * (u + v) + 8 * halfK u v w z
  let C : Int := (u + v) + 4 * halfK u v w z + 4 * (u + w)
  have hspec := primeFactors_spec hm1
  have hodd_ps : ∀ p ∈ primeFactors m, p % 2 = 1 :=
    odd_mem_of_odd_listProd (by rw [hspec.1]; exact hmo)
  have hnondeg : ∀ p ∈ primeFactors m, ¬ ((p : Int) ∣ A ∧ (p : Int) ∣ B ∧ (p : Int) ∣ C) := by
    intro p hp_mem ⟨hdA, hdB, hdC⟩
    have hp := hspec.2 p hp_mem
    have hpo := hodd_ps p hp_mem
    have hnd2 : ¬ (p : Int) ∣ 2 := fun h => by
      have h2n : p ∣ 2 := Int.ofNat_dvd.mp h
      have hle := Nat.le_of_dvd (by decide) h2n; have hp2 := hp.1; omega
    have hnd4 : ¬ (p : Int) ∣ 4 := fun h => (int_prime_dvd_mul hp (by simpa using h)).elim hnd2 hnd2
    have hnd8 : ¬ (p : Int) ∣ 8 := fun h => (int_prime_dvd_mul hp (by change (p : Int) ∣ 2 * 4 at h; exact h)).elim hnd2 hnd4
    have hd_uv : (p : Int) ∣ (u + v) := (int_prime_dvd_mul hp hdA).elim (fun h => False.elim (hnd4 h)) id
    have hd_8k : (p : Int) ∣ 8 * halfK u v w z := by
      rcases hdA with ⟨u1, hu1⟩; rcases hdB with ⟨u2, hu2⟩
      exact ⟨u2 - u1, by change 8 * halfK u v w z = _; grind⟩
    have hdk : (p : Int) ∣ halfK u v w z := (int_prime_dvd_mul hp hd_8k).elim (fun h => False.elim (hnd8 h)) id
    have hd_4uw : (p : Int) ∣ 4 * (u + w) := by
      rcases hd_uv with ⟨u1, hu1⟩; rcases hdk with ⟨u2, hu2⟩; rcases hdC with ⟨u3, hu3⟩
      exact ⟨u3 - u1 - 4 * u2, by change 4 * (u + w) = _; grind⟩
    have hd_uw : (p : Int) ∣ (u + w) := (int_prime_dvd_mul hp hd_4uw).elim (fun h => False.elim (hnd4 h)) id
    have hnorm := descartes_gaussian_norm hQ
    have hd_u2 : (p : Int) ∣ u * u := by
      rcases hd_uv with ⟨u1, hu1⟩; rcases hdk with ⟨u2, hu2⟩
      exact ⟨u1 * (u + w) - u2 * halfK u v w z, by grind⟩
    have hd_u : (p : Int) ∣ u := (int_prime_dvd_mul hp hd_u2).elim id id
    have hd_v : (p : Int) ∣ v := by
      rcases hd_uv with ⟨u1, hu1⟩; rcases hd_u with ⟨u2, hu2⟩; exact ⟨u1 - u2, by grind⟩
    have hd_w : (p : Int) ∣ w := by
      rcases hd_uw with ⟨u1, hu1⟩; rcases hd_u with ⟨u2, hu2⟩; exact ⟨u1 - u2, by grind⟩
    have h2k := two_mul_halfK hQ
    have hd_z : (p : Int) ∣ z := by
      rcases hd_u with ⟨ua, hua⟩; rcases hd_v with ⟨ub, hub⟩; rcases hd_w with ⟨uc, huc⟩
      rcases hdk with ⟨uk, huk⟩; exact ⟨ua + ub + uc - 2 * uk, by grind⟩
    exact hprim p hp ⟨hd_u, hd_v, hd_w, hd_z⟩
  rcases exists_quad_avoid_primes_large A B C (primeFactors m) 0 hspec.2 hodd_ps hnondeg with ⟨r, _, hravoid⟩
  refine ⟨2 * r + 1, 2, ?_, ?_, ?_⟩
  · -- Strictly positive via (u + v) * bqf(x, 2) = ((u+v)x + 2k)^2 + 4*u^2 ≥ 4 > 0!
    have hnorm := descartes_gaussian_norm hQ
    have hmul : (u + v) * bqf u v w z (2 * r + 1) 2 =
                ((u + v) * (2 * r + 1) + 2 * halfK u v w z) ^ 2 + 4 * (u * u) := by
      unfold bqf; grind
    have hu2 : 1 ≤ u * u := by
      by_cases h : 0 < u
      · exact Int.mul_pos h h
      · have hneg : 0 < -u := by omega
        have : u * u = (-u) * (-u) := by grind
        rw [this]; exact Int.mul_pos hneg hneg
    have hsq0 : 0 ≤ ((u + v) * (2 * r + 1) + 2 * halfK u v w z) ^ 2 := by
      have : ((u + v) * (2 * r + 1) + 2 * halfK u v w z) ^ 2 =
             ((u + v) * (2 * r + 1) + 2 * halfK u v w z) * ((u + v) * (2 * r + 1) + 2 * halfK u v w z) := by grind
      rw [this]; exact sq_nonneg _
    have hpos_prod : 0 < (u + v) * bqf u v w z (2 * r + 1) 2 := by omega
    by_cases hpos : 0 < bqf u v w z (2 * r + 1) 2
    · exact hpos
    · exfalso
      have : (u + v) * bqf u v w z (2 * r + 1) 2 ≤ 0 :=
        Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
      omega
  · unfold bqf
    have : (u + v) * (2 * r + 1) * (2 * r + 1) + 2 * halfK u v w z * (2 * r + 1) * 2 + (u + w) * 2 * 2 =
           (u + v) + 2 * ((u + v) * (2 * r * r + 2 * r) + 2 * halfK u v w z * (2 * r + 1) + 2 * (u + w)) := by grind
    rw [this]; omega
  · have hval : bqf u v w z (2 * r + 1) 2 = A * r * r + B * r + C := by
      unfold bqf; dsimp [A, B, C]; grind
    have hpos : 0 < bqf u v w z (2 * r + 1) 2 := by
      have hnorm := descartes_gaussian_norm hQ
      have hmul : (u + v) * bqf u v w z (2 * r + 1) 2 =
                  ((u + v) * (2 * r + 1) + 2 * halfK u v w z) ^ 2 + 4 * (u * u) := by
        unfold bqf; grind
      have hu2 : 1 ≤ u * u := by
        by_cases h : 0 < u
        · exact Int.mul_pos h h
        · have hneg : 0 < -u := by omega
          have : u * u = (-u) * (-u) := by grind
          rw [this]; exact Int.mul_pos hneg hneg
      have hsq0 : 0 ≤ ((u + v) * (2 * r + 1) + 2 * halfK u v w z) ^ 2 := by
        have : ((u + v) * (2 * r + 1) + 2 * halfK u v w z) ^ 2 =
               ((u + v) * (2 * r + 1) + 2 * halfK u v w z) * ((u + v) * (2 * r + 1) + 2 * halfK u v w z) := by grind
        rw [this]; exact sq_nonneg _
      have hpos_prod : 0 < (u + v) * bqf u v w z (2 * r + 1) 2 := by omega
      by_cases hpos : 0 < bqf u v w z (2 * r + 1) 2
      · exact hpos
      · exfalso
        have : (u + v) * bqf u v w z (2 * r + 1) 2 ≤ 0 :=
          Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
        omega
    have hcop_m : Nat.Coprime (bqf u v w z (2 * r + 1) 2).toNat m := by
      have hnat : (bqf u v w z (2 * r + 1) 2).natAbs = (bqf u v w z (2 * r + 1) 2).toNat := by omega
      rw [← hnat]
      apply coprime_of_avoid_primeFactors hm1
      intro p hp
      rw [hval]; exact hravoid p hp
    have hodd_t : (bqf u v w z (2 * r + 1) 2).toNat % 2 = 1 := by
      have : bqf u v w z (2 * r + 1) 2 % 2 = 1 := by
        unfold bqf
        have : (u + v) * (2 * r + 1) * (2 * r + 1) + 2 * halfK u v w z * (2 * r + 1) * 2 + (u + w) * 2 * 2 =
               (u + v) + 2 * ((u + v) * (2 * r * r + 2 * r) + 2 * halfK u v w z * (2 * r + 1) + 2 * (u + w)) := by grind
        rw [this]; omega
      omega
    have hcop2 : Nat.Coprime (2 ^ val2 u.natAbs) (bqf u v w z (2 * r + 1) 2).toNat :=
      Nat.Coprime.pow_left _ (coprime_two_left_of_odd hodd_t)
    rw [← hop.1]
    exact Nat.Coprime.mul_left hcop2 hcop_m.symm

/-- **Parabolic Dehn-Twist Transfer (Zero GCD Exceptions!):**
    In ANY primitive `4`-even Descartes quadruple `(u1, u2, v1, v2)` where `(u1, u2)` have the
    SAME parity (`u1 ≡ u2 mod 4`) and `(v1, v2)` have the OPPOSITE parity (`v1 ≡ v2 mod 4`),
    if `u2` has `χ = -1`, then `u1` ALSO has `χ = -1` (via the parabolic Dehn twist
    `c_n = (u1 + u2) n^2 + (v2 - v1 - (u1 + u2)) n + v1`)! -/
theorem parabolic_transfer_same_parity {u1 u2 v1 v2 : Int}
    (hQ : descartesQ u1 u2 v1 v2 = 0)
    (hpar : (u1 % 4 = 1 ∧ u2 % 4 = 1 ∧ v1 % 4 = 0 ∧ v2 % 4 = 0) ∨
            (u1 % 4 = 0 ∧ u2 % 4 = 0 ∧ v1 % 4 = 1 ∧ v2 % 4 = 1))
    (hu12_pos : 0 < u1 + u2)
    (hprim : ∀ p : Nat, IsPrime p → ¬ ((p : Int) ∣ u1 ∧ (p : Int) ∣ u2 ∧ (p : Int) ∣ v1 ∧ (p : Int) ∣ v2))
    (hu1_ne : u1 ≠ 0) (hu2_ne : u2 ≠ 0)
    (hchi_u2 : ∀ x y : Int, 0 < bqf u2 v1 v2 u1 x y → bqf u2 v1 v2 u1 x y % 2 = 1 →
      Nat.Coprime u2.natAbs (bqf u2 v1 v2 u1 x y).toNat →
      jacobi u2 (bqf u2 v1 v2 u1 x y).toNat = -1) :
    ∀ x y : Int, 0 < bqf u1 v1 v2 u2 x y → bqf u1 v1 v2 u2 x y % 2 = 1 →
      Nat.Coprime u1.natAbs (bqf u1 v1 v2 u2 x y).toNat →
      jacobi u1 (bqf u1 v1 v2 u2 x y).toNat = -1 := by
  let A : Int := u1 + u2
  let B : Int := v2 - v1 - (u1 + u2)
  let C : Int := v1
  let cseq (n : Int) : Int := A * n * n + B * n + C
  -- Exact Descartes identity for every parabolic twist step (u1, u2, c_n, c_{n+1})!
  have hQ_cn : ∀ n : Int, descartesQ u1 u2 (cseq n) (cseq (n + 1)) = 0 := by
    intro n
    unfold descartesQ at hQ ⊢
    dsimp [cseq, A, B, C]
    grind
  -- Exact parity of c_n for ALL n ∈ ℤ!
  have hc_par : ∀ n : Int, cseq n % 4 = v1 % 4 := by
    intro n
    have hv12 : (v2 - v1) % 4 = 0 := by rcases hpar with ⟨_,_,h1,h2⟩ | ⟨_,_,h1,h2⟩ <;> omega
    have hA2 : A % 2 = 0 := by dsimp [A]; rcases hpar with ⟨h1,h2,_,_⟩ | ⟨h1,h2,_,_⟩ <;> omega
    have hstep : cseq n - v1 = A * (n * (n - 1)) + (v2 - v1) * n := by dsimp [cseq, A, B, C]; grind
    have hnn : (n * (n - 1)) % 2 = 0 := by
      have : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases this with h | h <;> (rw [Int.mul_emod, Int.sub_emod, h]; omega)
    have h4a : (A * (n * (n - 1))) % 4 = 0 := by
      have h1 : A = 2 * (A / 2) := by omega
      have h2 : n * (n - 1) = 2 * ((n * (n - 1)) / 2) := by omega
      rw [h1, h2]; grind
    have h4b : ((v2 - v1) * n) % 4 = 0 := by
      have h1 : v2 - v1 = 4 * ((v2 - v1) / 4) := by omega
      rw [h1]; grind
    omega
  -- Prime list: all odd prime factors of u1 * u2!
  have hu12_ne : u1.natAbs * u2.natAbs ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hop := oddPart_spec (n := u1.natAbs * u2.natAbs) (by omega)
  let m := oddPart (u1.natAbs * u2.natAbs)
  have hm1 : 1 ≤ m := hop.2.2
  have hmo : m % 2 = 1 := hop.2.1
  have hspec := primeFactors_spec hm1
  have hodd_ps : ∀ p ∈ primeFactors m, p % 2 = 1 :=
    odd_mem_of_odd_listProd (by rw [hspec.1]; exact hmo)
  have hnondeg : ∀ p ∈ primeFactors m, ¬ ((p : Int) ∣ A ∧ (p : Int) ∣ B ∧ (p : Int) ∣ C) := by
    intro p hp_mem ⟨hdA, hdB, hdC⟩
    have hp := hspec.2 p hp_mem
    have hpm : p ∣ m := by have her := listProd_erase hp_mem; rw [hspec.1] at her; exact ⟨_, her.symm⟩
    have hpu12 : p ∣ u1.natAbs * u2.natAbs :=
      Nat.dvd_trans hpm ⟨2 ^ val2 (u1.natAbs * u2.natAbs), by
        have := hop.1.symm; rw [Nat.mul_comm (2 ^ _)] at this; exact this⟩
    have hpu : (p : Int) ∣ u1 ∨ (p : Int) ∣ u2 := by
      rcases prime_dvd_mul hp hpu12 with h1 | h2
      · left; exact nat_dvd_natAbs_iff.mp h1
      · right; exact nat_dvd_natAbs_iff.mp h2
    have hdu1 : (p : Int) ∣ u1 ∧ (p : Int) ∣ u2 := by
      rcases hdA with ⟨uA, huA⟩
      rcases hpu with h1 | h2
      · rcases h1 with ⟨k1, hk1⟩; exact ⟨⟨k1, hk1⟩, ⟨uA - k1, by dsimp [A] at huA; grind⟩⟩
      · rcases h2 with ⟨k2, hk2⟩; exact ⟨⟨uA - k2, by dsimp [A] at huA; grind⟩, ⟨k2, hk2⟩⟩
    have hdv2 : (p : Int) ∣ v2 := by
      rcases hdA with ⟨uA, huA⟩; rcases hdB with ⟨uB, huB⟩; rcases hdC with ⟨uC, huC⟩
      exact ⟨uB + uA + uC, by dsimp [A, B, C] at huA huB huC; grind⟩
    exact hprim p hp ⟨hdu1.1, hdu1.2, hdC, hdv2⟩
  -- Pick n large enough so c_n + u1 > 0, c_n + u2 > 0, c_n > 0, and coprime to oddPart(u1 * u2)!
  let N0 : Int := ((u1.natAbs + u2.natAbs + B.natAbs + C.natAbs + 4 : Nat) : Int)
  rcases exists_quad_avoid_primes_large A B C (primeFactors m) N0 hspec.2 hodd_ps hnondeg with ⟨n, hn_ge, hnavoid⟩
  have hn_nonneg : 0 ≤ n := by dsimp [N0] at hn_ge; omega
  have hn_ge1 : 1 ≤ n := by dsimp [N0] at hn_ge; omega
  have hcn_large : (u1.natAbs : Int) + (u2.natAbs : Int) + 1 ≤ cseq n := by
    have hA1 : 1 ≤ A := by dsimp [A]; omega
    have h1 : (B.natAbs : Int) * n + B * n ≥ 0 := by
      have : - (B.natAbs : Int) ≤ B := by omega
      have hmul := Int.mul_le_mul_of_nonneg_right this hn_nonneg
      grind
    have h2 : A * n * n ≥ n * n := by
      have hmul := Int.mul_le_mul_of_nonneg_right hA1 hn_nonneg
      have hmul2 := Int.mul_le_mul_of_nonneg_right hmul hn_nonneg
      grind
    have h3 : n * n ≥ N0 * n := Int.mul_le_mul_of_nonneg_right hn_ge hn_nonneg
    have h4 : N0 * n = ((u1.natAbs : Int) + (u2.natAbs : Int) + (C.natAbs : Int) + 4) * n + (B.natAbs : Int) * n := by
      dsimp [N0]; grind
    have h5 : ((u1.natAbs : Int) + (u2.natAbs : Int) + (C.natAbs : Int) + 4) * n ≥
              ((u1.natAbs : Int) + (u2.natAbs : Int) + (C.natAbs : Int) + 4) * 1 :=
      Int.mul_le_mul_of_nonneg_left hn_ge1 (by omega)
    dsimp [cseq]; omega
  let cn := cseq n
  let cn1 := cseq (n + 1)
  have hcn_pos : 0 < cn := by omega
  have ht1_pos : 0 < u1 + cn := by omega
  have ht2_pos : 0 < u2 + cn := by omega
  have ht1_odd : (u1 + cn) % 2 = 1 := by
    have := hc_par n; rcases hpar with ⟨h1,_,hv,_⟩ | ⟨h1,_,hv,_⟩ <;> omega
  have ht2_odd : (u2 + cn) % 2 = 1 := by
    have := hc_par n; rcases hpar with ⟨_,h2,hv,_⟩ | ⟨_,h2,hv,_⟩ <;> omega
  -- Coprimality of cn with u1 and u2 (odd parts, and hence odd sums u1+cn, u2+cn with u1, u2, cn!):
  have hcop_cn_m : Nat.Coprime cn.natAbs m := coprime_of_avoid_primeFactors hm1 hnavoid
  have hcop_t1_u1 : Nat.Coprime u1.natAbs (u1 + cn).toNat := by
    have hop1 := oddPart_spec (n := u1.natAbs) (by omega)
    have hcop2 : Nat.Coprime (2 ^ val2 u1.natAbs) (u1 + cn).toNat :=
      Nat.Coprime.pow_left _ (coprime_two_left_of_odd (by omega))
    have hm1_dvd_m : oddPart u1.natAbs ∣ m := by
      have h1 : oddPart u1.natAbs ∣ u1.natAbs * u2.natAbs :=
        Nat.dvd_trans ⟨2 ^ val2 u1.natAbs, by have := hop1.1.symm; rw [Nat.mul_comm (2 ^ _)] at this; exact this⟩
          (Nat.dvd_mul_right _ _)
      rw [← hop.1] at h1
      have hcop_o2 : Nat.Coprime (oddPart u1.natAbs) (2 ^ val2 (u1.natAbs * u2.natAbs)) :=
        Nat.Coprime.pow_right _ (coprime_two_left_of_odd hop1.2.1).symm
      exact hcop_o2.dvd_of_dvd_mul_left h1
    have hcop_o1_cn : Nat.Coprime (oddPart u1.natAbs) cn.natAbs :=
      Nat.Coprime.coprime_dvd_left hm1_dvd_m hcop_cn_m.symm
    have hcop_o1_t1 : Nat.Coprime (oddPart u1.natAbs) (u1 + cn).toNat := by
      have hnat : (u1 + cn).natAbs = (u1 + cn).toNat := by omega
      rw [← hnat]
      apply Nat.Coprime.symm
      apply coprime_of_avoid_primeFactors hop1.2.2
      intro p hp hdt
      have hspec1 := primeFactors_spec hop1.2.2
      have hpm1 : p ∣ oddPart u1.natAbs := by
        have her := listProd_erase hp; rw [hspec1.1] at her; exact ⟨_, her.symm⟩
      have hpu1 : (p : Int) ∣ u1 :=
        nat_dvd_natAbs_iff.mp (Nat.dvd_trans hpm1 ⟨2 ^ val2 u1.natAbs, by have := hop1.1.symm; rw [Nat.mul_comm (2 ^ _)] at this; exact this⟩)
      have hpcn : (p : Int) ∣ cn := by
        rcases hdt with ⟨k1, hk1⟩; rcases hpu1 with ⟨k2, hk2⟩; exact ⟨k1 - k2, by grind⟩
      have hg : p ∣ Nat.gcd (oddPart u1.natAbs) cn.natAbs := Nat.dvd_gcd hpm1 (nat_dvd_natAbs_iff.mpr hpcn)
      rw [hcop_o1_cn] at hg
      have := Nat.le_of_dvd (by decide) hg; have := (hspec1.2 p hp).1; omega
    rw [← hop1.1]
    exact Nat.Coprime.mul_left hcop2 hcop_o1_t1
  have hcop_t2_u2 : Nat.Coprime u2.natAbs (u2 + cn).toNat := by
    have hop2 := oddPart_spec (n := u2.natAbs) (by omega)
    have hcop2 : Nat.Coprime (2 ^ val2 u2.natAbs) (u2 + cn).toNat :=
      Nat.Coprime.pow_left _ (coprime_two_left_of_odd (by omega))
    have hm2_dvd_m : oddPart u2.natAbs ∣ m := by
      have h1 : oddPart u2.natAbs ∣ u1.natAbs * u2.natAbs :=
        Nat.dvd_trans ⟨2 ^ val2 u2.natAbs, by have := hop2.1.symm; rw [Nat.mul_comm (2 ^ _)] at this; exact this⟩
          (Nat.dvd_mul_left _ _)
      rw [← hop.1] at h1
      have hcop_o2 : Nat.Coprime (oddPart u2.natAbs) (2 ^ val2 (u1.natAbs * u2.natAbs)) :=
        Nat.Coprime.pow_right _ (coprime_two_left_of_odd hop2.2.1).symm
      exact hcop_o2.dvd_of_dvd_mul_left h1
    have hcop_o2_cn : Nat.Coprime (oddPart u2.natAbs) cn.natAbs :=
      Nat.Coprime.coprime_dvd_left hm2_dvd_m hcop_cn_m.symm
    have hcop_o2_t2 : Nat.Coprime (oddPart u2.natAbs) (u2 + cn).toNat := by
      have hnat : (u2 + cn).natAbs = (u2 + cn).toNat := by omega
      rw [← hnat]
      apply Nat.Coprime.symm
      apply coprime_of_avoid_primeFactors hop2.2.2
      intro p hp hdt
      have hspec2 := primeFactors_spec hop2.2.2
      have hpm2 : p ∣ oddPart u2.natAbs := by
        have her := listProd_erase hp; rw [hspec2.1] at her; exact ⟨_, her.symm⟩
      have hpu2 : (p : Int) ∣ u2 :=
        nat_dvd_natAbs_iff.mp (Nat.dvd_trans hpm2 ⟨2 ^ val2 u2.natAbs, by have := hop2.1.symm; rw [Nat.mul_comm (2 ^ _)] at this; exact this⟩)
      have hpcn : (p : Int) ∣ cn := by
        rcases hdt with ⟨k1, hk1⟩; rcases hpu2 with ⟨k2, hk2⟩; exact ⟨k1 - k2, by grind⟩
      have hg : p ∣ Nat.gcd (oddPart u2.natAbs) cn.natAbs := Nat.dvd_gcd hpm2 (nat_dvd_natAbs_iff.mpr hpcn)
      rw [hcop_o2_cn] at hg
      have := Nat.le_of_dvd (by decide) hg; have := (hspec2.2 p hp).1; omega
    rw [← hop2.1]
    exact Nat.Coprime.mul_left hcop2 hcop_o2_t2
  -- Coprimality of cn with (u1 + cn) and (u2 + cn):
  have hcop_cn_t1 : Nat.Coprime cn.natAbs (u1 + cn).toNat := by
    have hnat : (u1 + cn).natAbs = (u1 + cn).toNat := by omega
    rw [← hnat]
    apply coprime_of_avoid_primeFactors (by omega)
    intro p hp hd_cn
    have hspec_t1 := primeFactors_spec (n := (u1 + cn).natAbs) (by omega)
    have hpt : (p : Int) ∣ (u1 + cn) := nat_dvd_natAbs_iff.mp (by
      have her := listProd_erase hp; rw [hspec_t1.1] at her; exact ⟨_, her.symm⟩)
    have hpu1 : (p : Int) ∣ u1 := by
      rcases hpt with ⟨k1, hk1⟩; rcases hd_cn with ⟨k2, hk2⟩; exact ⟨k1 - k2, by grind⟩
    have hg : p ∣ Nat.gcd u1.natAbs (u1 + cn).toNat :=
      Nat.dvd_gcd (nat_dvd_natAbs_iff.mpr hpu1) (by rw [← hnat]; exact nat_dvd_natAbs_iff.mpr hpt)
    rw [hcop_t1_u1] at hg
    have := Nat.le_of_dvd (by decide) hg; have := (hspec_t1.2 p hp).1; omega
  have hcop_cn_t2 : Nat.Coprime cn.natAbs (u2 + cn).toNat := by
    have hnat : (u2 + cn).natAbs = (u2 + cn).toNat := by omega
    rw [← hnat]
    apply coprime_of_avoid_primeFactors (by omega)
    intro p hp hd_cn
    have hspec_t2 := primeFactors_spec (n := (u2 + cn).natAbs) (by omega)
    have hpt : (p : Int) ∣ (u2 + cn) := nat_dvd_natAbs_iff.mp (by
      have her := listProd_erase hp; rw [hspec_t2.1] at her; exact ⟨_, her.symm⟩)
    have hpu2 : (p : Int) ∣ u2 := by
      rcases hpt with ⟨k1, hk1⟩; rcases hd_cn with ⟨k2, hk2⟩; exact ⟨k1 - k2, by grind⟩
    have hg : p ∣ Nat.gcd u2.natAbs (u2 + cn).toNat :=
      Nat.dvd_gcd (nat_dvd_natAbs_iff.mpr hpu2) (by rw [← hnat]; exact nat_dvd_natAbs_iff.mpr hpt)
    rw [hcop_t2_u2] at hg
    have := Nat.le_of_dvd (by decide) hg; have := (hspec_t2.2 p hp).1; omega
  -- Key identity: u1 + cn = bqf u1 v1 v2 u2 (1 - n) n AND u2 + cn = bqf u2 v1 v2 u1 (1 - n) n!!
  have hbqf_u1_cn : bqf u1 v1 v2 u2 (1 - n) n = u1 + cn := by
    have h2k := two_mul_halfK ((descartesQ_perm u1 u2 v1 v2).1.symm.trans hQ)
    -- Expanding bqf u1 v1 v2 u2 (1 - n) n with 2*k = u1 + v1 + v2 - u2 yields u1 + cseq n.
    unfold bqf; dsimp [cn, cseq, A, B, C]; grind
  have hbqf_u2_cn : bqf u2 v1 v2 u1 (1 - n) n = u2 + cn := by
    have h2k := two_mul_halfK ((descartesQ_perm u1 u2 v1 v2).2.1.symm.trans hQ)
    unfold bqf; dsimp [cn, cseq, A, B, C]; grind
  -- ALSO: u1 + cn = bqf cn u1 u2 cn1 1 0 AND u2 + cn = bqf cn u1 u2 cn1 0 1!!
  have hbqf_cn_u1 : bqf cn u1 u2 cn1 1 0 = u1 + cn := by unfold bqf; grind
  have hbqf_cn_u2 : bqf cn u1 u2 cn1 0 1 = u2 + cn := by unfold bqf; grind
  -- Now chain the 4 equalities:
  --   jacobi u1 t = jacobi u1 (u1 + cn)         [Form-Invariance on u1]
  --               = jacobi cn (u1 + cn)         [u1 ≡ -cn mod (u1+cn) & (u1+cn) ≡ 1 mod 4]
  --               = jacobi cn (u2 + cn)         [Form-Invariance on cn in (cn, u1, u2, cn1)]
  --               = jacobi u2 (u2 + cn)         [cn ≡ -u2 mod (u2+cn) & (u2+cn) ≡ 1 mod 4]
  --               = -1                          [hchi_u2 at (1 - n, n)!]
  have hQ_u1 : descartesQ u1 v1 v2 u2 = 0 := (descartesQ_perm u1 u2 v1 v2).1.symm.trans hQ
  have hQ_cn' : descartesQ cn u1 u2 cn1 = 0 := (descartesQ_perm u1 u2 cn cn1).2.2.1.symm.trans (hQ_cn n)
  have h4_u1 : (u1 % 4 = 1 ∧ v1 % 4 = 0 ∧ v2 % 4 = 0 ∧ u2 % 4 = 1) ∨
               (u1 % 4 = 0 ∧ v1 % 4 = 1 ∧ v2 % 4 = 1 ∧ u2 % 4 = 0) := by
    rcases hpar with ⟨h1,h2,h3,h4'⟩ | ⟨h1,h2,h3,h4'⟩
    · left; exact ⟨h1, h3, h4', h2⟩
    · right; exact ⟨h1, h3, h4', h2⟩
  have h4_cn : (cn % 4 = 1 ∧ u1 % 4 = 0 ∧ u2 % 4 = 0 ∧ cn1 % 4 = 1) ∨
               (cn % 4 = 0 ∧ u1 % 4 = 1 ∧ u2 % 4 = 1 ∧ cn1 % 4 = 0) := by
    have hc1 := hc_par n; have hc2 := hc_par (n + 1)
    rcases hpar with ⟨h1,h2,h3,h4'⟩ | ⟨h1,h2,h3,h4'⟩
    · right; exact ⟨by omega, h1, h2, by omega⟩
    · left; exact ⟨by omega, h1, h2, by omega⟩
  have ht1_mod4 : (u1 + cn).toNat % 4 = 1 := by
    have : (u1 + cn) % 4 = 1 := by
      have := hc_par n; rcases hpar with ⟨h1,_,h3,_⟩ | ⟨h1,_,h3,_⟩ <;> omega
    omega
  have ht2_mod4 : (u2 + cn).toNat % 4 = 1 := by
    have : (u2 + cn) % 4 = 1 := by
      have := hc_par n; rcases hpar with ⟨_,h2,h3,_⟩ | ⟨_,h2,h3,_⟩ <;> omega
    omega
  have hstep1 : jacobi u1 (u1 + cn).toNat = jacobi cn (u1 + cn).toNat := by
    have hm : u1 % ((u1 + cn).toNat : Int) = (-cn) % ((u1 + cn).toNat : Int) := by
      have hpos_eq : ((u1 + cn).toNat : Int) = u1 + cn := Int.toNat_of_nonneg (by omega)
      rw [hpos_eq]
      have : u1 = (-cn) + 1 * (u1 + cn) := by omega
      conv => lhs; arg 1; rw [this]
      exact Int.add_mul_emod_self_right (-cn) 1 (u1 + cn)
    rw [jacobi_eq_of_mod_eq (by omega) hm, jacobi_neg (by omega) (by omega)]
    unfold signNeg1; simp [ht1_mod4]
  have hstep2 : jacobi cn (u1 + cn).toNat = jacobi cn (u2 + cn).toNat := by
    have hinv := jacobi_bqf_invariant hQ_cn' h4_cn (x1 := 1) (y1 := 0) (x2 := 0) (y2 := 1)
      (by rw [hbqf_cn_u1]; exact ht1_pos) (by rw [hbqf_cn_u1]; exact ht1_odd)
      (by rw [hbqf_cn_u1]; exact hcop_cn_t1)
      (by rw [hbqf_cn_u2]; exact ht2_pos) (by rw [hbqf_cn_u2]; exact ht2_odd)
      (by rw [hbqf_cn_u2]; exact hcop_cn_t2)
    rw [hbqf_cn_u1, hbqf_cn_u2] at hinv
    exact hinv
  have hstep3 : jacobi cn (u2 + cn).toNat = jacobi u2 (u2 + cn).toNat := by
    have hm : cn % ((u2 + cn).toNat : Int) = (-u2) % ((u2 + cn).toNat : Int) := by
      have hpos_eq : ((u2 + cn).toNat : Int) = u2 + cn := Int.toNat_of_nonneg (by omega)
      rw [hpos_eq]
      have : cn = (-u2) + 1 * (u2 + cn) := by omega
      conv => lhs; arg 1; rw [this]
      exact Int.add_mul_emod_self_right (-u2) 1 (u2 + cn)
    rw [jacobi_eq_of_mod_eq (by omega) hm, jacobi_neg (by omega) (by omega)]
    unfold signNeg1; simp [ht2_mod4]
  have hstep4 : jacobi u2 (u2 + cn).toNat = -1 := by
    have := hchi_u2 (1 - n) n (by rw [hbqf_u2_cn]; exact ht2_pos)
      (by rw [hbqf_u2_cn]; exact ht2_odd) (by rw [hbqf_u2_cn]; exact hcop_t2_u2)
    rw [hbqf_u2_cn] at this
    exact this
  intro x y hx_pos hx_odd hx_cop
  have hinv_u1 := jacobi_bqf_invariant hQ_u1 h4_u1 (x1 := x) (y1 := y) (x2 := 1 - n) (y2 := n)
    hx_pos hx_odd hx_cop
    (by rw [hbqf_u1_cn]; exact ht1_pos) (by rw [hbqf_u1_cn]; exact ht1_odd)
    (by rw [hbqf_u1_cn]; exact hcop_t1_u1)
  rw [hbqf_u1_cn] at hinv_u1
  rw [hinv_u1, hstep1, hstep2, hstep3, hstep4]

/-- Helper: BQF reflection flip `bqf u v w z' x y = bqf u v w z x (-y)` when `z' = 2(u+v+w) - z`. -/
theorem bqf_refl_fourth {u v w z : Int} (hQ : descartesQ u v w z = 0) (x y : Int) :
    bqf u v w (2 * (u + v + w) - z) x y = bqf u v w z x (-y) := by
  have hQ' : descartesQ u v w (2 * (u + v + w) - z) = 0 := by unfold descartesQ at hQ ⊢; grind
  have h1 := two_mul_halfK hQ
  have h2 := two_mul_halfK hQ'
  have hkneg : halfK u v w (2 * (u + v + w) - z) = - halfK u v w z := by omega
  unfold bqf; rw [hkneg]; grind

/-- Reusable helper: in a primitive 4-even quadruple `(a, b, 0, d)` where `a` has `χ = -1`,
    we derive `False` (since `a * b = k^2` and `Coprime a b` forces `a = r^2`, so `jacobi a t = +1`). -/
theorem no_zero_even_slot {a b d : Int}
    (hQ0 : descartesQ a b 0 d = 0)
    (ha4 : a % 4 = 1) (hb4 : b % 4 = 1) (hd4 : d % 4 = 0)
    (ha_pos : 0 < a) (hb_pos : 0 < b) (had : 0 < a + d)
    (hprim : ∀ p : Nat, IsPrime p → ¬ ((p : Int) ∣ a ∧ (p : Int) ∣ b ∧ (p : Int) ∣ (0 : Int) ∧ (p : Int) ∣ d))
    (hca : ∀ x y : Int, 0 < bqf a 0 d b x y → bqf a 0 d b x y % 2 = 1 →
      Nat.Coprime a.natAbs (bqf a 0 d b x y).toNat →
      jacobi a (bqf a 0 d b x y).toNat = -1) : False := by
  have hkab : a * b = halfK 0 a b d * halfK 0 a b d := by
    have h := descartes_gaussian_norm ((descartesQ_perm a b 0 d).2.2.1.symm.trans hQ0)
    simpa using h
  have hcop_ab : Nat.Coprime a.natAbs b.natAbs := by
    apply coprime_of_avoid_primeFactors (by omega)
    intro p hp hda
    have hspec := primeFactors_spec (n := b.natAbs) (by omega)
    have hdb : (p : Int) ∣ b := nat_dvd_natAbs_iff.mp (by
      have her := listProd_erase hp; rw [hspec.1] at her; exact ⟨_, her.symm⟩)
    have hdd : (p : Int) ∣ d := by
      have hp_pr := hspec.2 p hp
      have hsqd : (p : Int) ∣ d * d := by
        unfold descartesQ at hQ0
        rcases hda with ⟨ua, hua⟩; rcases hdb with ⟨ub, hub⟩
        exact ⟨2 * ua * b + 2 * ua * d + 2 * ub * d - ua * a - ub * b, by grind⟩
      exact (int_prime_dvd_mul hp_pr hsqd).elim id id
    exact hprim p (hspec.2 p hp) ⟨hda, hdb, ⟨0, by simp⟩, hdd⟩
  have hQ_a : descartesQ a 0 d b = 0 := (descartesQ_perm a b 0 d).1.symm.trans hQ0
  rcases exists_bqf_witness hQ_a (by omega) had (by omega) (by omega)
    (fun p hp ⟨h1, h2, h3, h4⟩ => hprim p hp ⟨h1, h4, h2, h3⟩)
    with ⟨x, y, ht_pos, ht_odd, ht_cop⟩
  have hneg1 := hca x y ht_pos ht_odd ht_cop
  have ha_sq : ∃ r : Nat, a.natAbs = r * r := by
    let aN := a.natAbs
    let bN := b.natAbs
    let kN := (halfK 0 a b d).natAbs
    have habk : aN * bN = kN * kN := by
      have : ((aN * bN : Nat) : Int) = ((kN * kN : Nat) : Int) := by
        rw [Int.natCast_mul, Int.natCast_mul, Int.natAbs_mul_self']
        have ha0 : (aN : Int) = a := by omega
        have hb0 : (bN : Int) = b := by omega
        rw [ha0, hb0]; exact hkab
      omega
    let g := Nat.gcd aN kN
    have hg_pos : 0 < g := by
      by_cases h0 : g = 0
      · have := Nat.gcd_eq_zero_iff.mp h0; omega
      · omega
    rcases Nat.gcd_dvd_left aN kN with ⟨a1, ha1⟩
    rcases Nat.gcd_dvd_right aN kN with ⟨k1, hk1⟩
    have hcop_a1k1 : Nat.Coprime a1 k1 := by
      have h1 : g * Nat.gcd a1 k1 = g * 1 := by
        rw [← Nat.gcd_mul_left, ← ha1, ← hk1, Nat.mul_one]
      exact Nat.eq_of_mul_eq_mul_left hg_pos h1
    have hmul1 : a1 * bN = g * (k1 * k1) := by
      have : g * (a1 * bN) = g * (g * (k1 * k1)) := by
        rw [← Nat.mul_assoc, ← ha1, habk, hk1]; grind
      exact Nat.eq_of_mul_eq_mul_left hg_pos this
    have ha1_dvd_g : a1 ∣ g := by
      have hdiv : a1 ∣ g * (k1 * k1) := ⟨bN, hmul1.symm⟩
      exact (Nat.Coprime.mul_right hcop_a1k1 hcop_a1k1).dvd_of_dvd_mul_right hdiv
    have hg2_dvd_a : g * g ∣ aN := by
      have hcop_gb : Nat.Coprime g bN := Nat.Coprime.coprime_dvd_left ⟨a1, ha1⟩ hcop_ab
      have hdiv : g * g ∣ aN * bN := ⟨k1 * k1, by rw [habk, hk1]; grind⟩
      exact (Nat.Coprime.mul_left hcop_gb hcop_gb).dvd_of_dvd_mul_right hdiv
    have hg_dvd_a1 : g ∣ a1 := by
      rcases hg2_dvd_a with ⟨t, ht⟩
      exact ⟨t, Nat.eq_of_mul_eq_mul_left hg_pos (by rw [← ha1, ht, Nat.mul_assoc])⟩
    have heq : a1 = g := Nat.dvd_antisymm ha1_dvd_g hg_dvd_a1
    exact ⟨g, by change aN = g * g; rw [ha1, heq]⟩
  rcases ha_sq with ⟨r, hr⟩
  let t := (bqf a 0 d b x y).toNat
  have hqa_eq : a = (r : Int) * (r : Int) := by
    have : (a.natAbs : Int) = a := by omega
    rw [← this, hr, Int.natCast_mul]
  have hcop_r : Nat.Coprime r t := by
    have ht_cop' : Nat.Coprime a.natAbs t := ht_cop
    rw [hr] at ht_cop'; exact (Nat.coprime_mul_iff_left.mp ht_cop').1
  have hj1 : jacobi a t = 1 := by
    rw [hqa_eq]
    exact jacobi_sq (by dsimp [t]; omega) (by dsimp [t]; omega) (by simpa using hcop_r)
  change jacobi a t = -1 at hneg1
  omega

/-- Helper: strict positivity of all 6 pairwise sums + non-vanishing of `c, d` when `HasHKRSObstruction q`. -/
theorem hkrs_all_nonzero {q : Quad} (h : HasHKRSObstruction q) :
    q.a ≠ 0 ∧ q.b ≠ 0 ∧ q.c ≠ 0 ∧ q.d ≠ 0 := by
  rcases h with ⟨h4, hca, hcb, hcc, hcd⟩
  rcases h4 with ⟨hQ, ha4, hb4, hc4, hd4, hab, hac, had, hbc, hbd, hcd_pos, hprim⟩
  refine ⟨by omega, by omega, ?_, ?_⟩
  · intro hc0
    exact no_zero_even_slot (hc0 ▸ hQ) ha4 hb4 hd4 (by omega) (by omega) had (hc0 ▸ hprim) (hc0 ▸ hca)
  · intro hd0
    have hQ0 : descartesQ q.a q.b 0 q.c = 0 := by
      have : descartesQ q.a q.b q.c 0 = 0 := hd0 ▸ hQ
      unfold descartesQ at this ⊢; grind
    have hca0 : ∀ x y : Int, 0 < bqf q.a 0 q.c q.b x y → bqf q.a 0 q.c q.b x y % 2 = 1 →
        Nat.Coprime q.a.natAbs (bqf q.a 0 q.c q.b x y).toNat →
        jacobi q.a (bqf q.a 0 q.c q.b x y).toNat = -1 := by
      intro x y hpos hodd hcop
      have hswap : bqf q.a 0 q.c q.b x y = bqf q.a q.c q.d q.b y x := by
        have h1 := two_mul_halfK ((descartesQ_perm q.a q.b q.c q.d).1.symm.trans hQ)
        have h2 := two_mul_halfK ((descartesQ_perm q.a q.b 0 q.c).1.symm.trans hQ0)
        unfold bqf; rw [hd0] at h1 ⊢; grind
      rw [hswap] at hpos hodd hcop ⊢; exact hca y x hpos hodd hcop
    exact no_zero_even_slot hQ0 ha4 hb4 hc4 (by omega) (by omega) hac
      (fun p hp ⟨h1, h2, h3, h4⟩ => hprim p hp ⟨h1, h2, h4, hd0 ▸ h3⟩) hca0

/-- **Invariance of `HasHKRSObstruction` under `refl1` (and by symmetry all 4 reflections)!** -/
theorem hkrs_preserved_refl1 {q : Quad} (h : HasHKRSObstruction q) :
    HasHKRSObstruction (refl1 q) := by
  have hnz := hkrs_all_nonzero h
  rcases h with ⟨h4, hca, hcb, hcc, hcd⟩
  rcases h4 with ⟨hQ, ha4, hb4, hc4, hd4, hab, hac, had, hbc, hbd, hcd_pos, hprim⟩
  let q' := refl1 q
  have hQ' : q'.descartes = 0 := by rw [(refl_involutions_and_descartes q).2.2.2.2.1]; exact hQ
  have ha4' : q'.a % 4 = 1 := by dsimp [q', refl1]; omega
  have hprim' := prim_refl1 hprim
  -- Positivity of q'.a + q.b, q'.a + q.c, q'.a + q.d via Gaussian norm identity (u+v)(u+w) = u^2 + k^2!
  have hba' : 0 < q'.a + q.b := by
    have hQb : descartesQ q.b q'.a q.c q.d = 0 := by
      simp only [Quad.descartes, descartesQ] at hQ' ⊢; dsimp [q', refl1] at hQ' ⊢; grind
    have hn' := descartes_gaussian_norm hQb
    have hb2 : 1 ≤ q.b * q.b := by
      by_cases h : 0 < q.b
      · exact Int.mul_pos h h
      · have : q.b * q.b = (-q.b) * (-q.b) := by grind
        rw [this]; exact Int.mul_pos (by omega) (by omega)
    have hk0 : 0 ≤ halfK q.b q'.a q.c q.d * halfK q.b q'.a q.c q.d := sq_nonneg _
    have hprod_pos : 0 < (q.b + q'.a) * (q.b + q.c) := by omega
    by_cases hp : 0 < q'.a + q.b
    · exact hp
    · exfalso
      have : (q.b + q'.a) * (q.b + q.c) ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
      omega
  have hca' : 0 < q'.a + q.c := by
    have hQc : descartesQ q.c q'.a q.b q.d = 0 := by
      simp only [Quad.descartes, descartesQ] at hQ' ⊢; dsimp [q', refl1] at hQ' ⊢; grind
    have hn' := descartes_gaussian_norm hQc
    have hc2 : 1 ≤ q.c * q.c := by
      by_cases h : 0 < q.c
      · exact Int.mul_pos h h
      · have : q.c * q.c = (-q.c) * (-q.c) := by grind
        rw [this]; exact Int.mul_pos (by omega) (by omega)
    have hk0 : 0 ≤ halfK q.c q'.a q.b q.d * halfK q.c q'.a q.b q.d := sq_nonneg _
    have hprod_pos : 0 < (q.c + q'.a) * (q.c + q.b) := by omega
    by_cases hp : 0 < q'.a + q.c
    · exact hp
    · exfalso
      have : (q.c + q'.a) * (q.c + q.b) ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
      omega
  have hda' : 0 < q'.a + q.d := by
    have hQd : descartesQ q.d q'.a q.b q.c = 0 := by
      simp only [Quad.descartes, descartesQ] at hQ' ⊢; dsimp [q', refl1] at hQ' ⊢; grind
    have hn' := descartes_gaussian_norm hQd
    have hd2 : 1 ≤ q.d * q.d := by
      by_cases h : 0 < q.d
      · exact Int.mul_pos h h
      · have : q.d * q.d = (-q.d) * (-q.d) := by grind
        rw [this]; exact Int.mul_pos (by omega) (by omega)
    have hk0 : 0 ≤ halfK q.d q'.a q.b q.c * halfK q.d q'.a q.b q.c := sq_nonneg _
    have hprod_pos : 0 < (q.d + q'.a) * (q.d + q.b) := by omega
    by_cases hp : 0 < q'.a + q.d
    · exact hp
    · exfalso
      have : (q.d + q'.a) * (q.d + q.b) ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
      omega
  have h4' : Is4EvenPrim q' :=
    ⟨hQ', ha4', hb4, hc4, hd4, hba', hca', hda', hbc, hbd, hcd_pos, hprim'⟩
  -- For b, c, d: their BQFs flip sign on y (via bqf_refl_fourth) or permute identically!
  have hcb' : ∀ x y : Int, 0 < bqf q.b q.c q.d q'.a x y → bqf q.b q.c q.d q'.a x y % 2 = 1 →
      Nat.Coprime q.b.natAbs (bqf q.b q.c q.d q'.a x y).toNat →
      jacobi q.b (bqf q.b q.c q.d q'.a x y).toNat = -1 := by
    intro x y hpos hodd hcop
    have hQb : descartesQ q.b q.c q.d q.a = 0 := (descartesQ_perm q.a q.b q.c q.d).2.1.symm.trans hQ
    have hfl := bqf_refl_fourth hQb x y
    have heq : q'.a = 2 * (q.b + q.c + q.d) - q.a := rfl
    rw [heq, hfl] at hpos hodd hcop ⊢
    exact hcb x (-y) hpos hodd hcop
  have hcc' : ∀ x y : Int, 0 < bqf q.c q'.a q.b q.d x y → bqf q.c q'.a q.b q.d x y % 2 = 1 →
      Nat.Coprime q.c.natAbs (bqf q.c q'.a q.b q.d x y).toNat →
      jacobi q.c (bqf q.c q'.a q.b q.d x y).toNat = -1 := by
    intro x y hpos hodd hcop
    have hQc' : descartesQ q.c q'.a q.b q.d = 0 := (descartesQ_perm q'.a q.b q.c q.d).2.2.1.symm.trans hQ'
    -- Exact unimodular substitution: bqf c a' b d x y = bqf c a b d (-x) (y + 2 * x).
    have hsub : bqf q.c q'.a q.b q.d x y = bqf q.c q.a q.b q.d (-x) (y + 2 * x) := by
      have h1 := two_mul_halfK ((descartesQ_perm q.a q.b q.c q.d).2.2.1.symm.trans hQ)
      have h2 := two_mul_halfK hQc'
      unfold bqf; dsimp [q', refl1] at h2 ⊢; grind
    rw [hsub] at hpos hodd hcop ⊢
    exact hcc (-x) (y + 2 * x) hpos hodd hcop
  have hcd' : ∀ x y : Int, 0 < bqf q.d q'.a q.b q.c x y → bqf q.d q'.a q.b q.c x y % 2 = 1 →
      Nat.Coprime q.d.natAbs (bqf q.d q'.a q.b q.c x y).toNat →
      jacobi q.d (bqf q.d q'.a q.b q.c x y).toNat = -1 := by
    intro x y hpos hodd hcop
    have hQd' : descartesQ q.d q'.a q.b q.c = 0 := (descartesQ_perm q'.a q.b q.c q.d).2.2.2.symm.trans hQ'
    have hsub : bqf q.d q'.a q.b q.c x y = bqf q.d q.a q.b q.c (-x) (y + 2 * x) := by
      have h1 := two_mul_halfK ((descartesQ_perm q.a q.b q.c q.d).2.2.2.symm.trans hQ)
      have h2 := two_mul_halfK hQd'
      unfold bqf; dsimp [q', refl1] at h2 ⊢; grind
    rw [hsub] at hpos hodd hcop ⊢
    exact hcd (-x) (y + 2 * x) hpos hodd hcop
  -- And for the NEW circle q'.a: ONE LINE via parabolic_transfer_same_parity from q.b!
  have hca' : ∀ x y : Int, 0 < bqf q'.a q.c q.d q.b x y → bqf q'.a q.c q.d q.b x y % 2 = 1 →
      Nat.Coprime q'.a.natAbs (bqf q'.a q.c q.d q.b x y).toNat →
      jacobi q'.a (bqf q'.a q.c q.d q.b x y).toNat = -1 :=
    parabolic_transfer_same_parity hQ' (Or.inl ⟨ha4', hb4, hc4, hd4⟩) hba' hprim'
      (by omega) hnz.2.1 hcb'
  exact ⟨h4', hca', hcb', hcc', hcd'⟩

/-- Swap symmetry lemmas so `refl2`, `refl3`, `refl4` follow immediately from `hkrs_preserved_refl1`! -/
theorem hkrs_swap_ab {q : Quad} (h : HasHKRSObstruction q) :
    HasHKRSObstruction ⟨q.b, q.a, q.c, q.d⟩ := by
  rcases h with ⟨⟨hQ, ha4, hb4, hc4, hd4, hab, hac, had, hbc, hbd, hcd, hprim⟩, hca, hcb, hcc, hcd'⟩
  have hQ' : descartesQ q.b q.a q.c q.d = 0 := by simp only [Quad.descartes, descartesQ] at hQ ⊢; grind
  refine ⟨⟨hQ', hb4, ha4, hc4, hd4, by dsimp; omega, hbc, hbd, hac, had, hcd,
           fun p hp ⟨h1,h2,h3,h4⟩ => hprim p hp ⟨h2,h1,h3,h4⟩⟩, hcb, hca, ?_, ?_⟩
  · intro x y hpos hodd hcop
    have hswap : bqf q.c q.b q.a q.d x y = bqf q.c q.a q.b q.d y x := by
      have h1 := two_mul_halfK ((descartesQ_perm q.a q.b q.c q.d).2.2.1.symm.trans hQ)
      have h2 := two_mul_halfK ((descartesQ_perm q.b q.a q.c q.d).2.2.1.symm.trans hQ')
      unfold bqf; grind
    rw [hswap] at hpos hodd hcop ⊢; exact hcc y x hpos hodd hcop
  · intro x y hpos hodd hcop
    have hswap : bqf q.d q.b q.a q.c x y = bqf q.d q.a q.b q.c y x := by
      have h1 := two_mul_halfK ((descartesQ_perm q.a q.b q.c q.d).2.2.2.symm.trans hQ)
      have h2 := two_mul_halfK ((descartesQ_perm q.b q.a q.c q.d).2.2.2.symm.trans hQ')
      unfold bqf; grind
    rw [hswap] at hpos hodd hcop ⊢; exact hcd' y x hpos hodd hcop

theorem hkrs_swap_cd {q : Quad} (h : HasHKRSObstruction q) :
    HasHKRSObstruction ⟨q.a, q.b, q.d, q.c⟩ := by
  rcases h with ⟨⟨hQ, ha4, hb4, hc4, hd4, hab, hac, had, hbc, hbd, hcd, hprim⟩, hca, hcb, hcc, hcd'⟩
  have hQ' : descartesQ q.a q.b q.d q.c = 0 := by simp only [Quad.descartes, descartesQ] at hQ ⊢; grind
  refine ⟨⟨hQ', ha4, hb4, hd4, hc4, hab, had, hac, hbd, hbc, by dsimp; omega,
           fun p hp ⟨h1,h2,h3,h4⟩ => hprim p hp ⟨h1,h2,h4,h3⟩⟩, ?_, ?_, hcd', hcc⟩
  · intro x y hpos hodd hcop
    have hswap : bqf q.a q.d q.c q.b x y = bqf q.a q.c q.d q.b y x := by
      have h1 := two_mul_halfK ((descartesQ_perm q.a q.b q.c q.d).1.symm.trans hQ)
      have h2 := two_mul_halfK ((descartesQ_perm q.a q.b q.d q.c).1.symm.trans hQ')
      unfold bqf; grind
    rw [hswap] at hpos hodd hcop ⊢; exact hca y x hpos hodd hcop
  · intro x y hpos hodd hcop
    have hswap : bqf q.b q.d q.c q.a x y = bqf q.b q.c q.d q.a y x := by
      have h1 := two_mul_halfK ((descartesQ_perm q.a q.b q.c q.d).2.1.symm.trans hQ)
      have h2 := two_mul_halfK ((descartesQ_perm q.a q.b q.d q.c).2.1.symm.trans hQ')
      unfold bqf; grind
    rw [hswap] at hpos hodd hcop ⊢; exact hcb y x hpos hodd hcop

theorem hkrs_preserved_refl2 {q : Quad} (h : HasHKRSObstruction q) :
    HasHKRSObstruction (refl2 q) := by
  have h1 := hkrs_preserved_refl1 (hkrs_swap_ab h)
  have h2 := hkrs_swap_ab h1
  have heq : (⟨(refl1 ⟨q.b, q.a, q.c, q.d⟩).b, (refl1 ⟨q.b, q.a, q.c, q.d⟩).a,
               (refl1 ⟨q.b, q.a, q.c, q.d⟩).c, (refl1 ⟨q.b, q.a, q.c, q.d⟩).d⟩ : Quad) = refl2 q := by
    simp [refl1, refl2]
  rwa [heq] at h2

theorem hkrs_preserved_refl3 {q : Quad} (h : HasHKRSObstruction q) :
    HasHKRSObstruction (refl3 q) := by
  have hnz := hkrs_all_nonzero h
  rcases h with ⟨h4, hca, hcb, hcc, hcd⟩
  rcases h4 with ⟨hQ, ha4, hb4, hc4, hd4, hab, hac, had, hbc, hbd, hcd_pos, hprim⟩
  let q' := refl3 q
  have hQ' : q'.descartes = 0 := by rw [(refl_involutions_and_descartes q).2.2.2.2.2.2.1]; exact hQ
  have hc4' : q'.c % 4 = 0 := by dsimp [q', refl3]; omega
  have hprim' : ∀ p : Nat, IsPrime p →
      ¬ ((p : Int) ∣ q'.a ∧ (p : Int) ∣ q'.b ∧ (p : Int) ∣ q'.c ∧ (p : Int) ∣ q'.d) := by
    intro p hp ⟨ha, hb, hc', hd⟩
    apply hprim p hp; refine ⟨ha, hb, ?_, hd⟩
    rcases ha with ⟨ua, hua⟩; rcases hb with ⟨ub, hub⟩; rcases hc' with ⟨uc, huc⟩; rcases hd with ⟨ud, hud⟩
    exact ⟨2 * (ua + ub + ud) - uc, by dsimp [q', refl3] at hua hub huc hud; grind⟩
  have hac' : 0 < q.a + q'.c := by
    have hQa : descartesQ q.a q'.c q.d q.b = 0 := by
      simp only [Quad.descartes, descartesQ] at hQ' ⊢; dsimp [q', refl3] at hQ' ⊢; grind
    have hn' := descartes_gaussian_norm hQa
    have ha2 : 1 ≤ q.a * q.a := by
      by_cases h : 0 < q.a
      · exact Int.mul_pos h h
      · have : q.a * q.a = (-q.a) * (-q.a) := by grind
        rw [this]; exact Int.mul_pos (by omega) (by omega)
    have hk0 : 0 ≤ halfK q.a q'.c q.d q.b * halfK q.a q'.c q.d q.b := sq_nonneg _
    have hprod_pos : 0 < (q.a + q'.c) * (q.a + q.d) := by omega
    by_cases hp : 0 < q.a + q'.c
    · exact hp
    · exfalso
      have : (q.a + q'.c) * (q.a + q.d) ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
      omega
  have hbc' : 0 < q.b + q'.c := by
    have hQb : descartesQ q.b q'.c q.d q.a = 0 := by
      simp only [Quad.descartes, descartesQ] at hQ' ⊢; dsimp [q', refl3] at hQ' ⊢; grind
    have hn' := descartes_gaussian_norm hQb
    have hb2 : 1 ≤ q.b * q.b := by
      by_cases h : 0 < q.b
      · exact Int.mul_pos h h
      · have : q.b * q.b = (-q.b) * (-q.b) := by grind
        rw [this]; exact Int.mul_pos (by omega) (by omega)
    have hk0 : 0 ≤ halfK q.b q'.c q.d q.a * halfK q.b q'.c q.d q.a := sq_nonneg _
    have hprod_pos : 0 < (q.b + q'.c) * (q.b + q.d) := by omega
    by_cases hp : 0 < q.b + q'.c
    · exact hp
    · exfalso
      have : (q.b + q'.c) * (q.b + q.d) ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
      omega
  have hcd_pos' : 0 < q'.c + q.d := by
    have hQd : descartesQ q.d q'.c q.a q.b = 0 := by
      simp only [Quad.descartes, descartesQ] at hQ' ⊢; dsimp [q', refl3] at hQ' ⊢; grind
    have hn' := descartes_gaussian_norm hQd
    have hd2 : 1 ≤ q.d * q.d := by
      by_cases h : 0 < q.d
      · exact Int.mul_pos h h
      · have : q.d * q.d = (-q.d) * (-q.d) := by grind
        rw [this]; exact Int.mul_pos (by omega) (by omega)
    have hk0 : 0 ≤ halfK q.d q'.c q.a q.b * halfK q.d q'.c q.a q.b := sq_nonneg _
    have hprod_pos : 0 < (q.d + q'.c) * (q.d + q.a) := by omega
    by_cases hp : 0 < q'.c + q.d
    · exact hp
    · exfalso
      have : (q.d + q'.c) * (q.d + q.a) ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
      omega
  have hca' : ∀ x y : Int, 0 < bqf q.a q'.c q.d q.b x y → bqf q.a q'.c q.d q.b x y % 2 = 1 →
      Nat.Coprime q.a.natAbs (bqf q.a q'.c q.d q.b x y).toNat →
      jacobi q.a (bqf q.a q'.c q.d q.b x y).toNat = -1 := by
    intro x y hpos hodd hcop
    have hQa' : descartesQ q.a q'.c q.d q.b = 0 := (descartesQ_perm q.a q.b q'.c q.d).1.symm.trans hQ'
    have hsub : bqf q.a q'.c q.d q.b x y = bqf q.a q.c q.d q.b (-x) (y + 2 * x) := by
      have h1 := two_mul_halfK ((descartesQ_perm q.a q.b q.c q.d).1.symm.trans hQ)
      have h2 := two_mul_halfK hQa'
      unfold bqf; dsimp [q', refl3] at h2 ⊢; grind
    rw [hsub] at hpos hodd hcop ⊢
    exact hca (-x) (y + 2 * x) hpos hodd hcop
  have hcb' : ∀ x y : Int, 0 < bqf q.b q'.c q.d q.a x y → bqf q.b q'.c q.d q.a x y % 2 = 1 →
      Nat.Coprime q.b.natAbs (bqf q.b q'.c q.d q.a x y).toNat →
      jacobi q.b (bqf q.b q'.c q.d q.a x y).toNat = -1 := by
    intro x y hpos hodd hcop
    have hQb' : descartesQ q.b q'.c q.d q.a = 0 := (descartesQ_perm q.a q.b q'.c q.d).2.1.symm.trans hQ'
    have hsub : bqf q.b q'.c q.d q.a x y = bqf q.b q.c q.d q.a (-x) (y + 2 * x) := by
      have h1 := two_mul_halfK ((descartesQ_perm q.a q.b q.c q.d).2.1.symm.trans hQ)
      have h2 := two_mul_halfK hQb'
      unfold bqf; dsimp [q', refl3] at h2 ⊢; grind
    rw [hsub] at hpos hodd hcop ⊢
    exact hcb (-x) (y + 2 * x) hpos hodd hcop
  have hcd' : ∀ x y : Int, 0 < bqf q.d q.a q.b q'.c x y → bqf q.d q.a q.b q'.c x y % 2 = 1 →
      Nat.Coprime q.d.natAbs (bqf q.d q.a q.b q'.c x y).toNat →
      jacobi q.d (bqf q.d q.a q.b q'.c x y).toNat = -1 := by
    intro x y hpos hodd hcop
    have hQd : descartesQ q.d q.a q.b q.c = 0 := (descartesQ_perm q.a q.b q.c q.d).2.2.2.symm.trans hQ
    have hfl := bqf_refl_fourth hQd x y
    have heq : q'.c = 2 * (q.d + q.a + q.b) - q.c := by dsimp [q', refl3]; omega
    rw [heq, hfl] at hpos hodd hcop ⊢
    exact hcd x (-y) hpos hodd hcop
  -- Prove q'.c ≠ 0 via our clean reusable `no_zero_even_slot` lemma!
  have hqc'_ne : q'.c ≠ 0 := by
    intro hc0
    exact no_zero_even_slot (hc0 ▸ hQ') ha4 hb4 hd4 (by omega) (by omega) had (hc0 ▸ hprim') (hc0 ▸ hca')
  have hQ_cd : descartesQ q'.c q.d q.a q.b = 0 := by
    simp only [Quad.descartes, descartesQ] at hQ' ⊢; dsimp [q', refl3] at hQ' ⊢; grind
  have hcc' : ∀ x y : Int, 0 < bqf q'.c q.a q.b q.d x y → bqf q'.c q.a q.b q.d x y % 2 = 1 →
      Nat.Coprime q'.c.natAbs (bqf q'.c q.a q.b q.d x y).toNat →
      jacobi q'.c (bqf q'.c q.a q.b q.d x y).toNat = -1 :=
    parabolic_transfer_same_parity hQ_cd (Or.inr ⟨hc4', hd4, ha4, hb4⟩) hcd_pos'
      (fun p hp ⟨h1,h2,h3,h4⟩ => hprim' p hp ⟨h3,h4,h1,h2⟩) hqc'_ne hnz.2.2.2 hcd'
  exact ⟨⟨hQ', ha4, hb4, hc4', hd4, hab, hac', had, hbc', hbd, hcd_pos', hprim'⟩, hca', hcb', hcc', hcd'⟩

theorem hkrs_preserved_refl4 {q : Quad} (h : HasHKRSObstruction q) :
    HasHKRSObstruction (refl4 q) := by
  have h1 := hkrs_preserved_refl3 (hkrs_swap_cd h)
  have h2 := hkrs_swap_cd h1
  have heq : (⟨(refl3 ⟨q.a, q.b, q.d, q.c⟩).a, (refl3 ⟨q.a, q.b, q.d, q.c⟩).b,
               (refl3 ⟨q.a, q.b, q.d, q.c⟩).d, (refl3 ⟨q.a, q.b, q.d, q.c⟩).c⟩ : Quad) = refl4 q := by
    simp [refl3, refl4]
  rwa [heq] at h2

/-- **Universal HKRS Invariance:** If a root quadruple satisfies `HasHKRSObstruction`, then EVERY
    quadruple in its infinite Apollonian orbit satisfies `HasHKRSObstruction` AND contains ZERO
    perfect squares `m^2`! -/
theorem hkrs_orbit_no_squares {root q : Quad} (hroot : HasHKRSObstruction root)
    (horb : InApollonianOrbit root q) :
    ∀ m : Int, q.a ≠ m * m ∧ q.b ≠ m * m ∧ q.c ≠ m * m ∧ q.d ≠ m * m := by
  have hq : HasHKRSObstruction q := by
    induction horb with
    | base => exact hroot
    | s1 _ ih => exact hkrs_preserved_refl1 ih
    | s2 _ ih => exact hkrs_preserved_refl2 ih
    | s3 _ ih => exact hkrs_preserved_refl3 ih
    | s4 _ ih => exact hkrs_preserved_refl4 ih
  have hnz := hkrs_all_nonzero hq
  rcases hq with ⟨⟨hQ, ha4, hb4, hc4, hd4, hab, hac, had, hbc, hbd, hcd, hprim⟩, hca, hcb, hcc, hcd'⟩
  intro m
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hm
    have hQa : descartesQ q.a q.c q.d q.b = 0 := (descartesQ_perm q.a q.b q.c q.d).1.symm.trans hQ
    rcases exists_bqf_witness hQa hac had (by omega) hnz.1 (fun p hp ⟨h1,h2,h3,h4⟩ => hprim p hp ⟨h1,h4,h2,h3⟩)
      with ⟨x, y, ht_pos, ht_odd, ht_cop⟩
    let t := (bqf q.a q.c q.d q.b x y).toNat
    have hneg1 : jacobi q.a t = -1 := hca x y ht_pos ht_odd ht_cop
    have hcop_m : Nat.Coprime m.natAbs t := by
      have h' : Nat.Coprime q.a.natAbs t := ht_cop
      rw [hm, Int.natAbs_mul] at h'; exact (Nat.coprime_mul_iff_left.mp h').1
    have hj1 : jacobi q.a t = 1 := by
      rw [hm]; exact jacobi_sq (by dsimp [t]; omega) (by dsimp [t]; omega) hcop_m
    omega
  · intro hm
    have hQb : descartesQ q.b q.c q.d q.a = 0 := (descartesQ_perm q.a q.b q.c q.d).2.1.symm.trans hQ
    rcases exists_bqf_witness hQb hbc hbd (by omega) hnz.2.1 (fun p hp ⟨h1,h2,h3,h4⟩ => hprim p hp ⟨h4,h1,h2,h3⟩)
      with ⟨x, y, ht_pos, ht_odd, ht_cop⟩
    let t := (bqf q.b q.c q.d q.a x y).toNat
    have hneg1 : jacobi q.b t = -1 := hcb x y ht_pos ht_odd ht_cop
    have hcop_m : Nat.Coprime m.natAbs t := by
      have h' : Nat.Coprime q.b.natAbs t := ht_cop
      rw [hm, Int.natAbs_mul] at h'; exact (Nat.coprime_mul_iff_left.mp h').1
    have hj1 : jacobi q.b t = 1 := by
      rw [hm]; exact jacobi_sq (by dsimp [t]; omega) (by dsimp [t]; omega) hcop_m
    omega
  · intro hm
    have hQc : descartesQ q.c q.a q.b q.d = 0 := (descartesQ_perm q.a q.b q.c q.d).2.2.1.symm.trans hQ
    rcases exists_bqf_witness hQc (by omega) (by omega) (by omega) hnz.2.2.1
      (fun p hp ⟨h1,h2,h3,h4⟩ => hprim p hp ⟨h2,h3,h1,h4⟩) with ⟨x, y, ht_pos, ht_odd, ht_cop⟩
    let t := (bqf q.c q.a q.b q.d x y).toNat
    have hneg1 : jacobi q.c t = -1 := hcc x y ht_pos ht_odd ht_cop
    have hcop_m : Nat.Coprime m.natAbs t := by
      have h' : Nat.Coprime q.c.natAbs t := ht_cop
      rw [hm, Int.natAbs_mul] at h'; exact (Nat.coprime_mul_iff_left.mp h').1
    have hj1 : jacobi q.c t = 1 := by
      rw [hm]; exact jacobi_sq (by dsimp [t]; omega) (by dsimp [t]; omega) hcop_m
    omega
  · intro hm
    have hQd : descartesQ q.d q.a q.b q.c = 0 := (descartesQ_perm q.a q.b q.c q.d).2.2.2.symm.trans hQ
    rcases exists_bqf_witness hQd (by omega) (by omega) (by omega) hnz.2.2.2
      (fun p hp ⟨h1,h2,h3,h4⟩ => hprim p hp ⟨h2,h3,h4,h1⟩) with ⟨x, y, ht_pos, ht_odd, ht_cop⟩
    let t := (bqf q.d q.a q.b q.c x y).toNat
    have hneg1 : jacobi q.d t = -1 := hcd' x y ht_pos ht_odd ht_cop
    have hcop_m : Nat.Coprime m.natAbs t := by
      have h' : Nat.Coprime q.d.natAbs t := ht_cop
      rw [hm, Int.natAbs_mul] at h'; exact (Nat.coprime_mul_iff_left.mp h').1
    have hj1 : jacobi q.d t = 1 := by
      rw [hm]; exact jacobi_sq (by dsimp [t]; omega) (by dsimp [t]; omega) hcop_m
    omega

/-- Concrete certification helper: check `HasHKRSObstruction` on any concrete root via a single
    basepoint evaluation `(x0, y0)` per circle (then `jacobi_bqf_invariant` propagates to ALL `(x, y)`!). -/
theorem mk_hkrs_root {q : Quad} (h4 : Is4EvenPrim q)
    (xa ya xb yb xc yc xd yd : Int)
    (hpa : 0 < bqf q.a q.c q.d q.b xa ya) (hoa : bqf q.a q.c q.d q.b xa ya % 2 = 1)
    (hca : Nat.Coprime q.a.natAbs (bqf q.a q.c q.d q.b xa ya).toNat)
    (hja : jacobi q.a (bqf q.a q.c q.d q.b xa ya).toNat = -1)
    (hpb : 0 < bqf q.b q.c q.d q.a xb yb) (hob : bqf q.b q.c q.d q.a xb yb % 2 = 1)
    (hcb : Nat.Coprime q.b.natAbs (bqf q.b q.c q.d q.a xb yb).toNat)
    (hjb : jacobi q.b (bqf q.b q.c q.d q.a xb yb).toNat = -1)
    (hpc : 0 < bqf q.c q.a q.b q.d xc yc) (hoc : bqf q.c q.a q.b q.d xc yc % 2 = 1)
    (hcc : Nat.Coprime q.c.natAbs (bqf q.c q.a q.b q.d xc yc).toNat)
    (hjc : jacobi q.c (bqf q.c q.a q.b q.d xc yc).toNat = -1)
    (hpd : 0 < bqf q.d q.a q.b q.c xd yd) (hod : bqf q.d q.a q.b q.c xd yd % 2 = 1)
    (hcd : Nat.Coprime q.d.natAbs (bqf q.d q.a q.b q.c xd yd).toNat)
    (hjd : jacobi q.d (bqf q.d q.a q.b q.c xd yd).toNat = -1) :
    HasHKRSObstruction q := by
  rcases h4 with ⟨hQ, ha4, hb4, hc4, hd4, hab, hac, had, hbc, hbd, hcd_pos, hprim⟩
  refine ⟨⟨hQ, ha4, hb4, hc4, hd4, hab, hac, had, hbc, hbd, hcd_pos, hprim⟩, ?_, ?_, ?_, ?_⟩
  · intro x y hp ho hc
    rw [jacobi_bqf_invariant ((descartesQ_perm q.a q.b q.c q.d).1.symm.trans hQ)
        (Or.inl ⟨ha4, hc4, hd4, hb4⟩) hp ho hc hpa hoa hca, hja]
  · intro x y hp ho hc
    rw [jacobi_bqf_invariant ((descartesQ_perm q.a q.b q.c q.d).2.1.symm.trans hQ)
        (Or.inl ⟨hb4, hc4, hd4, ha4⟩) hp ho hc hpb hob hcb, hjb]
  · intro x y hp ho hc
    rw [jacobi_bqf_invariant ((descartesQ_perm q.a q.b q.c q.d).2.2.1.symm.trans hQ)
        (Or.inr ⟨hc4, ha4, hb4, hd4⟩) hp ho hc hpc hoc hcc, hjc]
  · intro x y hp ho hc
    rw [jacobi_bqf_invariant ((descartesQ_perm q.a q.b q.c q.d).2.2.2.symm.trans hQ)
        (Or.inr ⟨hd4, ha4, hb4, hc4⟩) hp ho hc hpd hod hcd, hjd]

/-- Helper for finite primitivity check on concrete roots. -/
theorem prim_of_coprime_pair {a b c d : Int} (hcop : Nat.Coprime a.natAbs b.natAbs) :
    ∀ p : Nat, IsPrime p → ¬ ((p : Int) ∣ a ∧ (p : Int) ∣ b ∧ (p : Int) ∣ c ∧ (p : Int) ∣ d) := by
  intro p hp ⟨ha, hb, _, _⟩
  have hg : p ∣ Nat.gcd a.natAbs b.natAbs :=
    Nat.dvd_gcd (nat_dvd_natAbs_iff.mpr ha) (nat_dvd_natAbs_iff.mpr hb)
  rw [hcop] at hg
  have := Nat.le_of_dvd (by decide) hg; have := hp.1; omega

/-- Concrete HKRS certificate 1: `(-3, 5, 8, 8)`. -/
def rootHKRS1 : Quad := ⟨-3, 5, 8, 8⟩
/-- Concrete HKRS certificate 2: `(-7, 17, 12, 20)` (same mod-24 set as `(-4, 8, 9, 9)`). -/
def rootHKRS2 : Quad := ⟨-7, 17, 12, 20⟩
/-- Concrete HKRS certificate 3: `(-11, 21, 24, 28)`. -/
def rootHKRS3 : Quad := ⟨-11, 21, 24, 28⟩
/-- Square-hitting contrast root: `(9, 9, -4, 8)` (hits `9 = 3^2`; HKRS list `3n^2, 6n^2, n^4, 4n^4` obstructions for it). -/
def rootSquareContrast : Quad := ⟨9, 9, -4, 8⟩

theorem hkrs_root1_obstructed : HasHKRSObstruction rootHKRS1 := by
  apply mk_hkrs_root (xa := 1) (ya := 0) (xb := 1) (yb := 0) (xc := 1) (yc := 0) (xd := 1) (yd := 0)
  · exact ⟨by decide, by decide, by decide, by decide, by decide,
           by decide, by decide, by decide, by decide, by decide, by decide,
           prim_of_coprime_pair (by decide)⟩
  all_goals decide

theorem hkrs_root2_obstructed : HasHKRSObstruction rootHKRS2 := by
  apply mk_hkrs_root (xa := 1) (ya := 0) (xb := 1) (yb := 0) (xc := 1) (yc := 0) (xd := 1) (yd := 0)
  · exact ⟨by decide, by decide, by decide, by decide, by decide,
           by decide, by decide, by decide, by decide, by decide, by decide,
           prim_of_coprime_pair (by decide)⟩
  all_goals decide

theorem hkrs_root3_obstructed : HasHKRSObstruction rootHKRS3 := by
  apply mk_hkrs_root (xa := 1) (ya := 0) (xb := 1) (yb := 2) (xc := 1) (yc := 0) (xd := 1) (yd := 0)
  · exact ⟨by decide, by decide, by decide, by decide, by decide,
           by decide, by decide, by decide, by decide, by decide, by decide,
           prim_of_coprime_pair (by decide)⟩
  all_goals decide

/-- **T1c Master Export (HKRS *Annals of Math.*, 2024, for three packings):**
    Every quadruple in the infinite Apollonian orbits of `(-3, 5, 8, 8)`, `(-7, 17, 12, 20)`, and
    `(-11, 21, 24, 28)` contains zero perfect squares `m^2`, whereas the square-hitting contrast
    root `(9, 9, -4, 8)` lies on the Descartes cone and contains `9 = 3^2` (HKRS list `3n^2, 6n^2,
    n^4, 4n^4` obstructions for it). -/
theorem t1c_hkrs_apollonian_reciprocity_obstruction :
    (∀ q, InApollonianOrbit rootHKRS1 q → ∀ m : Int, q.a ≠ m * m ∧ q.b ≠ m * m ∧ q.c ≠ m * m ∧ q.d ≠ m * m) ∧
    (∀ q, InApollonianOrbit rootHKRS2 q → ∀ m : Int, q.a ≠ m * m ∧ q.b ≠ m * m ∧ q.c ≠ m * m ∧ q.d ≠ m * m) ∧
    (∀ q, InApollonianOrbit rootHKRS3 q → ∀ m : Int, q.a ≠ m * m ∧ q.b ≠ m * m ∧ q.c ≠ m * m ∧ q.d ≠ m * m) ∧
    (rootSquareContrast.descartes = 0 ∧ rootSquareContrast.a = 3 * 3) :=
  ⟨fun _ h => hkrs_orbit_no_squares hkrs_root1_obstructed h,
   fun _ h => hkrs_orbit_no_squares hkrs_root2_obstructed h,
   fun _ h => hkrs_orbit_no_squares hkrs_root3_obstructed h,
   ⟨by decide, by decide⟩⟩

/-! ### Part 4: Generalized Octahedral Circle Packings & `ℚ(√-2)` Reciprocity (`T1d`) -/

/-- Six-circle octahedral configuration with opposite pairs `(b1, b4)`, `(b2, b5)`, `(b3, b6)`. -/
structure OctSext where
  b1 : Int
  b2 : Int
  b3 : Int
  b4 : Int
  b5 : Int
  b6 : Int
deriving DecidableEq, Repr

/-- Octahedral Lorentzian-Descartes equations:
    `b1 + b4 = b2 + b5 = b3 + b6 = S` and `(b1 - b4)^2 + (b2 - b5)^2 + (b3 - b6)^2 = 2 * S^2`. -/
def IsOctahedral (x : OctSext) : Prop :=
  let S := x.b1 + x.b4
  x.b2 + x.b5 = S ∧ x.b3 + x.b6 = S ∧
  (x.b1 - x.b4) * (x.b1 - x.b4) + (x.b2 - x.b5) * (x.b2 - x.b5) +
  (x.b3 - x.b6) * (x.b3 - x.b6) = 2 * S * S

/-- The 8 octahedral face reflections parameterized by `s1 s2 s3 : Bool`
    (`false` picks `b1/b2/b3` on the fixed face; `true` picks `b4/b5/b6`). -/
def octRefl (s1 s2 s3 : Bool) (x : OctSext) : OctSext :=
  let S := x.b1 + x.b4
  let f1 := if s1 then x.b4 else x.b1
  let f2 := if s2 then x.b5 else x.b2
  let f3 := if s3 then x.b6 else x.b3
  let delta := 4 * (f1 + f2 + f3) - 2 * S
  { b1 := if s1 then x.b1 + delta else x.b1
    b2 := if s2 then x.b2 + delta else x.b2
    b3 := if s3 then x.b3 + delta else x.b3
    b4 := if s1 then x.b4 else x.b4 + delta
    b5 := if s2 then x.b5 else x.b5 + delta
    b6 := if s3 then x.b6 else x.b6 + delta }

inductive InOctOrbit (root : OctSext) : OctSext → Prop
  | base : InOctOrbit root root
  | step (s1 s2 s3 : Bool) {x} : InOctOrbit root x → InOctOrbit root (octRefl s1 s2 s3 x)

/-- All 8 octahedral face reflections are exact involutions preserving `IsOctahedral`. -/
theorem octRefl_involution_and_preserves (s1 s2 s3 : Bool) (x : OctSext) :
    octRefl s1 s2 s3 (octRefl s1 s2 s3 x) = x ∧
    (IsOctahedral x → IsOctahedral (octRefl s1 s2 s3 x)) := by
  cases x with
  | mk b1 b2 b3 b4 b5 b6 =>
    cases s1 <;> cases s2 <;> cases s3 <;>
      (constructor
       · simp [octRefl]; grind
       · intro ⟨h1, h2, h3⟩; simp only [IsOctahedral, octRefl] at *; refine ⟨by grind, by grind, by grind⟩)

/-- Exact octahedral `ℚ(√-2)` norm identity: for ANY face `(b1, b2, b3)` of an octahedral sextuple,
    `(2*(b1 + b2 + b3) - S)` is divisible by `4`, and letting `k = (2*(b1+b2+b3) - S) / 4`:
    `(b1 + b2) * (b1 + b3) = b1^2 + 2 * k^2`! -/
theorem oct_sqrt_neg2_norm {x : OctSext} (hO : IsOctahedral x) :
    let S := x.b1 + x.b4
    (2 * (x.b1 + x.b2 + x.b3) - S) % 4 = 0 ∧
    let k := (2 * (x.b1 + x.b2 + x.b3) - S) / 4
    (x.b1 + x.b2) * (x.b1 + x.b3) = x.b1 * x.b1 + 2 * k * k := by
  rcases hO with ⟨h25, h36, hsq⟩
  let S := x.b1 + x.b4
  have h16 : (2 * (x.b1 + x.b2 + x.b3) - S) * (2 * (x.b1 + x.b2 + x.b3) - S) =
             8 * ((x.b1 + x.b2) * (x.b1 + x.b3) - x.b1 * x.b1) := by
    dsimp [S] at h25 h36 hsq ⊢; grind
  have hdiv4 : (2 * (x.b1 + x.b2 + x.b3) - S) % 4 = 0 := by
    let u := 2 * (x.b1 + x.b2 + x.b3) - S
    have hu8 : (u * u) % 8 = 0 := by change ((2 * (x.b1 + x.b2 + x.b3) - S) * _) % 8 = 0; rw [h16]; omega
    have hu4 : u % 4 = 0 ∨ u % 4 = 1 ∨ u % 4 = 2 ∨ u % 4 = 3 := by omega
    rcases hu4 with h | h | h | h
    · exact h
    · exfalso
      have : (u * u) % 4 = 1 := by rw [Int.mul_emod, h]; decide
      omega
    · exfalso
      have : u = 4 * (u / 4) + 2 := by omega
      have hsq2 : u * u = 8 * (2 * (u / 4) * (u / 4) + 2 * (u / 4)) + 4 := by grind
      rw [hsq2] at hu8; omega
    · exfalso
      have : (u * u) % 4 = 1 := by rw [Int.mul_emod, h]; decide
      omega
  refine ⟨hdiv4, ?_⟩
  have h4k : 4 * ((2 * (x.b1 + x.b2 + x.b3) - S) / 4) = 2 * (x.b1 + x.b2 + x.b3) - S := by omega
  have h16k : 16 * (((2 * (x.b1 + x.b2 + x.b3) - S) / 4) * ((2 * (x.b1 + x.b2 + x.b3) - S) / 4)) =
              8 * ((x.b1 + x.b2) * (x.b1 + x.b3) - x.b1 * x.b1) := by
    have : 16 * (((2 * (x.b1 + x.b2 + x.b3) - S) / 4) * ((2 * (x.b1 + x.b2 + x.b3) - S) / 4)) =
           (4 * ((2 * (x.b1 + x.b2 + x.b3) - S) / 4)) * (4 * ((2 * (x.b1 + x.b2 + x.b3) - S) / 4)) := by grind
    rw [this, h4k, h16]
  grind

/-- Exact Octahedral Vieta sum-of-two-squares congruence under face reflection `(b1, b2, b3)`:
    `b6 * b6' - 4 * (b1^2 + b2^2) = b3 * (b3 - 4*b1 - 4*b2)`. -/
theorem oct_vieta_congruence {x : OctSext} (hO : IsOctahedral x) :
    let b6' := (octRefl false false false x).b6
    x.b6 * b6' - 4 * (x.b1 * x.b1 + x.b2 * x.b2) =
    x.b3 * (x.b3 - 4 * x.b1 - 4 * x.b2) := by
  rcases hO with ⟨h25, h36, hsq⟩
  simp only [octRefl, Bool.false_eq_true, ↓reduceIte]
  grind

/-- Exact Octahedral mod-8 parity conservation for our obstructed packing `(-6, 10, 17, 40, 24, 17)`:
    `(b1, b4) ≡ (2, 0) mod 8`, `(b2, b5) ≡ (2, 0) mod 8`, `(b3, b6) ≡ (1, 1) mod 8` is preserved
    by ALL 8 octahedral face reflections because `delta ≡ 0 (mod 8)` ALWAYS! -/
def octRootObstructed : OctSext := ⟨-6, 10, 17, 40, 24, 17⟩
def octRootStrip : OctSext := ⟨0, 0, 1, 2, 2, 1⟩

def HasOctMod8Pattern (x : OctSext) : Prop :=
  x.b1 % 8 = 2 ∧ x.b4 % 8 = 0 ∧ x.b2 % 8 = 2 ∧ x.b5 % 8 = 0 ∧ x.b3 % 8 = 1 ∧ x.b6 % 8 = 1

theorem oct_mod8_preserved (s1 s2 s3 : Bool) {x : OctSext} (h : HasOctMod8Pattern x) :
    HasOctMod8Pattern (octRefl s1 s2 s3 x) := by
  rcases h with ⟨h1, h4, h2, h5, h3, h6⟩
  cases s1 <;> cases s2 <;> cases s3 <;>
    (simp only [HasOctMod8Pattern, octRefl, Bool.false_eq_true, ↓reduceIte]; refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩)

/-- Exact Octahedral `ℚ(√-2)` binary form `g_a(x, y) = (a + c1) x^2 + 4 k xy + 2 (a + c2) y^2`
    satisfying `(a + c1) * g_a(x, y) = ((a + c1) x + 2 k y)^2 + 2 a^2 y^2`! -/
def octBqf (a c1 c2 k x y : Int) : Int :=
  (a + c1) * x * x + 4 * k * x * y + 2 * (a + c2) * y * y

theorem octBqf_identity {a c1 c2 k : Int} (hnorm : (a + c1) * (a + c2) = a * a + 2 * k * k) (x y : Int) :
    (a + c1) * octBqf a c1 c2 k x y = ((a + c1) * x + 2 * k * y) ^ 2 + 2 * (a * a) * (y * y) := by
  unfold octBqf; grind

/-- **Exact Octahedral `ℚ(√-2)` Obstruction Corollary for `(-6, 10, 17, 40, 24, 17)`:**
    For every sextuple in the infinite orbit of `(-6, 10, 17, 40, 24, 17)`:
    (1) `IsOctahedral x` and `HasOctMod8Pattern x` hold universally;
    (2) NO entry in slots `b1, b2` (`≡ 2 mod 8`) can ever be a square `m^2`, and NO entry in slots
        `b3, b6` (`≡ 1 mod 8`) can ever be `2 * m^2`;
    (3) At the obstructed root `(-6, 10, 17, 40, 24, 17)`, EVERY single circle `a` satisfies
        `jacobi (signedOddPart a) (a + b_adj) = -1` (verified for all 6 circles), contrasting with
        the unobstructed octahedral strip `(0, 0, 1, 2, 2, 1)` which hits both `1 = 1^2` and `2 = 2 * 1^2`! -/
theorem t1d_octahedral_lorentzian_and_sqrt_neg2_obstruction :
    (∀ s1 s2 s3 x, octRefl s1 s2 s3 (octRefl s1 s2 s3 x) = x ∧
      (IsOctahedral x → IsOctahedral (octRefl s1 s2 s3 x))) ∧
    (∀ x, IsOctahedral x →
      let S := x.b1 + x.b4
      (2 * (x.b1 + x.b2 + x.b3) - S) % 4 = 0 ∧
      let k := (2 * (x.b1 + x.b2 + x.b3) - S) / 4
      (x.b1 + x.b2) * (x.b1 + x.b3) = x.b1 * x.b1 + 2 * k * k) ∧
    (∀ x, InOctOrbit octRootObstructed x →
      IsOctahedral x ∧ HasOctMod8Pattern x ∧
      (∀ m : Int, x.b1 ≠ m * m ∧ x.b2 ≠ m * m ∧ x.b3 ≠ 2 * m * m ∧ x.b6 ≠ 2 * m * m)) ∧
    (jacobi (-3) 11 = -1 ∧ jacobi 5 27 = -1 ∧ jacobi 17 11 = -1 ∧
     jacobi 5 57 = -1 ∧ jacobi 3 41 = -1 ∧
     IsOctahedral octRootStrip ∧ octRootStrip.b3 = 1 * 1 ∧ octRootStrip.b4 = 2 * (1 * 1)) := by
  refine ⟨octRefl_involution_and_preserves, fun _ h => oct_sqrt_neg2_norm h, ?_, ?_⟩
  · intro x hx
    have hboth : IsOctahedral x ∧ HasOctMod8Pattern x := by
      induction hx with
      | base => exact ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩⟩
      | step s1 s2 s3 _ ih =>
        exact ⟨(octRefl_involution_and_preserves s1 s2 s3 _).2 ih.1, oct_mod8_preserved s1 s2 s3 ih.2⟩
    refine ⟨hboth.1, hboth.2, ?_⟩
    rcases hboth.2 with ⟨h1, h4, h2, h5, h3, h6⟩
    intro m
    have hm8 : (m * m) % 8 = 0 ∨ (m * m) % 8 = 1 ∨ (m * m) % 8 = 4 := by
      have hm4 : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
      have hmod : (m * m) % 8 = ((m % 4) * (m % 4)) % 8 := by
        have hm_eq : m = 4 * (m / 4) + m % 4 := by omega
        have hrepr : m * m = 8 * (2 * (m / 4) * (m / 4) + (m / 4) * (m % 4)) + (m % 4) * (m % 4) := by grind
        rw [hrepr, Int.mul_add_emod_self_left]
      rcases hm4 with hm4 | hm4 | hm4 | hm4 <;> (rw [hmod, hm4]; omega)
    have h2m8 : (2 * m * m) % 8 = 0 ∨ (2 * m * m) % 8 = 2 := by
      have h2eq : 2 * m * m = 2 * (m * m) := by grind
      rw [h2eq]
      rcases hm8 with h | h | h <;> (rw [Int.mul_emod, h]; decide)
    refine ⟨by omega, by omega, by omega, by omega⟩
  · exact ⟨by decide, by decide, by decide, by decide, by decide,
           ⟨by decide, by decide, by decide⟩, by decide, by decide⟩

/-! ### Part 5: General `d`-Dimensional Soddy–Gosset Integrality Dichotomy & 3D Contrast (`T1e`) -/

/-- Local integer finite sum helper over `0 .. n - 1` (zero external dependencies). -/
def sumNatInt (n : Nat) (f : Nat → Int) : Int :=
  match n with
  | 0 => 0
  | k + 1 => sumNatInt k f + f k

/-- Sum of an `Int`-valued function over `Fin n`. -/
def sumFinInt {n : Nat} (f : Fin n → Int) : Int :=
  sumNatInt n (fun i => if h : i < n then f ⟨i, h⟩ else 0)

theorem sumNatInt_eq_of_eq (n : Nat) (f g : Nat → Int) (h : ∀ i, i < n → f i = g i) :
    sumNatInt n f = sumNatInt n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumNatInt, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h k (Nat.lt_succ_self k)]

theorem sumFinInt_eq_of_eq {n : Nat} (f g : Fin n → Int) (h : ∀ i, f i = g i) :
    sumFinInt f = sumFinInt g := by
  unfold sumFinInt
  apply sumNatInt_eq_of_eq
  intro i hi
  simp only [hi, ↓reduceDIte, h ⟨i, hi⟩]

theorem sumFinInt_zero {n : Nat} : sumFinInt (fun _ : Fin n => (0 : Int)) = 0 := by
  unfold sumFinInt
  have haux : ∀ m : Nat, sumNatInt m (fun i => if _ : i < n then (0 : Int) else 0) = 0 := by
    intro m
    induction m with
    | zero => rfl
    | succ k ih => simp only [sumNatInt, ih]; split <;> omega
  exact haux n

theorem sumFinInt_update {n : Nat} (f : Fin n → Int) (k : Fin n) (v : Int) :
    sumFinInt (fun i => if i = k then v else f i) = sumFinInt f - f k + v := by
  unfold sumFinInt
  have haux : ∀ m (hm : m ≤ n),
      sumNatInt m (fun i => if h : i < n then (if (⟨i, h⟩ : Fin n) = k then v else f ⟨i, h⟩) else 0) =
      sumNatInt m (fun i => if h : i < n then f ⟨i, h⟩ else 0) + (if k.val < m then v - f k else 0) := by
    intro m
    induction m with
    | zero => intro _; simp [sumNatInt]
    | succ r ih =>
      intro hr
      have hr_lt : r < n := hr
      simp only [sumNatInt, ih (Nat.le_of_succ_le hr), hr_lt, ↓reduceDIte]
      by_cases hkr : k.val = r
      · have heq : (⟨r, hr_lt⟩ : Fin n) = k := Fin.ext hkr.symm
        have h1 : ¬ (k.val < r) := by omega
        have h2 : k.val < r + 1 := by omega
        simp only [heq, h1, h2, ↓reduceIte]; omega
      · have hne : (⟨r, hr_lt⟩ : Fin n) ≠ k := fun h => hkr (congrArg Fin.val h).symm
        by_cases hlt : k.val < r
        · have hlt' : k.val < r + 1 := by omega
          simp only [hne, hlt, hlt', ↓reduceIte]; omega
        · have hlt' : ¬ (k.val < r + 1) := by omega
          simp only [hne, hlt, hlt', ↓reduceIte]; omega
  have hfull := haux n (Nat.le_refl n)
  simp only [k.isLt, ↓reduceIte] at hfull
  dsimp only at hfull ⊢
  omega

/-- General `d`-dimensional Soddy–Gosset quadratic form on `d + 2` mutually tangent spheres:
    `(∑ b_i)^2 - d * ∑ b_i^2`. -/
def soddyQ (d : Nat) (b : Fin (d + 2) → Int) : Int :=
  (sumFinInt b) ^ 2 - (d : Int) * sumFinInt (fun i => b i * b i)

/-- General `d`-dimensional integer linear sphere reflection with multiplier `α`:
    replaces `b k` by `α * (∑_{i ≠ k} b_i) - b k`. -/
def soddyRefl (d : Nat) (α : Int) (k : Fin (d + 2)) (b : Fin (d + 2) → Int) : Fin (d + 2) → Int :=
  fun i => if i = k then α * (sumFinInt b - b k) - b k else b i

/-- Every `soddyRefl d α k` is an exact involution for all `d, α, k, b`. -/
theorem soddyRefl_involution (d : Nat) (α : Int) (k : Fin (d + 2)) (b : Fin (d + 2) → Int) :
    soddyRefl d α k (soddyRefl d α k b) = b := by
  have hS : sumFinInt (soddyRefl d α k b) - soddyRefl d α k b k = sumFinInt b - b k := by
    have hupd := sumFinInt_update b k (α * (sumFinInt b - b k) - b k)
    change sumFinInt (soddyRefl d α k b) = sumFinInt b - b k + (α * (sumFinInt b - b k) - b k) at hupd
    have hk : soddyRefl d α k b k = α * (sumFinInt b - b k) - b k := by simp [soddyRefl]
    omega
  funext i
  unfold soddyRefl
  by_cases hik : i = k
  · subst hik
    simp only [↓reduceIte]
    have hS' : sumFinInt (soddyRefl d α i b) - (α * (sumFinInt b - b i) - b i) = sumFinInt b - b i := by
      simpa [soddyRefl] using hS
    change α * (sumFinInt (soddyRefl d α i b) - (α * (sumFinInt b - b i) - b i)) - (α * (sumFinInt b - b i) - b i) = b i
    rw [hS']; omega
  · simp [hik]

/-- Exact change in `soddyQ d` under a single reflection `soddyRefl d α k`. -/
theorem soddyQ_refl_diff (d : Nat) (α : Int) (k : Fin (d + 2)) (b : Fin (d + 2) → Int) :
    soddyQ d (soddyRefl d α k b) - soddyQ d b =
    (α * (sumFinInt b - b k) - 2 * b k) * (sumFinInt b - b k) * (2 - ((d : Int) - 1) * α) := by
  let S_other := sumFinInt b - b k
  let x := b k
  let x' := α * S_other - x
  have hsum : sumFinInt (soddyRefl d α k b) = S_other + x' := by
    have h := sumFinInt_update b k x'
    change sumFinInt (soddyRefl d α k b) = sumFinInt b - b k + x' at h
    dsimp [S_other]; omega
  have hsq : sumFinInt (fun i => soddyRefl d α k b i * soddyRefl d α k b i) =
      sumFinInt (fun i => b i * b i) - x * x + x' * x' := by
    have hcongr : sumFinInt (fun i => soddyRefl d α k b i * soddyRefl d α k b i) =
        sumFinInt (fun i => if i = k then x' * x' else b i * b i) := by
      apply sumFinInt_eq_of_eq
      intro i
      unfold soddyRefl
      by_cases hik : i = k <;> simp [hik, x', S_other, x]
    rw [hcongr, sumFinInt_update (fun i => b i * b i) k (x' * x')]
  unfold soddyQ
  rw [hsum, hsq]
  have hSb : sumFinInt b = S_other + x := by dsimp [S_other, x]; omega
  rw [hSb]
  dsimp [x']
  grind

/-- **General `d`-Dimensional Soddy–Gosset Reflection Preservation Criterion:**
    For every dimension `d ≥ 2` and integer multiplier `α : Int`, the reflection `soddyRefl d α`
    preserves `soddyQ d` for all tuples and indices if and only if `(d - 1) * α = 2`. -/
theorem soddyRefl_preserves_soddyQ_iff (d : Nat) (hd : 2 ≤ d) (α : Int) :
    (∀ (b : Fin (d + 2) → Int) (k : Fin (d + 2)), soddyQ d (soddyRefl d α k b) = soddyQ d b) ↔
    ((d : Int) - 1) * α = 2 := by
  constructor
  · intro hall
    let i0 : Fin (d + 2) := ⟨0, by omega⟩
    let i1 : Fin (d + 2) := ⟨1, by omega⟩
    have hne : i0 ≠ i1 := fun h => by have := congrArg Fin.val h; dsimp [i0, i1] at this; omega
    let b1 : Fin (d + 2) → Int := fun i => if i = i1 then 1 else 0
    have hsum1 : sumFinInt b1 = 1 := by
      have h := sumFinInt_update (fun _ : Fin (d + 2) => (0 : Int)) i1 1
      rw [sumFinInt_zero] at h
      simpa [b1] using h
    have hb1_0 : b1 i0 = 0 := by simp [b1, hne]
    have hdiff1 := soddyQ_refl_diff d α i0 b1
    rw [hall b1 i0, hsum1, hb1_0] at hdiff1
    have hfac1 : α * (2 - ((d : Int) - 1) * α) = 0 := by grind
    rcases Int.mul_eq_zero.mp hfac1 with hα0 | hmain
    · exfalso
      let b2 : Fin (d + 2) → Int := fun i => if i = i0 then 1 else b1 i
      have hsum2 : sumFinInt b2 = 2 := by
        have h := sumFinInt_update b1 i0 1
        rw [hsum1, hb1_0] at h
        simpa [b2] using h
      have hb2_0 : b2 i0 = 1 := by simp [b2]
      have hdiff2 := soddyQ_refl_diff d α i0 b2
      rw [hall b2 i0, hsum2, hb2_0, hα0] at hdiff2
      omega
    · omega
  · intro hα b k
    have hdiff := soddyQ_refl_diff d α k b
    have hz : 2 - ((d : Int) - 1) * α = 0 := by omega
    rw [hz] at hdiff
    omega

/-- **Lagarias–Mallows–Wilks (2002) General `d`-Dimensional Soddy–Gosset Integrality Dichotomy:**
    For `d ≥ 2`, an integer linear sphere-inversion family preserving the `d`-dimensional
    Soddy–Gosset form `soddyQ d` exists if and only if `d = 2` (Apollonian, `α = 2`) or
    `d = 3` (3D Soddy, `α = 1`). -/
theorem soddy_general_d_integrality_dichotomy (d : Nat) (hd : 2 ≤ d) :
    (∃ α : Int, ∀ (b : Fin (d + 2) → Int) (k : Fin (d + 2)),
      soddyQ d (soddyRefl d α k b) = soddyQ d b) ↔ (d = 2 ∨ d = 3) := by
  constructor
  · rintro ⟨α, hα⟩
    have heq : ((d : Int) - 1) * α = 2 := (soddyRefl_preserves_soddyQ_iff d hd α).mp hα
    have hα_pos : 1 ≤ α := by
      by_cases hle : α ≤ 0
      · have hnp : ((d : Int) - 1) * α ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) hle
        omega
      · omega
    have hd_le3 : d ≤ 3 := by
      by_cases h4 : 4 ≤ d
      · have hge3 : (3 : Int) * 1 ≤ ((d : Int) - 1) * α :=
          Int.mul_le_mul (by omega) hα_pos (by decide) (by omega)
        omega
      · omega
    omega
  · rintro (rfl | rfl)
    · exact ⟨2, (soddyRefl_preserves_soddyQ_iff 2 (by decide) 2).mpr (by decide)⟩
    · exact ⟨1, (soddyRefl_preserves_soddyQ_iff 3 (by decide) 1).mpr (by decide)⟩

/-- Exact 3D Soddy sphere-packing Descartes form: `(∑ b_i)^2 - 3 * ∑ b_i^2`. -/
def soddy3Q (b1 b2 b3 b4 b5 : Int) : Int :=
  (b1 + b2 + b3 + b4 + b5) ^ 2 - 3 * (b1 ^ 2 + b2 ^ 2 + b3 ^ 2 + b4 ^ 2 + b5 ^ 2)

structure Soddy3 where
  b1 : Int
  b2 : Int
  b3 : Int
  b4 : Int
  b5 : Int
deriving DecidableEq, Repr

def soddy3Refl1 (s : Soddy3) : Soddy3 := ⟨s.b2 + s.b3 + s.b4 + s.b5 - s.b1, s.b2, s.b3, s.b4, s.b5⟩
def soddy3Refl2 (s : Soddy3) : Soddy3 := ⟨s.b1, s.b1 + s.b3 + s.b4 + s.b5 - s.b2, s.b3, s.b4, s.b5⟩
def soddy3Refl3 (s : Soddy3) : Soddy3 := ⟨s.b1, s.b2, s.b1 + s.b2 + s.b4 + s.b5 - s.b3, s.b4, s.b5⟩
def soddy3Refl4 (s : Soddy3) : Soddy3 := ⟨s.b1, s.b2, s.b3, s.b1 + s.b2 + s.b3 + s.b5 - s.b4, s.b5⟩
def soddy3Refl5 (s : Soddy3) : Soddy3 := ⟨s.b1, s.b2, s.b3, s.b4, s.b1 + s.b2 + s.b3 + s.b4 - s.b5⟩

/-- **T1e Master Export:**
    1. General `d`-dimensional Soddy–Gosset integrality dichotomy (Lagarias–Mallows–Wilks 2002):
       for all `d ≥ 2`, `soddyRefl d α` is an involution preserving `soddyQ d` iff `(d - 1) * α = 2`,
       so an integer reflection group preserving `soddyQ d` exists iff `d = 2 ∨ d = 3`.
    2. Arithmetic divisibility corollary `(d - 1) ∣ 2 ↔ d = 2 ∨ d = 3` for `d ≥ 2`.
    3. All five 3D Soddy reflections `soddy3Refl1`–`soddy3Refl5` are involutions preserving `soddy3Q`.
    4. 3D Soddy contrast witnesses (`(-5, 9, 12, 13, 16)` containing `9 = 3^2` and `16 = 4^2`, and
       `(-6, 13, 13, 13, 18)` reaching `25 = 5^2` in one reflection). -/
theorem t1e_soddy_dimension_dichotomy_and_3d_contrast :
    (∀ d : Nat, 2 ≤ d →
      ((∃ α : Int, ∀ (b : Fin (d + 2) → Int) (k : Fin (d + 2)),
        soddyQ d (soddyRefl d α k b) = soddyQ d b) ↔ (d = 2 ∨ d = 3))) ∧
    (∀ (d : Nat) (α : Int) (k : Fin (d + 2)) (b : Fin (d + 2) → Int),
      soddyRefl d α k (soddyRefl d α k b) = b) ∧
    (∀ d : Nat, 2 ≤ d → ((d - 1) ∣ 2 ↔ d = 2 ∨ d = 3)) ∧
    (∀ s : Soddy3,
      soddy3Refl1 (soddy3Refl1 s) = s ∧ soddy3Refl2 (soddy3Refl2 s) = s ∧
      soddy3Refl3 (soddy3Refl3 s) = s ∧ soddy3Refl4 (soddy3Refl4 s) = s ∧
      soddy3Refl5 (soddy3Refl5 s) = s ∧
      soddy3Q (soddy3Refl1 s).b1 (soddy3Refl1 s).b2 (soddy3Refl1 s).b3 (soddy3Refl1 s).b4 (soddy3Refl1 s).b5 =
        soddy3Q s.b1 s.b2 s.b3 s.b4 s.b5 ∧
      soddy3Q (soddy3Refl2 s).b1 (soddy3Refl2 s).b2 (soddy3Refl2 s).b3 (soddy3Refl2 s).b4 (soddy3Refl2 s).b5 =
        soddy3Q s.b1 s.b2 s.b3 s.b4 s.b5 ∧
      soddy3Q (soddy3Refl3 s).b1 (soddy3Refl3 s).b2 (soddy3Refl3 s).b3 (soddy3Refl3 s).b4 (soddy3Refl3 s).b5 =
        soddy3Q s.b1 s.b2 s.b3 s.b4 s.b5 ∧
      soddy3Q (soddy3Refl4 s).b1 (soddy3Refl4 s).b2 (soddy3Refl4 s).b3 (soddy3Refl4 s).b4 (soddy3Refl4 s).b5 =
        soddy3Q s.b1 s.b2 s.b3 s.b4 s.b5 ∧
      soddy3Q (soddy3Refl5 s).b1 (soddy3Refl5 s).b2 (soddy3Refl5 s).b3 (soddy3Refl5 s).b4 (soddy3Refl5 s).b5 =
        soddy3Q s.b1 s.b2 s.b3 s.b4 s.b5) ∧
    (soddy3Q (-5) 9 12 13 16 = 0 ∧ soddy3Q (-6) 13 13 13 18 = 0 ∧
     (soddy3Refl5 ⟨-6, 13, 13, 13, 18⟩).b5 = 15 ∧
     (soddy3Refl1 ⟨-6, 13, 13, 13, 18⟩).b1 = 63 ∧
     (soddy3Refl2 ⟨-6, 13, 13, 13, 18⟩).b2 = 25 ∧ 25 = 5 * 5) := by
  refine ⟨soddy_general_d_integrality_dichotomy, soddyRefl_involution, ?_, ?_, ?_⟩
  · intro d hd
    constructor
    · intro hdvd
      have hle := Nat.le_of_dvd (by decide) hdvd
      omega
    · rintro (rfl | rfl)
      · exact ⟨2, by decide⟩
      · exact ⟨1, by decide⟩
  · intro s
    cases s with
    | mk b1 b2 b3 b4 b5 =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        (simp only [soddy3Refl1, soddy3Refl2, soddy3Refl3, soddy3Refl4, soddy3Refl5, soddy3Q]; grind)
  · exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

end

end ApollonianSandpileMarkov.ApollonianReciprocity
