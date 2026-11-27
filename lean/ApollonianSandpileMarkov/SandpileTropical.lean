-- SPDX-License-Identifier: Apache-2.0
module

/-!
# Pillar II: Abelian Sandpile Toppling Laws, Exact Grid Laplacian Determinants (`ℤ²` & `𝔸₂`),
# Lattice-Laplacian Parity Obstructions, and Lattice-Polygon Edge-Normal Closure

Formalizes:
- `T2a`: Toppling commutativity, Laplacian odometer identity, Discrete Least Action bound, and
  uniqueness of legal stabilizing traces for symmetric zero-diagonal adjacency with arbitrary
  degrees (no sink condition and no termination theorem are formalized).
- `T2b`: Exact `det4 (gridLap 2) = 192`, direct Laplace determinant `detMat 9 (gridLap 3) = 100352`,
  `D_4` integer block-diagonalization (`4 * 14^2 * 128 = 100,352`), and explicit legal Dhar traces
  on `2×2` and `3×3` `ℤ²` grids (no Matrix–Tree or group-identity link is formalized).
- `T2c`: Torus Green's First Identity on `ℤ²`, periodic superharmonic constancy, one isotropic
  case `4u = 3(x^2+y^2) + ψ` with `Δu ≤ 3` impossible, and constant-Laplacian `2, 3` witnesses.
- `T2d`: Elementary `𝔸₂` even-Laplacian parity lemma (no prior statement found): under
  `M * u = A*x^2 + B*x*y + C*y^2 + D*x + E*y + ψ` (`M ≥ 1`, `ψ` doubly periodic),
  `M * K = 4*A - 2*B + 4*C`, and `Δ_{𝔸₂} u ≤ K`, necessarily `K % 2 = 0` (so `K = 5` is excluded
  in this class, while `K = 4, 2` are attained). Says nothing about finite sandpile configurations.
- `T2e`: Lattice-polygon edge-normal closure identity `∑ R_{90°}(v_{i+1} - v_i) = (0, 0)`,
  `det(v1,v2) = det(v2,v3) = det(v3,v1)` when `v1 + v2 + v3 = (0, 0)`, and closed numeric checks
  (the Kalinin–Shkolnikov theorem is not formalized).
- `T2f`: Exact `det4 (a2GridLap 2) = 1092`, direct Laplace determinant `detMat 9 (a2GridLap 3) = 5393920`,
  Klein-4 integer block-diagonalization (`7 * 28 * 40 * 688 = 5,393,920`), and explicit legal Dhar
  traces on `2×2` and `3×3` `𝔸₂` grids (no Matrix–Tree or group-identity link is formalized).
-/

namespace ApollonianSandpileMarkov.SandpileTropical

@[expose] public section

/-! ### Part 1: Finite-Sum & Torus-Summation Infrastructure -/

/-- Sum `f 0 + f 1 + ... + f (n - 1)` over `Int`. -/
def sumNat (n : Nat) (f : Nat → Int) : Int :=
  match n with
  | 0 => 0
  | k + 1 => sumNat k f + f k

theorem sumNat_add (n : Nat) (f g : Nat → Int) :
    sumNat n (fun i => f i + g i) = sumNat n f + sumNat n g := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumNat, ih]; omega

theorem sumNat_sub (n : Nat) (f g : Nat → Int) :
    sumNat n (fun i => f i - g i) = sumNat n f - sumNat n g := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumNat, ih]; omega

theorem sumNat_neg (n : Nat) (f : Nat → Int) :
    sumNat n (fun i => - f i) = - sumNat n f := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumNat, ih]; omega

theorem sumNat_const (n : Nat) (c : Int) :
    sumNat n (fun _ => c) = (n : Int) * c := by
  induction n with
  | zero => simp [sumNat]
  | succ k ih => simp only [sumNat, ih]; grind

theorem sumNat_eq_of_eq (n : Nat) (f g : Nat → Int) (h : ∀ i, i < n → f i = g i) :
    sumNat n f = sumNat n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumNat, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h k (Nat.lt_succ_self k)]

theorem sq_nonneg (a : Int) : 0 ≤ a * a := by
  by_cases h : 0 ≤ a
  · exact Int.mul_nonneg h h
  · have : a * a = (-a) * (-a) := by grind
    rw [this]; exact Int.mul_nonneg (by omega) (by omega)

theorem sumNat_nonneg (n : Nat) (f : Nat → Int) (h : ∀ i, i < n → 0 ≤ f i) :
    0 ≤ sumNat n f := by
  induction n with
  | zero => simp [sumNat]
  | succ k ih =>
    simp only [sumNat]
    have h1 := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have h2 := h k (Nat.lt_succ_self k)
    omega

theorem sumNat_nonpos (n : Nat) (f : Nat → Int) (h : ∀ i, i < n → f i ≤ 0) :
    sumNat n f ≤ 0 := by
  induction n with
  | zero => simp [sumNat]
  | succ k ih =>
    simp only [sumNat]
    have h1 := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have h2 := h k (Nat.lt_succ_self k)
    omega

theorem sumNat_eq_zero_of_nonneg (n : Nat) (f : Nat → Int)
    (hge : ∀ i, i < n → 0 ≤ f i) (hsum : sumNat n f = 0) :
    ∀ i, i < n → f i = 0 := by
  induction n with
  | zero => intro _ hi; omega
  | succ k ih =>
    simp only [sumNat] at hsum
    have h1 := sumNat_nonneg k f (fun i hi => hge i (Nat.lt_succ_of_lt hi))
    have h2 := hge k (Nat.lt_succ_self k)
    have hsk : sumNat k f = 0 := by omega
    have hfk : f k = 0 := by omega
    intro i hi
    by_cases hik : i = k
    · subst hik; exact hfk
    · exact ih (fun j hj => hge j (Nat.lt_succ_of_lt hj)) hsk i (by omega)

theorem sumNat_eq_zero_of_nonpos (n : Nat) (f : Nat → Int)
    (hle : ∀ i, i < n → f i ≤ 0) (hsum : sumNat n f = 0) :
    ∀ i, i < n → f i = 0 := by
  induction n with
  | zero => intro _ hi; omega
  | succ k ih =>
    simp only [sumNat] at hsum
    have h1 := sumNat_nonpos k f (fun i hi => hle i (Nat.lt_succ_of_lt hi))
    have h2 := hle k (Nat.lt_succ_self k)
    have hsk : sumNat k f = 0 := by omega
    have hfk : f k = 0 := by omega
    intro i hi
    by_cases hik : i = k
    · subst hik; exact hfk
    · exact ih (fun j hj => hle j (Nat.lt_succ_of_lt hj)) hsk i (by omega)

theorem sumNat_swap (m n : Nat) (f : Nat → Nat → Int) :
    sumNat m (fun i => sumNat n (fun j => f i j)) =
    sumNat n (fun j => sumNat m (fun i => f i j)) := by
  induction m with
  | zero =>
    simp only [sumNat]
    have h0 : sumNat n (fun _ => (0 : Int)) = 0 := by rw [sumNat_const]; simp
    exact h0.symm
  | succ k ih =>
    simp only [sumNat, ih, sumNat_add]

theorem sumNat_shift_periodic (P : Nat) (g : Int → Int)
    (hper : ∀ x : Int, g (x + (P : Int)) = g x) :
    sumNat P (fun i => g ((i : Int) + 1)) = sumNat P (fun i => g (i : Int)) := by
  cases P with
  | zero => rfl
  | succ k =>
    have htele : ∀ m : Nat,
        sumNat m (fun i => g ((i : Int) + 1) - g (i : Int)) = g (m : Int) - g 0 := by
      intro m
      induction m with
      | zero => simp [sumNat]
      | succ j ihj =>
        simp only [sumNat, ihj]
        have : ((j + 1 : Nat) : Int) = (j : Int) + 1 := by omega
        rw [this]; omega
    have hdiff := htele (k + 1)
    rw [sumNat_sub] at hdiff
    have hp : g (((k + 1 : Nat) : Int)) = g 0 := by
      have := hper 0; simpa using this
    omega

theorem sumNat_shift_neg_periodic (P : Nat) (g : Int → Int)
    (hper : ∀ x : Int, g (x + (P : Int)) = g x) :
    sumNat P (fun i => g ((i : Int) - 1)) = sumNat P (fun i => g (i : Int)) := by
  have h1 := sumNat_shift_periodic P (fun x => g (x - 1)) (fun x => by
    have : x + (P : Int) - 1 = (x - 1) + (P : Int) := by omega
    rw [this, hper])
  have h2 : sumNat P (fun i => g (((i : Int) + 1) - 1)) = sumNat P (fun i => g (i : Int)) := by
    apply sumNat_eq_of_eq; intro i _; congr 1; omega
  rw [h2] at h1
  exact h1.symm

/-- Shift a 2D periodic sum along `(dx, dy) = (1, -1)`! -/
theorem sumNat2_shift_diag_periodic (Px Py : Nat) (g : Int → Int → Int)
    (hx : ∀ x y : Int, g (x + (Px : Int)) y = g x y)
    (hy : ∀ x y : Int, g x (y + (Py : Int)) = g x y) :
    sumNat Px (fun i => sumNat Py (fun j => g ((i : Int) + 1) ((j : Int) - 1))) =
    sumNat Px (fun i => sumNat Py (fun j => g (i : Int) (j : Int))) := by
  have hstep1 :
      sumNat Px (fun i => sumNat Py (fun j => g ((i : Int) + 1) ((j : Int) - 1))) =
      sumNat Px (fun i => sumNat Py (fun j => g ((i : Int) + 1) (j : Int))) := by
    apply sumNat_eq_of_eq; intro i _
    exact sumNat_shift_neg_periodic Py (fun y => g ((i : Int) + 1) y) (fun y => hy _ y)
  rw [hstep1, sumNat_swap Px Py, sumNat_swap Px Py]
  apply sumNat_eq_of_eq; intro j _
  exact sumNat_shift_periodic Px (fun x => g x (j : Int)) (fun x => hx x _)

/-! ### Part 2: Universal Abelian Sandpile Confluence & Discrete Least Action (`T2a`) -/

/-- Sum over `Fin n`. -/
def sumFin {n : Nat} (f : Fin n → Int) : Int :=
  sumNat n (fun i => if h : i < n then f ⟨i, h⟩ else 0)

theorem sumFin_add {n : Nat} (f g : Fin n → Int) :
    sumFin (fun i => f i + g i) = sumFin f + sumFin g := by
  unfold sumFin
  rw [← sumNat_add]
  apply sumNat_eq_of_eq
  intro i hi; simp [hi]

theorem sumFin_single {n : Nat} (u : Fin n) (c : Int) :
    sumFin (fun j => if j = u then c else 0) = c := by
  unfold sumFin
  have haux : ∀ m (hm : m ≤ n),
      sumNat m (fun i => if h : i < n then (if (⟨i, h⟩ : Fin n) = u then c else 0) else 0) =
      if u.val < m then c else 0 := by
    intro m
    induction m with
    | zero => intro _; simp [sumNat]
    | succ k ih =>
      intro hle
      simp only [sumNat, ih (Nat.le_of_succ_le hle)]
      have hkn : k < n := hle
      simp only [hkn, ↓reduceDIte]
      by_cases huk : u.val = k
      · have heq : (⟨k, hkn⟩ : Fin n) = u := Fin.ext huk.symm
        have h1 : ¬ u.val < k := by omega
        have h2 : u.val < k + 1 := by omega
        simp [heq, h1, h2]
      · have hne : (⟨k, hkn⟩ : Fin n) ≠ u := fun h => huk (congrArg Fin.val h).symm
        by_cases hlt : u.val < k
        · have hlt' : u.val < k + 1 := by omega
          simp [hne, hlt, hlt']
        · have hlt' : ¬ u.val < k + 1 := by omega
          simp [hne, hlt, hlt']
  have hfull := haux n (Nat.le_refl n)
  simpa [u.isLt] using hfull

/-- An arbitrary finite Abelian sandpile graph on `n` non-sink vertices. -/
structure SandpileGraph (n : Nat) where
  adj : Fin n → Fin n → Nat
  deg : Fin n → Nat
  adj_diag : ∀ i : Fin n, adj i i = 0
  adj_symm : ∀ i j : Fin n, adj i j = adj j i

abbrev Config (n : Nat) := Fin n → Int

def IsStable {n : Nat} (G : SandpileGraph n) (s : Config n) : Prop :=
  ∀ i : Fin n, s i < (G.deg i : Int)

def topple {n : Nat} (G : SandpileGraph n) (u : Fin n) (s : Config n) : Config n :=
  fun i => if i = u then s i - (G.deg u : Int) else s i + (G.adj u i : Int)

def toppleList {n : Nat} (G : SandpileGraph n) : List (Fin n) → Config n → Config n
  | [], s => s
  | u :: us, s => toppleList G us (topple G u s)

def LegalTrace {n : Nat} (G : SandpileGraph n) : List (Fin n) → Config n → Prop
  | [], _ => True
  | u :: us, s => (G.deg u : Int) ≤ s u ∧ LegalTrace G us (topple G u s)

def countFin {n : Nat} (L : List (Fin n)) (i : Fin n) : Nat :=
  match L with
  | [] => 0
  | u :: us => (if u = i then 1 else 0) + countFin us i

/-- **Exact Toppling Commutativity:** `topple u` and `topple v` commute unconditionally! -/
theorem topple_comm {n : Nat} (G : SandpileGraph n) (u v : Fin n) (s : Config n) :
    topple G u (topple G v s) = topple G v (topple G u s) := by
  funext i
  unfold topple
  by_cases hiu : i = u <;> by_cases hiv : i = v
  · subst hiu; subst hiv; simp
  · simp [hiu]
    have : G.adj u i = 0 := hiu ▸ G.adj_diag i
    omega
  · simp [hiv]
    have : G.adj v i = 0 := hiv ▸ G.adj_diag i
    omega
  · simp [hiu, hiv]; omega

/-- **Exact Sandpile Laplacian Identity:** the final configuration depends ONLY on the
    odometer `countFin L`! -/
theorem toppleList_laplacian_identity {n : Nat} (G : SandpileGraph n)
    (L : List (Fin n)) (s : Config n) (i : Fin n) :
    toppleList G L s i =
    s i - (G.deg i : Int) * (countFin L i : Int) +
    sumFin (fun j => (G.adj j i : Int) * (countFin L j : Int)) := by
  induction L generalizing s with
  | nil =>
    simp only [toppleList, countFin, Int.natCast_zero, Int.mul_zero, Int.sub_zero]
    have h0 : sumFin (fun _ : Fin n => (0 : Int)) = 0 := by
      unfold sumFin
      have : sumNat n (fun j => if h : j < n then (0 : Int) else 0) = sumNat n (fun _ => 0) := by
        apply sumNat_eq_of_eq; intro j hj; simp [hj]
      rw [this, sumNat_const]; simp
    rw [h0, Int.add_zero]
  | cons u us ih =>
    simp only [toppleList, ih, countFin]
    have hsplit : sumFin (fun j => (G.adj j i : Int) * (((if u = j then 1 else 0) + countFin us j : Nat) : Int)) =
        sumFin (fun j => if j = u then (G.adj u i : Int) else 0) +
        sumFin (fun j => (G.adj j i : Int) * (countFin us j : Int)) := by
      rw [← sumFin_add]
      unfold sumFin
      apply sumNat_eq_of_eq; intro j hj
      simp only [hj, ↓reduceDIte]
      by_cases huj : u = ⟨j, hj⟩
      · subst huj; simp; grind
      · have hne : (⟨j, hj⟩ : Fin n) ≠ u := fun h => huj h.symm
        simp [huj, hne]
    rw [hsplit, sumFin_single u (G.adj u i : Int)]
    unfold topple
    by_cases hiu : i = u
    · subst hiu
      have hdiag : G.adj i i = 0 := G.adj_diag i
      simp only [↓reduceIte, hdiag, Int.natCast_zero]
      grind
    · have hui : u ≠ i := fun h => hiu h.symm
      simp only [hiu, hui, ↓reduceIte]
      grind

/-- Helper: stabilizing odometer predicate. -/
def IsStabilizingOdometer {n : Nat} (G : SandpileGraph n) (s : Config n) (w : Fin n → Nat) : Prop :=
  ∀ i : Fin n,
    s i - (G.deg i : Int) * (w i : Int) +
    sumFin (fun j => (G.adj j i : Int) * (w j : Int)) < (G.deg i : Int)

/-- **Universal Discrete Least Action Principle:**
    EVERY legal toppling sequence `L` starting from `s` fires every vertex at most `w i` times,
    for ANY stabilizing odometer `w`! -/
theorem discrete_least_action {n : Nat} (G : SandpileGraph n)
    (L : List (Fin n)) (s : Config n) (w : Fin n → Nat)
    (hleg : LegalTrace G L s) (hstab : IsStabilizingOdometer G s w) :
    ∀ i : Fin n, countFin L i ≤ w i := by
  induction L generalizing s w with
  | nil => intro i; simp [countFin]
  | cons u us ih =>
    rcases hleg with ⟨hu_ge, hus_leg⟩
    have hwu_pos : 1 ≤ w u := by
      by_cases h0 : w u = 0
      · exfalso
        have hst := hstab u
        have hsum0 : 0 ≤ sumFin (fun j => (G.adj j u : Int) * (w j : Int)) := by
          unfold sumFin
          apply sumNat_nonneg
          intro j hj
          simp only [hj, ↓reduceDIte]
          exact Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
        rw [h0] at hst
        simp at hst
        omega
      · omega
    let w' : Fin n → Nat := fun j => if j = u then w j - 1 else w j
    have hstab' : IsStabilizingOdometer G (topple G u s) w' := by
      intro i
      have hst := hstab i
      have hdiff_sum :
          sumFin (fun j => (G.adj j i : Int) * (w j : Int)) =
          (G.adj u i : Int) + sumFin (fun j => (G.adj j i : Int) * (w' j : Int)) := by
        rw [← sumFin_single u (G.adj u i : Int), ← sumFin_add]
        unfold sumFin
        apply sumNat_eq_of_eq; intro j hj
        simp only [hj, ↓reduceDIte]
        by_cases hju : (⟨j, hj⟩ : Fin n) = u
        · subst hju; simp only [w', ↓reduceIte]; grind
        · simp only [w', hju, ↓reduceIte]; omega
      unfold topple
      by_cases hiu : i = u
      · subst hiu
        have hdiag : G.adj i i = 0 := G.adj_diag i
        have hwsub : ((w i - 1 : Nat) : Int) = (w i : Int) - 1 := by omega
        simp only [w', ↓reduceIte, hdiag, Int.natCast_zero] at hdiff_sum ⊢
        rw [hwsub]
        have hmul : (G.deg i : Int) * ((w i : Int) - 1) = (G.deg i : Int) * (w i : Int) - (G.deg i : Int) := by grind
        omega
      · simp only [w', hiu, ↓reduceIte] at hdiff_sum ⊢
        omega
    have hsub := ih (topple G u s) w' hus_leg hstab'
    intro i
    have hi := hsub i
    simp only [countFin]
    by_cases hui : u = i
    · subst hui; simp only [w', ↓reduceIte] at hi ⊢; omega
    · have hiu : i ≠ u := fun h => hui h.symm
      simp only [w', hui, hiu, ↓reduceIte] at hi ⊢; omega

/-- **Universal Church–Rosser Confluence (Abelian Property):**
    ANY two legal stabilizing toppling sequences `L1, L2` from `s` produce the EXACT SAME
    odometer AND the EXACT SAME terminal stable configuration! -/
theorem sandpile_confluence {n : Nat} (G : SandpileGraph n) (s : Config n)
    (L1 L2 : List (Fin n))
    (hleg1 : LegalTrace G L1 s) (hstab1 : IsStable G (toppleList G L1 s))
    (hleg2 : LegalTrace G L2 s) (hstab2 : IsStable G (toppleList G L2 s)) :
    (∀ i : Fin n, countFin L1 i = countFin L2 i) ∧
    toppleList G L1 s = toppleList G L2 s := by
  have hw1 : IsStabilizingOdometer G s (countFin L1) := fun i => by
    rw [← toppleList_laplacian_identity G L1 s i]; exact hstab1 i
  have hw2 : IsStabilizingOdometer G s (countFin L2) := fun i => by
    rw [← toppleList_laplacian_identity G L2 s i]; exact hstab2 i
  have h12 := discrete_least_action G L1 s (countFin L2) hleg1 hw2
  have h21 := discrete_least_action G L2 s (countFin L1) hleg2 hw1
  have hcnt : ∀ i : Fin n, countFin L1 i = countFin L2 i := fun i => Nat.le_antisymm (h12 i) (h21 i)
  refine ⟨hcnt, ?_⟩
  funext i
  rw [toppleList_laplacian_identity G L1 s i, toppleList_laplacian_identity G L2 s i, hcnt i]
  congr 1
  unfold sumFin
  apply sumNat_eq_of_eq; intro j hj
  simp only [hj, ↓reduceDIte, hcnt ⟨j, hj⟩]

/-- **T2a Master Export.** -/
theorem t2a_abelian_sandpile_confluence_and_least_action :
    (∀ {n} (G : SandpileGraph n) (u v : Fin n) (s : Config n),
      topple G u (topple G v s) = topple G v (topple G u s)) ∧
    (∀ {n} (G : SandpileGraph n) (L : List (Fin n)) (s : Config n) (w : Fin n → Nat),
      LegalTrace G L s → IsStabilizingOdometer G s w → ∀ i, countFin L i ≤ w i) ∧
    (∀ {n} (G : SandpileGraph n) (s : Config n) (L1 L2 : List (Fin n)),
      LegalTrace G L1 s → IsStable G (toppleList G L1 s) →
      LegalTrace G L2 s → IsStable G (toppleList G L2 s) →
      (∀ i, countFin L1 i = countFin L2 i) ∧ toppleList G L1 s = toppleList G L2 s) :=
  ⟨fun G u v s => topple_comm G u v s,
   fun G L s w h1 h2 => discrete_least_action G L s w h1 h2,
   fun G s L1 L2 h1 h2 h3 h4 => sandpile_confluence G s L1 L2 h1 h2 h3 h4⟩

/-! ### Part 3: Dhar's Critical Group Identity & Exact Matrix-Tree Grid Orders (`T2b`) -/

/-- Concrete `k × k` open-boundary square grid sandpile graph (`deg = 4` everywhere). -/
def gridGraph (k : Nat) : SandpileGraph (k * k) where
  adj i j :=
    let r1 := i.val / k; let c1 := i.val % k
    let r2 := j.val / k; let c2 := j.val % k
    let dr := if r1 ≥ r2 then r1 - r2 else r2 - r1
    let dc := if c1 ≥ c2 then c1 - c2 else c2 - c1
    if dr + dc == 1 then 1 else 0
  deg _ := 4
  adj_diag i := by simp
  adj_symm i j := by
    dsimp only
    have h1 : (if i.val / k ≥ j.val / k then i.val / k - j.val / k else j.val / k - i.val / k) =
              (if j.val / k ≥ i.val / k then j.val / k - i.val / k else i.val / k - j.val / k) := by
      split <;> split <;> omega
    have h2 : (if i.val % k ≥ j.val % k then i.val % k - j.val % k else j.val % k - i.val % k) =
              (if j.val % k ≥ i.val % k then j.val % k - i.val % k else i.val % k - j.val % k) := by
      split <;> split <;> omega
    rw [h1, h2]

/-- Exact `2×2` and `3×3` grid Laplacian matrices `L_{ij} = deg(i) δ_{ij} - adj(i, j)`. -/
def gridLap (k : Nat) (i j : Fin (k * k)) : Int :=
  if i = j then 4 else - ((gridGraph k).adj i j : Int)

/-- Exact closed-form `4×4` determinant over `Int` (cofactor expansion). -/
def det2 (a b c d : Int) : Int := a * d - b * c

def det3 (m : Fin 3 → Fin 3 → Int) : Int :=
  m 0 0 * det2 (m 1 1) (m 1 2) (m 2 1) (m 2 2) -
  m 0 1 * det2 (m 1 0) (m 1 2) (m 2 0) (m 2 2) +
  m 0 2 * det2 (m 1 0) (m 1 1) (m 2 0) (m 2 1)

def minor4 (m : Fin 4 → Fin 4 → Int) (col : Fin 4) (r c : Fin 3) : Int :=
  let r' : Fin 4 := ⟨r.val + 1, by omega⟩
  let c' : Fin 4 := if c.val < col.val then ⟨c.val, by omega⟩ else ⟨c.val + 1, by omega⟩
  m r' c'

def det4 (m : Fin 4 → Fin 4 → Int) : Int :=
  m 0 0 * det3 (minor4 m 0) - m 0 1 * det3 (minor4 m 1) +
  m 0 2 * det3 (minor4 m 2) - m 0 3 * det3 (minor4 m 3)

/-! #### Zero-Mathlib General `n × n` Laplace Determinant & Verified Row-Operation Elimination -/

def skipFin {n : Nat} (k : Fin (n + 1)) (i : Fin n) : Fin (n + 1) :=
  if i.val < k.val then ⟨i.val, by omega⟩ else ⟨i.val + 1, by omega⟩

def minorMat {n : Nat} (M : Fin (n + 1) → Fin (n + 1) → Int) (r c : Fin (n + 1)) :
    Fin n → Fin n → Int :=
  fun i j => M (skipFin r i) (skipFin c j)

def signNat (j : Nat) : Int := if j % 2 = 0 then 1 else -1

/-- Textbook inductive Laplace expansion along row 0 for arbitrary `n × n` integer matrices. -/
def detMat : (n : Nat) → (Fin n → Fin n → Int) → Int
  | 0, _ => 1
  | n + 1, M =>
    sumFin (fun j : Fin (n + 1) => signNat j.val * M 0 j * detMat n (minorMat M 0 j))

theorem sumFin_eq_of_eq {n : Nat} (f g : Fin n → Int) (h : ∀ i, f i = g i) :
    sumFin f = sumFin g := by
  unfold sumFin
  apply sumNat_eq_of_eq
  intro i hi
  simp only [hi, ↓reduceDIte, h ⟨i, hi⟩]

theorem sumFin_zero {n : Nat} : sumFin (fun _ : Fin n => (0 : Int)) = 0 := by
  unfold sumFin
  have h : sumNat n (fun i => if _ : i < n then (0 : Int) else 0) = sumNat n (fun _ => 0) :=
    sumNat_eq_of_eq n _ _ (fun _ _ => by split <;> rfl)
  rw [h, sumNat_const]; simp

theorem sumFin_mul_left {n : Nat} (c : Int) (f : Fin n → Int) :
    sumFin (fun i => c * f i) = c * sumFin f := by
  unfold sumFin
  have haux : ∀ m (g : Nat → Int), sumNat m (fun i => c * g i) = c * sumNat m g := by
    intro m g
    induction m with
    | zero => simp [sumNat]
    | succ k ih => simp only [sumNat, ih]; grind
  rw [← haux]
  apply sumNat_eq_of_eq
  intro i hi; simp [hi]

theorem sumFin_swap {m n : Nat} (f : Fin m → Fin n → Int) :
    sumFin (fun i => sumFin (fun j => f i j)) = sumFin (fun j => sumFin (fun i => f i j)) := by
  unfold sumFin
  have h1 :
      sumNat m (fun i => if hi : i < m then sumNat n (fun j => if hj : j < n then f ⟨i, hi⟩ ⟨j, hj⟩ else 0) else 0) =
      sumNat m (fun i => sumNat n (fun j => if hi : i < m then (if hj : j < n then f ⟨i, hi⟩ ⟨j, hj⟩ else 0) else 0)) :=
    sumNat_eq_of_eq m _ _ (fun i hi => by simp only [hi, ↓reduceDIte])
  have h2 :
      sumNat n (fun j => if hj : j < n then sumNat m (fun i => if hi : i < m then f ⟨i, hi⟩ ⟨j, hj⟩ else 0) else 0) =
      sumNat n (fun j => sumNat m (fun i => if hi : i < m then (if hj : j < n then f ⟨i, hi⟩ ⟨j, hj⟩ else 0) else 0)) := by
    apply sumNat_eq_of_eq; intro j hj
    simp only [hj, ↓reduceDIte]
  rw [h1, h2, sumNat_swap]

theorem sumFin_skip {n : Nat} (k : Fin (n + 1)) (f : Fin (n + 1) → Int) :
    sumFin f = f k + sumFin (fun i : Fin n => f (skipFin k i)) := by
  unfold sumFin
  have haux : ∀ m (hm : m ≤ n + 1),
      sumNat m (fun j => if h : j < n + 1 then f ⟨j, h⟩ else 0) =
      (if k.val < m then f k else 0) +
      sumNat (if k.val < m then m - 1 else m) (fun i => if h : i < n then f (skipFin k ⟨i, h⟩) else 0) := by
    intro m
    induction m with
    | zero => intro _; simp [sumNat]
    | succ r ih =>
      intro hr
      have hr' : r ≤ n + 1 := Nat.le_of_succ_le hr
      have ih_r := ih hr'
      simp only [sumNat, ih_r]
      have hr_lt : r < n + 1 := hr
      simp only [hr_lt, ↓reduceDIte]
      by_cases hkr : k.val < r
      · have hkr1 : k.val < r + 1 := by omega
        have hsub : r + 1 - 1 = (r - 1) + 1 := by omega
        have hr1_lt : r - 1 < n := by omega
        have hskip : skipFin k ⟨r - 1, hr1_lt⟩ = ⟨r, hr_lt⟩ := by
          unfold skipFin
          have hnot : ¬ (r - 1 < k.val) := by omega
          simp only [hnot, ↓reduceIte]
          apply Fin.ext; dsimp; omega
        simp only [hkr, hkr1, ↓reduceIte, hsub, sumNat, hr1_lt, ↓reduceDIte, hskip]
        omega
      · by_cases hkeq : k.val = r
        · have hkr1 : k.val < r + 1 := by omega
          have hfk : (⟨r, hr_lt⟩ : Fin (n + 1)) = k := Fin.ext hkeq.symm
          have hsub : r + 1 - 1 = r := by omega
          simp only [hkr, hkr1, ↓reduceIte, hfk, hsub]
          omega
        · have hkr1 : ¬ (k.val < r + 1) := by omega
          have hrn : r < n := by omega
          have hskip : skipFin k ⟨r, hrn⟩ = ⟨r, hr_lt⟩ := by
            unfold skipFin
            have hlt : r < k.val := by omega
            simp only [hlt, ↓reduceIte]
          simp only [hkr, hkr1, ↓reduceIte, sumNat, hrn, ↓reduceDIte, hskip]
          omega
  have hfull := haux (n + 1) (Nat.le_refl _)
  have hklt : k.val < n + 1 := k.isLt
  simp only [hklt, ↓reduceIte, Nat.add_sub_cancel] at hfull
  exact hfull

theorem detMat_congr {n : Nat} {M N : Fin n → Fin n → Int} (h : ∀ i j, M i j = N i j) :
    detMat n M = detMat n N := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [detMat]
    apply sumFin_eq_of_eq
    intro j
    rw [h 0 j]
    congr 1
    exact ih (M := minorMat M 0 j) (N := minorMat N 0 j) (fun r c => h (skipFin 0 r) (skipFin j c))

def setRow {n : Nat} (M : Fin n → Fin n → Int) (r : Fin n) (v : Fin n → Int) :
    Fin n → Fin n → Int :=
  fun i j => if i = r then v j else M i j

theorem detMat_setRow_add {n : Nat} (M : Fin n → Fin n → Int) (r : Fin n) (u v : Fin n → Int) :
    detMat n (setRow M r (fun j => u j + v j)) =
    detMat n (setRow M r u) + detMat n (setRow M r v) := by
  induction n with
  | zero => exact r.elim0
  | succ k ih =>
    simp only [detMat]
    rw [← sumFin_add]
    apply sumFin_eq_of_eq
    intro j
    by_cases hr0 : r.val = 0
    · have hr : r = 0 := Fin.ext hr0
      subst hr
      have hmin : ∀ w, minorMat (setRow M 0 w) 0 j = minorMat M 0 j := by
        intro w; funext a b
        unfold minorMat setRow skipFin
        have hne : (⟨a.val + 1, by omega⟩ : Fin (k + 1)) ≠ 0 := fun h => by
          have := congrArg Fin.val h; simp at this
        simp [hne]
      rw [hmin, hmin, hmin]
      simp only [setRow, ↓reduceIte]; grind
    · let r' : Fin k := ⟨r.val - 1, by omega⟩
      have h0ne : (0 : Fin (k + 1)) ≠ r := fun h => hr0 (congrArg Fin.val h).symm
      have hmin : ∀ w, minorMat (setRow M r w) 0 j =
          setRow (minorMat M 0 j) r' (fun c => w (skipFin j c)) := by
        intro w; funext a b
        unfold minorMat setRow
        have hrow_eq : skipFin (0 : Fin (k + 1)) a = ⟨a.val + 1, by omega⟩ := by
          unfold skipFin; apply Fin.ext; simp
        have hiff : skipFin (0 : Fin (k + 1)) a = r ↔ a = r' := by
          rw [hrow_eq]
          constructor
          · intro h; apply Fin.ext; have := congrArg Fin.val h; dsimp [r'] at this ⊢; omega
          · intro h; apply Fin.ext; have := congrArg Fin.val h; dsimp [r'] at this ⊢; omega
        by_cases ha : a = r'
        · have ha' : skipFin (0 : Fin (k + 1)) a = r := hiff.mpr ha
          rw [ha', ha]; simp only [↓reduceIte]
        · have ha' : skipFin (0 : Fin (k + 1)) a ≠ r := fun h => ha (hiff.mp h)
          simp only [ha', ha, ↓reduceIte]
      rw [hmin, hmin, hmin, ih (minorMat M 0 j) r' (fun c => u (skipFin j c)) (fun c => v (skipFin j c))]
      simp only [setRow, h0ne, ↓reduceIte]; grind

theorem detMat_setRow_scale {n : Nat} (M : Fin n → Fin n → Int) (r : Fin n) (c : Int) (u : Fin n → Int) :
    detMat n (setRow M r (fun j => c * u j)) = c * detMat n (setRow M r u) := by
  induction n with
  | zero => exact r.elim0
  | succ k ih =>
    simp only [detMat]
    rw [← sumFin_mul_left]
    apply sumFin_eq_of_eq
    intro j
    by_cases hr0 : r.val = 0
    · have hr : r = 0 := Fin.ext hr0
      subst hr
      have hmin : ∀ w, minorMat (setRow M 0 w) 0 j = minorMat M 0 j := by
        intro w; funext a b
        unfold minorMat setRow skipFin
        have hne : (⟨a.val + 1, by omega⟩ : Fin (k + 1)) ≠ 0 := fun h => by
          have := congrArg Fin.val h; simp at this
        simp [hne]
      rw [hmin, hmin]
      simp only [setRow, ↓reduceIte]; grind
    · let r' : Fin k := ⟨r.val - 1, by omega⟩
      have h0ne : (0 : Fin (k + 1)) ≠ r := fun h => hr0 (congrArg Fin.val h).symm
      have hmin : ∀ w, minorMat (setRow M r w) 0 j =
          setRow (minorMat M 0 j) r' (fun col => w (skipFin j col)) := by
        intro w; funext a b
        unfold minorMat setRow
        have hrow_eq : skipFin (0 : Fin (k + 1)) a = ⟨a.val + 1, by omega⟩ := by
          unfold skipFin; apply Fin.ext; simp
        have hiff : skipFin (0 : Fin (k + 1)) a = r ↔ a = r' := by
          rw [hrow_eq]
          constructor
          · intro h; apply Fin.ext; have := congrArg Fin.val h; dsimp [r'] at this ⊢; omega
          · intro h; apply Fin.ext; have := congrArg Fin.val h; dsimp [r'] at this ⊢; omega
        by_cases ha : a = r'
        · have ha' : skipFin (0 : Fin (k + 1)) a = r := hiff.mpr ha
          rw [ha', ha]; simp only [↓reduceIte]
        · have ha' : skipFin (0 : Fin (k + 1)) a ≠ r := fun h => ha (hiff.mp h)
          simp only [ha', ha, ↓reduceIte]
      rw [hmin, hmin, ih (minorMat M 0 j) r' (fun col => u (skipFin j col))]
      simp only [setRow, h0ne, ↓reduceIte]; grind

def skip2 {n : Nat} (a b : Fin (n + 2)) (c : Fin n) : Fin (n + 2) :=
  let lo := if a.val ≤ b.val then a.val else b.val
  let hi := if a.val ≤ b.val then b.val else a.val
  if c.val < lo then ⟨c.val, by omega⟩
  else if c.val + 1 < hi then ⟨c.val + 1, by omega⟩
  else ⟨c.val + 2, by omega⟩

theorem skip2_comm {n : Nat} (a b : Fin (n + 2)) (c : Fin n) :
    skip2 a b c = skip2 b a c := by
  unfold skip2
  apply Fin.ext
  by_cases hab : a.val ≤ b.val <;> by_cases hba : b.val ≤ a.val
  · have heq : a.val = b.val := by omega
    simp [heq]
  · simp [hab, hba]
  · simp [hab, hba]
  · omega

theorem skipFin_skipFin_eq_skip2 {n : Nat} (a : Fin (n + 2)) (i : Fin (n + 1)) (c : Fin n) :
    skipFin a (skipFin i c) = skip2 a (skipFin a i) c := by
  apply Fin.ext
  dsimp only [skipFin, skip2]
  by_cases hci : c.val < i.val <;> by_cases hia : i.val < a.val
  · have h1 : c.val < a.val := by omega
    have h2 : ¬ (a.val ≤ i.val) := by omega
    simp only [hci, hia, h1, h2, ↓reduceIte]
  · by_cases hca : c.val < a.val
    · have h2 : a.val ≤ i.val + 1 := by omega
      simp only [hci, hia, hca, h2, ↓reduceIte]
    · have h2 : a.val ≤ i.val + 1 := by omega
      have h3 : c.val + 1 < i.val + 1 := by omega
      simp only [hci, hia, hca, h2, h3, ↓reduceIte]
  · have h2 : ¬ (a.val ≤ i.val) := by omega
    by_cases hc1a : c.val + 1 < a.val
    · have h3 : ¬ (c.val < i.val) := hci
      simp only [hci, hia, h2, hc1a, ↓reduceIte]
    · simp only [hci, hia, h2, hc1a, ↓reduceIte]
  · have h2 : a.val ≤ i.val + 1 := by omega
    have hca : ¬ (c.val < a.val) := by omega
    have hc1a : ¬ (c.val + 1 < a.val) := by omega
    have hc1i : ¬ (c.val + 1 < i.val + 1) := by omega
    simp only [hci, hia, h2, hca, hc1a, hc1i, ↓reduceIte]

theorem detMat_eq_zero_of_row0_eq_row1 {n : Nat} (M : Fin (n + 2) → Fin (n + 2) → Int)
    (heq : ∀ j : Fin (n + 2), M 0 j = M 1 j) : detMat (n + 2) M = 0 := by
  let F : Fin (n + 2) → Fin (n + 2) → Int := fun a b =>
    if a = b then 0
    else (if a.val < b.val then (-1 : Int) else 1) * signNat (a.val + b.val) *
         M 0 a * M 0 b * detMat n (fun (r : Fin n) (c : Fin n) => M ⟨r.val + 2, by omega⟩ (skip2 a b c))
  have hanti : ∀ a b : Fin (n + 2), F a b + F b a = 0 := by
    intro a b
    by_cases hab : a = b
    · subst hab; simp [F]
    · have hba : b ≠ a := fun h => hab h.symm
      have hcomm : (fun (r : Fin n) (c : Fin n) => M ⟨r.val + 2, by omega⟩ (skip2 a b c)) =
                   (fun (r : Fin n) (c : Fin n) => M ⟨r.val + 2, by omega⟩ (skip2 b a c)) := by
        funext r c; rw [skip2_comm]
      have hadd : a.val + b.val = b.val + a.val := Nat.add_comm _ _
      simp only [F, hab, hba, ↓reduceIte, hadd]
      rw [hcomm]
      by_cases hlt : a.val < b.val
      · have hnot : ¬ (b.val < a.val) := by omega
        simp only [hlt, hnot, ↓reduceIte]; grind
      · have hlt2 : b.val < a.val := by
          have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
          omega
        simp only [hlt, hlt2, ↓reduceIte]; grind
  have hS0 : sumFin (fun a => sumFin (fun b => F a b)) = 0 := by
    have h2 : sumFin (fun a => sumFin (fun b => F a b)) + sumFin (fun a => sumFin (fun b => F a b)) = 0 := by
      conv => lhs; rhs; rw [sumFin_swap]
      rw [← sumFin_add]
      have hinner : ∀ a, sumFin (fun b => F a b) + sumFin (fun b => F b a) = 0 := fun a => by
        rw [← sumFin_add]
        rw [sumFin_eq_of_eq _ (fun _ => 0) (fun b => hanti a b), sumFin_zero]
      rw [sumFin_eq_of_eq _ (fun _ => 0) hinner, sumFin_zero]
    omega
  have hmatch : detMat (n + 2) M = sumFin (fun a => sumFin (fun b => F a b)) := by
    simp only [detMat]
    apply sumFin_eq_of_eq
    intro a
    rw [sumFin_skip a]
    have hFaa : F a a = 0 := by simp [F]
    rw [hFaa, Int.zero_add, ← sumFin_mul_left]
    apply sumFin_eq_of_eq
    intro i
    have hne : a ≠ skipFin a i := by
      intro h
      have hv := congrArg Fin.val h
      unfold skipFin at hv
      split at hv <;> dsimp at hv <;> omega
    have hminor : minorMat (minorMat M 0 a) 0 i =
        fun (r : Fin n) (c : Fin n) => M ⟨r.val + 2, by omega⟩ (skip2 a (skipFin a i) c) := by
      funext r c
      unfold minorMat
      have hrow : skipFin (0 : Fin (n + 2)) (skipFin (0 : Fin (n + 1)) r) = ⟨r.val + 2, by omega⟩ := by
        unfold skipFin; apply Fin.ext; simp
      rw [hrow, skipFin_skipFin_eq_skip2]
    have hM1 : minorMat M 0 a 0 i = M 0 (skipFin a i) := by
      unfold minorMat
      have hrow1 : skipFin (0 : Fin (n + 2)) (0 : Fin (n + 1)) = 1 := by
        unfold skipFin; apply Fin.ext; simp
      rw [hrow1, ← heq]
    rw [hminor, hM1]
    simp only [F, hne, ↓reduceIte]
    have hsgn : signNat a.val * signNat i.val =
        (if a.val < (skipFin a i).val then (-1 : Int) else 1) * signNat (a.val + (skipFin a i).val) := by
      unfold signNat skipFin
      by_cases hia : i.val < a.val
      · have hnot : ¬ (a.val < i.val) := by omega
        simp only [hia, hnot, ↓reduceIte]
        have ha2 : a.val % 2 = 0 ∨ a.val % 2 = 1 := by omega
        have hi2 : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
        rcases ha2 with ha2 | ha2 <;> rcases hi2 with hi2 | hi2 <;>
          (have hsum : (a.val + i.val) % 2 = (a.val % 2 + i.val % 2) % 2 := Nat.add_mod _ _ 2;
           rw [ha2, hi2] at hsum ⊢; simp [hsum])
      · have hlt : a.val < i.val + 1 := by omega
        simp only [hia, hlt, ↓reduceIte]
        have ha2 : a.val % 2 = 0 ∨ a.val % 2 = 1 := by omega
        have hi2 : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
        rcases ha2 with ha2 | ha2 <;> rcases hi2 with hi2 | hi2 <;>
          (have hsum : (a.val + (i.val + 1)) % 2 = (a.val % 2 + (i.val % 2 + 1)) % 2 := by omega;
           rw [ha2, hi2] at hsum ⊢; simp [hsum])
    have hrearr : ∀ s1 s2 m1 m2 d : Int, s1 * m1 * (s2 * m2 * d) = (s1 * s2) * m1 * m2 * d :=
      fun _ _ _ _ _ => by grind
    rw [hrearr, hsgn]
  rw [hmatch, hS0]

theorem detMat_eq_zero_of_adj_eq :
    ∀ {n : Nat} (M : Fin n → Fin n → Int) (k : Nat) (hk : k + 1 < n),
      (∀ j : Fin n, M ⟨k, by omega⟩ j = M ⟨k + 1, hk⟩ j) → detMat n M = 0 := by
  intro n
  induction n with
  | zero => intro _ _ hk; omega
  | succ m ih =>
    intro M k hk heq
    cases k with
    | zero =>
      cases m with
      | zero => omega
      | succ m' =>
        exact detMat_eq_zero_of_row0_eq_row1 M (fun j => heq j)
    | succ k' =>
      conv => lhs; unfold detMat
      have hterm : ∀ j : Fin (m + 1),
          signNat j.val * M 0 j * detMat m (minorMat M 0 j) = 0 := by
        intro j
        have hz : detMat m (minorMat M 0 j) = 0 := by
          apply ih (minorMat M 0 j) k' (by omega)
          intro c
          unfold minorMat
          have h1 : skipFin (0 : Fin (m + 1)) ⟨k', by omega⟩ = ⟨k' + 1, by omega⟩ := by
            unfold skipFin; apply Fin.ext; simp
          have h2 : skipFin (0 : Fin (m + 1)) ⟨k' + 1, by omega⟩ = ⟨k' + 1 + 1, hk⟩ := by
            unfold skipFin; apply Fin.ext; simp
          rw [h1, h2]
          exact heq (skipFin j c)
        rw [hz]; simp
      rw [sumFin_eq_of_eq _ (fun _ => 0) hterm, sumFin_zero]

def swapAdj {n : Nat} (M : Fin n → Fin n → Int) (k : Nat) (hk : k + 1 < n) :
    Fin n → Fin n → Int :=
  fun i j =>
    if i.val = k then M ⟨k + 1, hk⟩ j
    else if i.val = k + 1 then M ⟨k, by omega⟩ j
    else M i j

theorem detMat_swapAdj {n : Nat} (M : Fin n → Fin n → Int) (k : Nat) (hk : k + 1 < n) :
    detMat n (swapAdj M k hk) = - detMat n M := by
  let rk : Fin n := ⟨k, by omega⟩
  let rk1 : Fin n := ⟨k + 1, hk⟩
  have hne : rk ≠ rk1 := fun h => by have := congrArg Fin.val h; dsimp [rk, rk1] at this; omega
  let r0 := M rk
  let r1 := M rk1
  let N := setRow (setRow M rk (fun j => r0 j + r1 j)) rk1 (fun j => r0 j + r1 j)
  have hN0 : detMat n N = 0 := by
    apply detMat_eq_zero_of_adj_eq N k hk
    intro j; simp [N, setRow, rk, rk1, hne]
  have hN_exp : detMat n N =
      detMat n (setRow (setRow M rk r0) rk1 r0) +
      detMat n (setRow (setRow M rk r1) rk1 r0) +
      detMat n (setRow (setRow M rk r0) rk1 r1) +
      detMat n (setRow (setRow M rk r1) rk1 r1) := by
    have h1 := detMat_setRow_add (setRow M rk (fun j => r0 j + r1 j)) rk1 r0 r1
    have hcomm : ∀ u v, setRow (setRow M rk u) rk1 v = setRow (setRow M rk1 v) rk u := by
      intro u v; funext i j; unfold setRow
      by_cases hi1 : i = rk1 <;> by_cases hi0 : i = rk
      · exact absurd (hi0.symm.trans hi1) hne
      · subst hi1; simp [hne.symm]
      · subst hi0; simp [hne]
      · simp [hi1, hi0]
    have h2 : detMat n (setRow (setRow M rk (fun j => r0 j + r1 j)) rk1 r0) =
              detMat n (setRow (setRow M rk r0) rk1 r0) + detMat n (setRow (setRow M rk r1) rk1 r0) := by
      rw [hcomm, detMat_setRow_add, ← hcomm, ← hcomm]
    have h3 : detMat n (setRow (setRow M rk (fun j => r0 j + r1 j)) rk1 r1) =
              detMat n (setRow (setRow M rk r0) rk1 r1) + detMat n (setRow (setRow M rk r1) rk1 r1) := by
      rw [hcomm, detMat_setRow_add, ← hcomm, ← hcomm]
    dsimp [N]; rw [h1, h2, h3]; omega
  have hz0 : detMat n (setRow (setRow M rk r0) rk1 r0) = 0 :=
    detMat_eq_zero_of_adj_eq _ k hk (fun j => by simp [setRow, rk, rk1, hne])
  have hz1 : detMat n (setRow (setRow M rk r1) rk1 r1) = 0 :=
    detMat_eq_zero_of_adj_eq _ k hk (fun j => by simp [setRow, rk, rk1, hne])
  have hM : detMat n (setRow (setRow M rk r0) rk1 r1) = detMat n M := by
    apply detMat_congr; intro i j
    unfold setRow
    by_cases hi1 : i = rk1
    · subst hi1; simp [r1]
    · by_cases hi0 : i = rk
      · subst hi0; simp [hi1, r0]
      · simp [hi1, hi0]
  have hS : detMat n (setRow (setRow M rk r1) rk1 r0) = detMat n (swapAdj M k hk) := by
    apply detMat_congr; intro i j
    unfold setRow swapAdj
    by_cases hi1 : i = rk1
    · subst hi1; simp [r0, rk, rk1]
    · by_cases hi0 : i = rk
      · subst hi0; simp [hi1, r1, rk, rk1]
      · have h1 : ¬ (i.val = k) := fun h => hi0 (Fin.ext h)
        have h2 : ¬ (i.val = k + 1) := fun h => hi1 (Fin.ext h)
        simp [hi1, hi0, h1, h2]
  rw [hN0, hz0, hz1, hM, hS] at hN_exp
  omega

theorem detMat_eq_zero_of_eq_rows_lt {n : Nat} :
    ∀ (d : Nat) (M : Fin n → Fin n → Int) (r1 r2 : Fin n),
      r2.val = r1.val + 1 + d → (∀ j : Fin n, M r1 j = M r2 j) → detMat n M = 0 := by
  intro d
  induction d with
  | zero =>
    intro M r1 r2 hr heq
    have hk : r1.val + 1 < n := by omega
    apply detMat_eq_zero_of_adj_eq M r1.val hk
    intro j
    have hr1 : (⟨r1.val, by omega⟩ : Fin n) = r1 := Fin.ext rfl
    have hr2 : (⟨r1.val + 1, hk⟩ : Fin n) = r2 := by apply Fin.ext; dsimp; omega
    rw [hr1, hr2]; exact heq j
  | succ d' ih =>
    intro M r1 r2 hr heq
    have hk : (r2.val - 1) + 1 < n := by omega
    let M' := swapAdj M (r2.val - 1) hk
    have hswap : detMat n M' = - detMat n M := detMat_swapAdj M (r2.val - 1) hk
    have hz : detMat n M' = 0 := by
      let r2' : Fin n := ⟨r2.val - 1, by omega⟩
      apply ih M' r1 r2' (by dsimp [r2']; omega)
      intro j
      have hr1_ne1 : ¬ (r1.val = r2.val - 1) := by omega
      have hr1_ne2 : ¬ (r1.val = (r2.val - 1) + 1) := by omega
      have hr2_eq : (⟨(r2.val - 1) + 1, hk⟩ : Fin n) = r2 := by apply Fin.ext; dsimp; omega
      simp only [M', swapAdj, hr1_ne1, hr1_ne2, ↓reduceIte, r2', hr2_eq]
      exact heq j
    omega

theorem detMat_eq_zero_of_eq_rows {n : Nat} (M : Fin n → Fin n → Int) (r1 r2 : Fin n)
    (hne : r1 ≠ r2) (heq : ∀ j : Fin n, M r1 j = M r2 j) : detMat n M = 0 := by
  by_cases hlt : r1.val < r2.val
  · exact detMat_eq_zero_of_eq_rows_lt (r2.val - r1.val - 1) M r1 r2 (by omega) heq
  · have hlt2 : r2.val < r1.val := by
      have : r1.val ≠ r2.val := fun h => hne (Fin.ext h)
      omega
    exact detMat_eq_zero_of_eq_rows_lt (r1.val - r2.val - 1) M r2 r1 (by omega) (fun j => (heq j).symm)

theorem detMat_addRowMul {n : Nat} (M : Fin n → Fin n → Int) (dst src : Fin n) (hne : dst ≠ src) (c : Int) :
    detMat n (setRow M dst (fun j => M dst j + c * M src j)) = detMat n M := by
  rw [detMat_setRow_add, detMat_setRow_scale]
  have hz : detMat n (setRow M dst (M src)) = 0 := by
    apply detMat_eq_zero_of_eq_rows _ dst src hne
    intro j; simp [setRow, hne.symm]
  have hM : detMat n (setRow M dst (M dst)) = detMat n M := by
    apply detMat_congr; intro i j; unfold setRow; by_cases h : i = dst <;> simp [h]
  rw [hz, hM]; simp

theorem detMat_eq_zero_of_col0_zero :
    ∀ {n : Nat} (M : Fin (n + 1) → Fin (n + 1) → Int),
      (∀ i : Fin (n + 1), M i 0 = 0) → detMat (n + 1) M = 0 := by
  intro n
  induction n with
  | zero =>
    intro M h0
    conv => lhs; unfold detMat
    have hterm : ∀ j : Fin 1, signNat j.val * M 0 j * detMat 0 (minorMat M 0 j) = 0 := by
      intro j
      have hj0 : j = 0 := Fin.ext (by omega)
      rw [hj0, h0 0]; simp
    rw [sumFin_eq_of_eq _ (fun _ => 0) hterm, sumFin_zero]
  | succ k ih =>
    intro M h0
    conv => lhs; unfold detMat
    have hterm : ∀ j : Fin (k + 2), signNat j.val * M 0 j * detMat (k + 1) (minorMat M 0 j) = 0 := by
      intro j
      by_cases hj : j.val = 0
      · have hj0 : j = 0 := Fin.ext hj
        rw [hj0, h0 0]; simp
      · have hz : detMat (k + 1) (minorMat M 0 j) = 0 := by
          apply ih (minorMat M 0 j)
          intro i
          unfold minorMat skipFin
          have hlt : (0 : Nat) < j.val := by omega
          simp only [Fin.val_zero, hlt, ↓reduceIte]
          exact h0 ⟨i.val + 1, by omega⟩
        rw [hz]; simp
    rw [sumFin_eq_of_eq _ (fun _ => 0) hterm, sumFin_zero]

def prodDiag : (n : Nat) → (Fin n → Fin n → Int) → Int
  | 0, _ => 1
  | n + 1, M => M 0 0 * prodDiag n (minorMat M 0 0)

theorem detMat_upperTriangular :
    ∀ {n : Nat} (M : Fin n → Fin n → Int),
      (∀ i j : Fin n, j.val < i.val → M i j = 0) → detMat n M = prodDiag n M := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ k ih =>
    intro M htri
    conv => lhs; unfold detMat
    conv => rhs; unfold prodDiag
    rw [sumFin_skip 0]
    have hrest : ∀ i : Fin k,
        signNat (skipFin 0 i).val * M 0 (skipFin 0 i) * detMat k (minorMat M 0 (skipFin 0 i)) = 0 := by
      intro i
      cases k with
      | zero => exact i.elim0
      | succ k' =>
        have hz : detMat (k' + 1) (minorMat M 0 (skipFin 0 i)) = 0 := by
          apply detMat_eq_zero_of_col0_zero
          intro r
          unfold minorMat skipFin
          simp only [Fin.val_zero]
          exact htri ⟨r.val + 1, by omega⟩ 0 (by simp)
        rw [hz]; simp
    rw [sumFin_eq_of_eq _ (fun _ => 0) hrest, sumFin_zero, Int.add_zero]
    have hs0 : signNat (0 : Fin (k + 1)).val = 1 := rfl
    rw [hs0, Int.one_mul]
    have hsub : detMat k (minorMat M 0 0) = prodDiag k (minorMat M 0 0) := by
      apply ih (minorMat M 0 0)
      intro a b hlt
      unfold minorMat skipFin
      exact htri ⟨a.val + 1, by omega⟩ ⟨b.val + 1, by omega⟩ (by dsimp; omega)
    rw [hsub]

/-- Concrete verified elementary row-operation checker on `List (List Int)`. -/
inductive RowOp (n : Nat) where
  | scale (r : Fin n) (c : Int)
  | addMul (dst src : Fin n) (c : Int)
  | divRow (r : Fin n) (d : Int)
  | cancel (g : Int)

theorem list_getD_eq_getElem {α : Type} (l : List α) (i : Nat) (d : α) (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD, List.getElem?_eq_getElem h, Option.getD_some]

def arrToMat {n : Nat} (arr : List (List Int)) : Fin n → Fin n → Int :=
  fun i j => (arr.getD i.val []).getD j.val 0

def matToArr {n : Nat} (M : Fin n → Fin n → Int) : List (List Int) :=
  (List.finRange n).map (fun i => (List.finRange n).map (fun j => M i j))

def setRowArr {n : Nat} (arr : List (List Int)) (r : Fin n) (newRow : List Int) : List (List Int) :=
  (List.finRange n).map (fun i => if i = r then newRow else arr.getD i.val [])

theorem arrToMat_matToArr {n : Nat} (M : Fin n → Fin n → Int) (i j : Fin n) :
    arrToMat (n := n) (matToArr M) i j = M i j := by
  unfold arrToMat matToArr
  have hi : i.val < ((List.finRange n).map (fun i => (List.finRange n).map (fun j => M i j))).length := by
    simp [i.isLt]
  rw [list_getD_eq_getElem _ _ _ hi]
  simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk, Fin.eta]
  have hj : j.val < ((List.finRange n).map (fun j => M i j)).length := by simp [j.isLt]
  rw [list_getD_eq_getElem _ _ _ hj]
  simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk, Fin.eta]

theorem arrToMat_setRowArr {n : Nat} (arr : List (List Int)) (r : Fin n) (newRow : List Int) (i j : Fin n) :
    arrToMat (n := n) (setRowArr arr r newRow) i j =
    setRow (arrToMat (n := n) arr) r (fun c => newRow.getD c.val 0) i j := by
  unfold arrToMat setRowArr setRow
  have hi : i.val < ((List.finRange n).map (fun i => if i = r then newRow else arr.getD i.val [])).length := by
    simp [i.isLt]
  rw [list_getD_eq_getElem _ _ _ hi]
  simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk, Fin.eta]
  by_cases hir : i = r <;> simp [hir]

def runRowOps {n : Nat} : List (RowOp n) → List (List Int) → Int → Int → Bool × List (List Int) × Int × Int
  | [], arr, num, den => (true, arr, num, den)
  | op :: ops, arr, num, den =>
    match op with
    | .scale r c =>
      let row := (List.finRange n).map (fun j => c * (arr.getD r.val []).getD j.val 0)
      runRowOps ops (setRowArr arr r row) (num * c) den
    | .addMul dst src c =>
      if dst = src then (false, arr, num, den)
      else
        let row := (List.finRange n).map (fun j =>
          (arr.getD dst.val []).getD j.val 0 + c * (arr.getD src.val []).getD j.val 0)
        runRowOps ops (setRowArr arr dst row) num den
    | .divRow r d =>
      if d = 0 then (false, arr, num, den)
      else
        let ok := (List.finRange n).all (fun j => decide (((arr.getD r.val []).getD j.val 0) % d = 0))
        if ok then
          let row := (List.finRange n).map (fun j => ((arr.getD r.val []).getD j.val 0) / d)
          runRowOps ops (setRowArr arr r row) num (den * d)
        else (false, arr, num, den)
    | .cancel g =>
      if g > 0 && decide (num % g = 0) && decide (den % g = 0) then
        runRowOps ops arr (num / g) (den / g)
      else (false, arr, num, den)

theorem runRowOps_sound {n : Nat} (ops : List (RowOp n)) (M0 : Fin n → Fin n → Int)
    (arr : List (List Int)) (num den : Int)
    (hinv : num * detMat n M0 = den * detMat n (arrToMat (n := n) arr))
    (hok : (runRowOps ops arr num den).1 = true) :
    let res := runRowOps ops arr num den
    res.2.2.1 * detMat n M0 = res.2.2.2 * detMat n (arrToMat (n := n) res.2.1) := by
  induction ops generalizing arr num den with
  | nil => exact hinv
  | cons op rest ih =>
    cases op with
    | scale r c =>
      simp only [runRowOps] at hok ⊢
      let row := (List.finRange n).map (fun j => c * (arr.getD r.val []).getD j.val 0)
      have hdet : detMat n (arrToMat (n := n) (setRowArr arr r row)) = c * detMat n (arrToMat (n := n) arr) := by
        have hcongr : detMat n (arrToMat (n := n) (setRowArr arr r row)) =
            detMat n (setRow (arrToMat (n := n) arr) r (fun j => c * arrToMat (n := n) arr r j)) := by
          apply detMat_congr; intro i j
          rw [arrToMat_setRowArr]
          unfold setRow
          by_cases hir : i = r
          · subst hir; simp only [↓reduceIte]
            have hj : j.val < row.length := by simp [row, j.isLt]
            rw [list_getD_eq_getElem _ _ _ hj]
            simp [row, arrToMat]
          · simp [hir]
        rw [hcongr, detMat_setRow_scale]
        congr 1
        apply detMat_congr; intro i j; unfold setRow; by_cases h : i = r <;> simp [h]
      apply ih (setRowArr arr r row) (num * c) den _ hok
      rw [hdet]; grind
    | addMul dst src c =>
      simp only [runRowOps] at hok ⊢
      by_cases hds : dst = src
      · simp only [hds, ↓reduceIte] at hok; exact Bool.noConfusion hok
      · simp only [hds, ↓reduceIte] at hok ⊢
        let row := (List.finRange n).map (fun j =>
          (arr.getD dst.val []).getD j.val 0 + c * (arr.getD src.val []).getD j.val 0)
        have hdet : detMat n (arrToMat (n := n) (setRowArr arr dst row)) = detMat n (arrToMat (n := n) arr) := by
          have hcongr : detMat n (arrToMat (n := n) (setRowArr arr dst row)) =
              detMat n (setRow (arrToMat (n := n) arr) dst
                (fun j => arrToMat (n := n) arr dst j + c * arrToMat (n := n) arr src j)) := by
            apply detMat_congr; intro i j
            rw [arrToMat_setRowArr]
            unfold setRow
            by_cases hid : i = dst
            · subst hid; simp only [↓reduceIte]
              have hj : j.val < row.length := by simp [row, j.isLt]
              rw [list_getD_eq_getElem _ _ _ hj]
              simp [row, arrToMat]
            · simp [hid]
          rw [hcongr, detMat_addRowMul _ dst src hds c]
        apply ih (setRowArr arr dst row) num den _ hok
        rw [hdet]; exact hinv
    | divRow r d =>
      simp only [runRowOps] at hok ⊢
      by_cases hd0 : d = 0
      · simp only [hd0, ↓reduceIte] at hok; exact Bool.noConfusion hok
      · simp only [hd0, ↓reduceIte] at hok ⊢
        cases hchk : (List.finRange n).all (fun j => decide (((arr.getD r.val []).getD j.val 0) % d = 0))
        · simp only [hchk, Bool.false_eq_true, ↓reduceIte] at hok
        · simp only [hchk, ↓reduceIte] at hok ⊢
          let row := (List.finRange n).map (fun j => ((arr.getD r.val []).getD j.val 0) / d)
          have hall : ∀ j : Fin n, ((arr.getD r.val []).getD j.val 0) % d = 0 := fun j =>
            of_decide_eq_true (List.all_eq_true.mp hchk j (List.mem_finRange j))
          have hdet : detMat n (arrToMat (n := n) arr) =
              d * detMat n (arrToMat (n := n) (setRowArr arr r row)) := by
            have hcongr : detMat n (arrToMat (n := n) arr) =
                detMat n (setRow (arrToMat (n := n) (setRowArr arr r row)) r
                  (fun j => d * arrToMat (n := n) (setRowArr arr r row) r j)) := by
              apply detMat_congr; intro i j
              unfold setRow
              by_cases hir : i = r
              · subst hir; simp only [↓reduceIte]
                rw [arrToMat_setRowArr]
                simp only [setRow, ↓reduceIte]
                have hj : j.val < row.length := by simp [row, j.isLt]
                rw [list_getD_eq_getElem _ _ _ hj]
                simp only [row, List.getElem_map, List.getElem_finRange, Fin.cast_mk, Fin.eta]
                have hmod := hall j
                have hdiv : d * (((arr.getD i.val []).getD j.val 0) / d) = (arr.getD i.val []).getD j.val 0 := by
                  have h := Int.emod_add_mul_ediv ((arr.getD i.val []).getD j.val 0) d
                  omega
                simpa [arrToMat] using hdiv.symm
              · simp only [hir, ↓reduceIte]
                rw [arrToMat_setRowArr]
                simp [setRow, hir]
            rw [hcongr, detMat_setRow_scale]
            congr 1
            apply detMat_congr; intro i j; unfold setRow; by_cases h : i = r <;> simp [h]
          apply ih (setRowArr arr r row) num (den * d) _ hok
          rw [hdet] at hinv; grind
    | cancel g =>
      simp only [runRowOps] at hok ⊢
      cases hc : (decide (g > 0) && decide (num % g = 0) && decide (den % g = 0))
      · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hok
      · simp only [hc, ↓reduceIte] at hok ⊢
        simp only [Bool.and_eq_true] at hc
        have hg : g > 0 := of_decide_eq_true hc.1.1
        have hnum : num % g = 0 := of_decide_eq_true hc.1.2
        have hden : den % g = 0 := of_decide_eq_true hc.2
        have hn_eq : g * (num / g) = num := by have := Int.emod_add_mul_ediv num g; omega
        have hd_eq : g * (den / g) = den := by have := Int.emod_add_mul_ediv den g; omega
        have hinv' : (num / g) * detMat n M0 = (den / g) * detMat n (arrToMat (n := n) arr) := by
          apply Int.eq_of_mul_eq_mul_left (a := g) (by omega)
          have h1 : g * ((num / g) * detMat n M0) = num * detMat n M0 := by rw [← Int.mul_assoc, hn_eq]
          have h2 : g * ((den / g) * detMat n (arrToMat (n := n) arr)) = den * detMat n (arrToMat (n := n) arr) := by
            rw [← Int.mul_assoc, hd_eq]
          rw [h1, h2, hinv]
        exact ih arr (num / g) (den / g) hinv' hok

def isUpperTriArr {n : Nat} (arr : List (List Int)) : Bool :=
  (List.finRange n).all (fun i =>
    (List.finRange n).all (fun j =>
      if j.val < i.val then decide ((arr.getD i.val []).getD j.val 0 = 0) else true))

def prodDiagArr {n : Nat} (arr : List (List Int)) : Int :=
  (List.finRange n).foldl (fun acc i => acc * (arr.getD i.val []).getD i.val 0) 1

theorem isUpperTri_of_bool {n : Nat} (arr : List (List Int)) (h : isUpperTriArr (n := n) arr = true) :
    ∀ i j : Fin n, j.val < i.val → arrToMat (n := n) arr i j = 0 := by
  intro i j hlt
  unfold isUpperTriArr at h
  have hi := List.all_eq_true.mp h i (List.mem_finRange i)
  have hj := List.all_eq_true.mp hi j (List.mem_finRange j)
  simp only [hlt, ↓reduceIte] at hj
  exact of_decide_eq_true hj

theorem foldl_mul_acc {α : Type} (l : List α) (a : Int) (f : α → Int) :
    l.foldl (fun acc i => acc * f i) a = a * l.foldl (fun acc i => acc * f i) 1 := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, Int.one_mul]
    rw [ih (a * f x), ih (f x)]; grind

theorem prodDiag_eq_foldl {n : Nat} (M : Fin n → Fin n → Int) :
    prodDiag n M = (List.finRange n).foldl (fun acc i => acc * M i i) 1 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [prodDiag, List.finRange_succ, List.foldl_cons, Int.one_mul]
    rw [foldl_mul_acc, ih (minorMat M 0 0)]
    congr 1
    rw [List.foldl_map]
    rfl

theorem detMat_eq_of_rowOps {n : Nat} (M : Fin n → Fin n → Int) (ops : List (RowOp n)) (target : Int)
    (hok :
      let res := runRowOps ops (matToArr M) 1 1
      res.1 && isUpperTriArr (n := n) res.2.1 &&
      decide (res.2.2.1 > 0) &&
      decide (res.2.2.2 * prodDiagArr (n := n) res.2.1 = res.2.2.1 * target)) :
    detMat n M = target := by
  dsimp only at hok
  simp only [Bool.and_eq_true] at hok
  have hrun : (runRowOps ops (matToArr M) 1 1).1 = true := hok.1.1.1
  have htri : isUpperTriArr (n := n) (runRowOps ops (matToArr M) 1 1).2.1 = true := hok.1.1.2
  have hpos : (runRowOps ops (matToArr M) 1 1).2.2.1 > 0 := of_decide_eq_true hok.1.2
  have heq : (runRowOps ops (matToArr M) 1 1).2.2.2 *
      prodDiagArr (n := n) (runRowOps ops (matToArr M) 1 1).2.1 =
      (runRowOps ops (matToArr M) 1 1).2.2.1 * target := of_decide_eq_true hok.2
  have hinit : (1 : Int) * detMat n M = (1 : Int) * detMat n (arrToMat (n := n) (matToArr M)) := by
    rw [detMat_congr (fun i j => (arrToMat_matToArr M i j).symm)]
  have hsnd := runRowOps_sound ops M (matToArr M) 1 1 hinit hrun
  dsimp only at hsnd
  have hdet_u : detMat n (arrToMat (n := n) (runRowOps ops (matToArr M) 1 1).2.1) =
      prodDiagArr (n := n) (runRowOps ops (matToArr M) 1 1).2.1 := by
    rw [detMat_upperTriangular _ (isUpperTri_of_bool _ htri), prodDiag_eq_foldl]
    rfl
  rw [hdet_u, heq] at hsnd
  exact Int.eq_of_mul_eq_mul_left (by omega) hsnd

def opsGridLap3 : List (RowOp 9) :=
  [.scale 1 4, .addMul 1 0 1, .scale 3 4, .addMul 3 0 1, .scale 2 15, .addMul 2 1 1,
   .scale 3 15, .addMul 3 1 1, .divRow 3 4, .cancel 4, .scale 4 15, .addMul 4 1 1,
   .scale 3 56, .addMul 3 2 1, .divRow 3 15, .cancel 15, .scale 4 14, .addMul 4 2 1,
   .divRow 4 15, .cancel 15, .scale 5 56, .addMul 5 2 1, .scale 4 209, .addMul 4 3 15,
   .divRow 4 14, .cancel 14, .scale 5 209, .addMul 5 3 1, .divRow 5 56, .cancel 56,
   .scale 6 209, .addMul 6 3 1, .scale 5 712, .addMul 5 4 225, .divRow 5 209, .cancel 209,
   .scale 6 178, .addMul 6 4 15, .divRow 6 209, .cancel 209, .scale 7 712, .addMul 7 4 1,
   .scale 6 2415, .addMul 6 5 17, .divRow 6 712, .cancel 712, .scale 7 161, .addMul 7 5 15,
   .divRow 7 11392, .cancel 11392, .scale 8 2415, .addMul 8 5 1, .divRow 8 4, .cancel 4,
   .scale 7 2237, .addMul 7 6 11, .divRow 7 1127, .cancel 1127, .scale 8 2237, .addMul 8 6 17,
   .divRow 8 135240, .cancel 16905, .scale 8 67, .addMul 8 7 11, .divRow 8 2237, .cancel 2237]

theorem detMat_gridLap3 : detMat 9 (gridLap 3) = 100352 :=
  detMat_eq_of_rowOps (gridLap 3) opsGridLap3 100352 (by decide)

/-- Exact `9×9` reflection similarity matrix `Q = P_3 ⊗ P_3` block-diagonalizing `L_{3×3}`
    over `ℤ` into `diag(4, B_2, B_2, B_4)` with `det(B_2) = 14`, `det(B_4) = 128`,
    yielding `det(L_{3×3}) = 4 * 14 * 14 * 128 = 100,352`! -/
def p3Mat (r c : Fin 3) : Int :=
  match r.val, c.val with
  | 0, 0 => 1  | 0, 1 => 1 | 0, 2 => 0
  | 1, 0 => 0  | 1, 1 => 0 | 1, 2 => 1
  | 2, 0 => -1 | 2, 1 => 1 | 2, 2 => 0
  | _, _ => 0

def p3Inv2 (r c : Fin 3) : Int :=
  match r.val, c.val with
  | 0, 0 => 1 | 0, 1 => 0 | 0, 2 => -1
  | 1, 0 => 1 | 1, 1 => 0 | 1, 2 => 1
  | 2, 0 => 0 | 2, 1 => 2 | 2, 2 => 0
  | _, _ => 0

/-- Basis-ordered `9×9` Kronecker transform `Q` mapping the 4 invariant subspaces:
    slot `0` = `(0,0)` (1D block `[4]`),
    slots `1,2` = `(0,1),(0,2)` (2D block `B2`),
    slots `3,4` = `(1,0),(2,0)` (2D block `B2`),
    slots `5,6,7,8` = `(1,1),(1,2),(2,1),(2,2)` (4D block `B4`). -/
def modeIdx (k : Fin 9) : Fin 3 × Fin 3 :=
  match k.val with
  | 0 => (0, 0)
  | 1 => (0, 1) | 2 => (0, 2)
  | 3 => (1, 0) | 4 => (2, 0)
  | 5 => (1, 1) | 6 => (1, 2) | 7 => (2, 1) | 8 => (2, 2)
  | _ => (0, 0)

def q9Mat (i j : Fin 9) : Int :=
  let (a, b) := modeIdx j
  p3Mat ⟨i.val / 3, by omega⟩ a * p3Mat ⟨i.val % 3, by omega⟩ b

def q9Inv4 (i j : Fin 9) : Int :=
  let (a, b) := modeIdx i
  p3Inv2 a ⟨j.val / 3, by omega⟩ * p3Inv2 b ⟨j.val % 3, by omega⟩

def b2Block (r c : Fin 2) : Int :=
  match r.val, c.val with
  | 0, 0 => 4  | 0, 1 => -1
  | 1, 0 => -2 | 1, 1 => 4
  | _, _ => 0

def b4Block (r c : Fin 4) : Int :=
  match r.val, c.val with
  | 0, 0 => 4  | 0, 1 => -1 | 0, 2 => -1 | 0, 3 => 0
  | 1, 0 => -2 | 1, 1 => 4  | 1, 2 => 0  | 1, 3 => -1
  | 2, 0 => -2 | 2, 1 => 0  | 2, 2 => 4  | 2, 3 => -1
  | 3, 0 => 0  | 3, 1 => -2 | 3, 2 => -2 | 3, 3 => 4
  | _, _ => 0

def blockDiag9 (i j : Fin 9) : Int :=
  if i.val = 0 ∧ j.val = 0 then 4
  else if h1 : 1 ≤ i.val ∧ i.val ≤ 2 ∧ 1 ≤ j.val ∧ j.val ≤ 2 then
    b2Block ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩
  else if h2 : 3 ≤ i.val ∧ i.val ≤ 4 ∧ 3 ≤ j.val ∧ j.val ≤ 4 then
    b2Block ⟨i.val - 3, by omega⟩ ⟨j.val - 3, by omega⟩
  else if h3 : 5 ≤ i.val ∧ 5 ≤ j.val then
    b4Block ⟨i.val - 5, by omega⟩ ⟨j.val - 5, by omega⟩
  else 0

def matMul9 (A B : Fin 9 → Fin 9 → Int) (i j : Fin 9) : Int :=
  sumFin (fun k : Fin 9 => A i k * B k j)

/-- Concrete `2×2` and `3×3` Dhar critical identity configurations and exact toppling witnesses. -/
def id2x2 : Config 4 := fun _ => 2

def id3x3 : Config 9 := fun i =>
  match i.val with
  | 0 => 2 | 1 => 1 | 2 => 2
  | 3 => 1 | 4 => 0 | 5 => 1
  | 6 => 2 | 7 => 1 | 8 => 2
  | _ => 0

/-- Structurally recursive unstable-vertex finder so `decide` reduces concrete traces in-kernel! -/
def findUnstableAux {n : Nat} (G : SandpileGraph n) (s : Config n) : Nat → Option (Fin n)
  | 0 => none
  | k + 1 =>
    match findUnstableAux G s k with
    | some u => some u
    | none =>
      if h : k < n then
        if (G.deg ⟨k, h⟩ : Int) ≤ s ⟨k, h⟩ then some ⟨k, h⟩ else none
      else none

def findUnstable {n : Nat} (G : SandpileGraph n) (s : Config n) : Option (Fin n) :=
  findUnstableAux G s n

def stabilizeTrace {n : Nat} (G : SandpileGraph n) (fuel : Nat) (s : Config n) : List (Fin n) :=
  match fuel with
  | 0 => []
  | f + 1 =>
    match findUnstable G s with
    | none => []
    | some u => u :: stabilizeTrace G f (topple G u s)

/-- Helper to check `LegalTrace` and `IsStable` decidably on finite concrete instances. -/
def isStableBool {n : Nat} (G : SandpileGraph n) (s : Config n) : Bool :=
  (List.finRange n).all (fun i => decide (s i < (G.deg i : Int)))

def legalTraceBool {n : Nat} (G : SandpileGraph n) : List (Fin n) → Config n → Bool
  | [], _ => true
  | u :: us, s => decide ((G.deg u : Int) ≤ s u) && legalTraceBool G us (topple G u s)

theorem isStable_of_bool {n : Nat} (G : SandpileGraph n) (s : Config n)
    (h : isStableBool G s = true) : IsStable G s := by
  intro i
  unfold isStableBool at h
  have hall := List.all_eq_true.mp h i (List.mem_finRange i)
  exact of_decide_eq_true hall

theorem legalTrace_of_bool {n : Nat} (G : SandpileGraph n) (L : List (Fin n)) (s : Config n)
    (h : legalTraceBool G L s = true) : LegalTrace G L s := by
  induction L generalizing s with
  | nil => trivial
  | cons u us ih =>
    simp only [legalTraceBool, Bool.and_eq_true] at h
    exact ⟨of_decide_eq_true h.1, ih (topple G u s) h.2⟩

/-- Explicit legal traces and intermediate stable states certifying `id2x2 ⊕ id2x2 = id2x2`,
    `id3x3 ⊕ id3x3 = id3x3`, and Dhar's formula `stab(2 μ_max - stab(2 μ_max)) = e`! -/
def s2Max2x2 : Config 4 := fun _ => 2

def s2Max3x3 : Config 9 := fun i =>
  match i.val with
  | 0 => 2 | 1 => 1 | 2 => 2
  | 3 => 1 | 4 => 2 | 5 => 1
  | 6 => 2 | 7 => 1 | 8 => 2
  | _ => 0

def traceId2x2 : List (Fin 4) := [0, 1, 2, 3]
def trace2Max2x2 : List (Fin 4) := [0, 1, 2, 0, 1, 2, 3, 3]
def traceDhar2x2 : List (Fin 4) := [0, 1, 2, 3]

def traceId3x3 : List (Fin 9) := [0, 2, 1, 6, 3, 8, 5, 7, 4]
def trace2Max3x3 : List (Fin 9) :=
  [0, 1, 2, 1, 0, 2, 3, 3, 4, 4, 1, 5, 4, 5, 6, 3, 0, 6, 7, 7, 4, 5, 2, 1, 7, 6, 3, 4, 8, 8, 5, 7, 8]
def traceDhar3x3 : List (Fin 9) :=
  [0, 1, 2, 3, 4, 1, 5, 4, 3, 0, 5, 2, 6, 7, 7, 4, 1, 6, 3, 8, 8, 5, 7, 4]

/-- Fast array-free concrete state evaluator using `List Int` (zero nested-closure blowup!). -/
def toppleListArr {n : Nat} (G : SandpileGraph n) (L : List (Fin n)) (s : List Int) : Bool × List Int :=
  match L with
  | [] => (true, s)
  | u :: us =>
    let su := s.getD u.val 0
    if (G.deg u : Int) ≤ su then
      let s' := (List.finRange n).map (fun i =>
        if i = u then s.getD i.val 0 - (G.deg u : Int)
        else s.getD i.val 0 + (G.adj u i : Int))
      toppleListArr G us s'
    else (false, s)

theorem toppleListArr_sound {n : Nat} (G : SandpileGraph n) (L : List (Fin n))
    (s : Config n) (arr : List Int)
    (harr : ∀ i : Fin n, arr.getD i.val 0 = s i)
    (hok : (toppleListArr G L arr).1 = true) :
    LegalTrace G L s ∧ ∀ i : Fin n, (toppleListArr G L arr).2.getD i.val 0 = toppleList G L s i := by
  induction L generalizing s arr with
  | nil => exact ⟨trivial, harr⟩
  | cons u us ih =>
    unfold toppleListArr at hok ⊢
    dsimp only at hok ⊢
    by_cases hge : (G.deg u : Int) ≤ arr.getD u.val 0
    · simp only [hge, ↓reduceIte] at hok ⊢
      have hge' : (G.deg u : Int) ≤ s u := by rw [← harr u]; exact hge
      let arr' := (List.finRange n).map (fun i =>
        if i = u then arr.getD i.val 0 - (G.deg u : Int)
        else arr.getD i.val 0 + (G.adj u i : Int))
      have harr' : ∀ i : Fin n, arr'.getD i.val 0 = topple G u s i := by
        intro i
        have hlen : arr'.length = n := by simp [arr']
        have hlt : i.val < arr'.length := by rw [hlen]; exact i.isLt
        rw [List.getD, List.getElem?_eq_getElem hlt, Option.getD_some]
        simp only [arr', List.getElem_map, List.getElem_finRange, Fin.cast_mk, Fin.eta]
        rw [harr i]
        rfl
      have hsub := ih (topple G u s) arr' harr' hok
      exact ⟨⟨hge', hsub.1⟩, hsub.2⟩
    · simp only [hge, ↓reduceIte] at hok
      exact Bool.noConfusion hok

/-- **T2b Master Export:**
    1. Exact `det4 (gridLap 2) = 192` and direct 9×9 Laplace determinant `detMat 9 (gridLap 3) = 100,352`.
    2. Exact `D_4` integer block-diagonalization `Q * (4 Q^{-1}) = 4 I_9`, `L Q = Q diag(4, B_2, B_2, B_4)`
       with block determinant product `4 * 14 * 14 * 128 = 100,352`.
    3. Explicit legal Dhar toppling traces on `2×2` (`[2,2,2,2]`) and `3×3` (`[2,1,2,1,0,1,2,1,2]`).
       (No Matrix–Tree or critical-group-identity theorem is formalized.) -/
theorem t2b_dhar_critical_identity_and_grid_orders :
    det4 (gridLap 2) = 192 ∧
    detMat 9 (gridLap 3) = 100352 ∧
    (∀ i j : Fin 9, matMul9 q9Mat q9Inv4 i j = if i = j then 4 else 0) ∧
    (∀ i j : Fin 9, matMul9 (gridLap 3) q9Mat i j = matMul9 q9Mat blockDiag9 i j) ∧
    (4 * det2 (b2Block 0 0) (b2Block 0 1) (b2Block 1 0) (b2Block 1 1) *
         det2 (b2Block 0 0) (b2Block 0 1) (b2Block 1 0) (b2Block 1 1) *
         det4 b4Block = 100352) ∧
    (LegalTrace (gridGraph 2) traceId2x2 (fun i => id2x2 i + id2x2 i) ∧
     toppleList (gridGraph 2) traceId2x2 (fun i => id2x2 i + id2x2 i) = id2x2 ∧
     IsStable (gridGraph 2) id2x2 ∧
     LegalTrace (gridGraph 2) trace2Max2x2 (fun _ => 6) ∧
     toppleList (gridGraph 2) trace2Max2x2 (fun _ => 6) = s2Max2x2 ∧
     IsStable (gridGraph 2) s2Max2x2 ∧
     LegalTrace (gridGraph 2) traceDhar2x2 (fun i => 6 - s2Max2x2 i) ∧
     toppleList (gridGraph 2) traceDhar2x2 (fun i => 6 - s2Max2x2 i) = id2x2) ∧
    (LegalTrace (gridGraph 3) traceId3x3 (fun i => id3x3 i + id3x3 i) ∧
     toppleList (gridGraph 3) traceId3x3 (fun i => id3x3 i + id3x3 i) = id3x3 ∧
     IsStable (gridGraph 3) id3x3 ∧
     LegalTrace (gridGraph 3) trace2Max3x3 (fun _ => 6) ∧
     toppleList (gridGraph 3) trace2Max3x3 (fun _ => 6) = s2Max3x3 ∧
     IsStable (gridGraph 3) s2Max3x3 ∧
     LegalTrace (gridGraph 3) traceDhar3x3 (fun i => 6 - s2Max3x3 i) ∧
     toppleList (gridGraph 3) traceDhar3x3 (fun i => 6 - s2Max3x3 i) = id3x3) := by
  have h2_id := toppleListArr_sound (gridGraph 2) traceId2x2 (fun i => id2x2 i + id2x2 i)
    ((List.finRange 4).map (fun i => id2x2 i + id2x2 i)) (by decide) (by decide)
  have h2_2m := toppleListArr_sound (gridGraph 2) trace2Max2x2 (fun _ => 6)
    ((List.finRange 4).map (fun _ => 6)) (by decide) (by decide)
  have h2_dh := toppleListArr_sound (gridGraph 2) traceDhar2x2 (fun i => 6 - s2Max2x2 i)
    ((List.finRange 4).map (fun i => 6 - s2Max2x2 i)) (by decide) (by decide)
  have h3_id := toppleListArr_sound (gridGraph 3) traceId3x3 (fun i => id3x3 i + id3x3 i)
    ((List.finRange 9).map (fun i => id3x3 i + id3x3 i)) (by decide) (by decide)
  have h3_2m := toppleListArr_sound (gridGraph 3) trace2Max3x3 (fun _ => 6)
    ((List.finRange 9).map (fun _ => 6)) (by decide) (by decide)
  have h3_dh := toppleListArr_sound (gridGraph 3) traceDhar3x3 (fun i => 6 - s2Max3x3 i)
    ((List.finRange 9).map (fun i => 6 - s2Max3x3 i)) (by decide) (by decide)
  refine ⟨by decide, detMat_gridLap3, by decide, by decide, by decide, ?_, ?_⟩
  · refine ⟨h2_id.1, funext (fun i => by rw [← h2_id.2 i]; revert i; decide),
            isStable_of_bool _ _ (by decide),
            h2_2m.1, funext (fun i => by rw [← h2_2m.2 i]; revert i; decide),
            isStable_of_bool _ _ (by decide),
            h2_dh.1, funext (fun i => by rw [← h2_dh.2 i]; revert i; decide)⟩
  · refine ⟨h3_id.1, funext (fun i => by rw [← h3_id.2 i]; revert i; decide),
            isStable_of_bool _ _ (by decide),
            h3_2m.1, funext (fun i => by rw [← h3_2m.2 i]; revert i; decide),
            isStable_of_bool _ _ (by decide),
            h3_dh.1, funext (fun i => by rw [← h3_dh.2 i]; revert i; decide)⟩

/-! ### Part 4: Levine–Pegden–Smart `ℤ²` Integer-Superharmonic Envelopes & Obstruction (`T2c`) -/

def lapZ2 (u : Int → Int → Int) (x y : Int) : Int :=
  u (x + 1) y + u (x - 1) y + u x (y + 1) + u x (y - 1) - 4 * u x y

def IsPeriodic2D (Px Py : Nat) (ψ : Int → Int → Int) : Prop :=
  1 ≤ Px ∧ 1 ≤ Py ∧
  (∀ x y : Int, ψ (x + (Px : Int)) y = ψ x y) ∧
  (∀ x y : Int, ψ x (y + (Py : Int)) = ψ x y)

/-- Periodic telescoping lemma: `∑_{Ω} Δ_{ℤ²} ψ = 0`. -/
theorem sum_lapZ2_periodic {Px Py : Nat} {ψ : Int → Int → Int} (hper : IsPeriodic2D Px Py ψ) :
    sumNat Px (fun i => sumNat Py (fun j => lapZ2 ψ (i : Int) (j : Int))) = 0 := by
  rcases hper with ⟨_, _, hx, hy⟩
  have h1 : sumNat Px (fun i => sumNat Py (fun j => ψ ((i : Int) + 1) (j : Int))) =
            sumNat Px (fun i => sumNat Py (fun j => ψ (i : Int) (j : Int))) := by
    rw [sumNat_swap Px Py, sumNat_swap Px Py]
    apply sumNat_eq_of_eq; intro j _
    exact sumNat_shift_periodic Px (fun x => ψ x (j : Int)) (fun x => hx x _)
  have h2 : sumNat Px (fun i => sumNat Py (fun j => ψ ((i : Int) - 1) (j : Int))) =
            sumNat Px (fun i => sumNat Py (fun j => ψ (i : Int) (j : Int))) := by
    rw [sumNat_swap Px Py, sumNat_swap Px Py]
    apply sumNat_eq_of_eq; intro j _
    exact sumNat_shift_neg_periodic Px (fun x => ψ x (j : Int)) (fun x => hx x _)
  have h3 : sumNat Px (fun i => sumNat Py (fun j => ψ (i : Int) ((j : Int) + 1))) =
            sumNat Px (fun i => sumNat Py (fun j => ψ (i : Int) (j : Int))) := by
    apply sumNat_eq_of_eq; intro i _
    exact sumNat_shift_periodic Py (fun y => ψ (i : Int) y) (fun y => hy _ y)
  have h4 : sumNat Px (fun i => sumNat Py (fun j => ψ (i : Int) ((j : Int) - 1))) =
            sumNat Px (fun i => sumNat Py (fun j => ψ (i : Int) (j : Int))) := by
    apply sumNat_eq_of_eq; intro i _
    exact sumNat_shift_neg_periodic Py (fun y => ψ (i : Int) y) (fun y => hy _ y)
  have hsplit : sumNat Px (fun i => sumNat Py (fun j => lapZ2 ψ (i : Int) (j : Int))) =
      sumNat Px (fun i => sumNat Py (fun j => ψ ((i : Int) + 1) (j : Int))) +
      sumNat Px (fun i => sumNat Py (fun j => ψ ((i : Int) - 1) (j : Int))) +
      sumNat Px (fun i => sumNat Py (fun j => ψ (i : Int) ((j : Int) + 1))) +
      sumNat Px (fun i => sumNat Py (fun j => ψ (i : Int) ((j : Int) - 1))) -
      4 * sumNat Px (fun i => sumNat Py (fun j => ψ (i : Int) (j : Int))) := by
    have h4mul : ∀ n (f : Nat → Int), sumNat n (fun i => 4 * f i) = 4 * sumNat n f := by
      intro n f; induction n with
      | zero => simp [sumNat]
      | succ k ih => simp only [sumNat, ih]; omega
    unfold lapZ2
    have hinner : ∀ i,
        sumNat Py (fun j => ψ ((i : Int) + 1) (j : Int) + ψ ((i : Int) - 1) (j : Int) +
          ψ (i : Int) ((j : Int) + 1) + ψ (i : Int) ((j : Int) - 1) - 4 * ψ (i : Int) (j : Int)) =
        sumNat Py (fun j => ψ ((i : Int) + 1) (j : Int)) +
        sumNat Py (fun j => ψ ((i : Int) - 1) (j : Int)) +
        sumNat Py (fun j => ψ (i : Int) ((j : Int) + 1)) +
        sumNat Py (fun j => ψ (i : Int) ((j : Int) - 1)) -
        4 * sumNat Py (fun j => ψ (i : Int) (j : Int)) := by
      intro i
      rw [sumNat_sub, sumNat_add, sumNat_add, sumNat_add, h4mul]
    rw [sumNat_eq_of_eq Px _ _ (fun i _ => hinner i),
        sumNat_sub, sumNat_add, sumNat_add, sumNat_add, h4mul]
  rw [hsplit, h1, h2, h3, h4]; omega

/-- **Discrete Green's First Identity on the `ℤ²` Torus:**
    `∑_Ω ((ψ(x+1,y) - ψ(x,y))^2 + (ψ(x,y+1) - ψ(x,y))^2) = - ∑_Ω ψ(x,y) * Δ_{ℤ²} ψ(x,y)`! -/
theorem green_identity_Z2 {Px Py : Nat} {ψ : Int → Int → Int} (hper : IsPeriodic2D Px Py ψ) :
    sumNat Px (fun i => sumNat Py (fun j =>
      (ψ ((i : Int) + 1) (j : Int) - ψ (i : Int) (j : Int)) *
        (ψ ((i : Int) + 1) (j : Int) - ψ (i : Int) (j : Int)) +
      (ψ (i : Int) ((j : Int) + 1) - ψ (i : Int) (j : Int)) *
        (ψ (i : Int) ((j : Int) + 1) - ψ (i : Int) (j : Int)))) =
    - sumNat Px (fun i => sumNat Py (fun j => ψ (i : Int) (j : Int) * lapZ2 ψ (i : Int) (j : Int))) := by
  rcases hper with ⟨_, _, hx, hy⟩
  have hxx : sumNat Px (fun i => sumNat Py (fun j => ψ ((i : Int) + 1) (j : Int) * ψ ((i : Int) + 1) (j : Int))) =
             sumNat Px (fun i => sumNat Py (fun j => ψ (i : Int) (j : Int) * ψ (i : Int) (j : Int))) := by
    rw [sumNat_swap Px Py, sumNat_swap Px Py]
    apply sumNat_eq_of_eq; intro j _
    exact sumNat_shift_periodic Px (fun x => ψ x (j : Int) * ψ x (j : Int)) (fun x => by rw [hx])
  have hyy : sumNat Px (fun i => sumNat Py (fun j => ψ (i : Int) ((j : Int) + 1) * ψ (i : Int) ((j : Int) + 1))) =
             sumNat Px (fun i => sumNat Py (fun j => ψ (i : Int) (j : Int) * ψ (i : Int) (j : Int))) := by
    apply sumNat_eq_of_eq; intro i _
    exact sumNat_shift_periodic Py (fun y => ψ (i : Int) y * ψ (i : Int) y) (fun y => by rw [hy])
  have hxm : sumNat Px (fun i => sumNat Py (fun j => ψ (i : Int) (j : Int) * ψ ((i : Int) - 1) (j : Int))) =
             sumNat Px (fun i => sumNat Py (fun j => ψ ((i : Int) + 1) (j : Int) * ψ (i : Int) (j : Int))) := by
    rw [sumNat_swap Px Py, sumNat_swap Px Py]
    apply sumNat_eq_of_eq; intro j _
    have hsh := sumNat_shift_periodic Px (fun x => ψ x (j : Int) * ψ (x - 1) (j : Int)) (fun x => by
      have hsub : x + (Px : Int) - 1 = (x - 1) + (Px : Int) := by omega
      rw [hx, hsub, hx])
    have heq : sumNat Px (fun i => ψ ((i : Int) + 1) (j : Int) * ψ (((i : Int) + 1) - 1) (j : Int)) =
               sumNat Px (fun i => ψ ((i : Int) + 1) (j : Int) * ψ (i : Int) (j : Int)) := by
      apply sumNat_eq_of_eq; intro i _; congr 2; omega
    rw [← hsh, heq]
  have hym : sumNat Px (fun i => sumNat Py (fun j => ψ (i : Int) (j : Int) * ψ (i : Int) ((j : Int) - 1))) =
             sumNat Px (fun i => sumNat Py (fun j => ψ (i : Int) ((j : Int) + 1) * ψ (i : Int) (j : Int))) := by
    apply sumNat_eq_of_eq; intro i _
    have hsh := sumNat_shift_periodic Py (fun y => ψ (i : Int) y * ψ (i : Int) (y - 1)) (fun y => by
      have hsub : y + (Py : Int) - 1 = (y - 1) + (Py : Int) := by omega
      rw [hy, hsub, hy])
    have heq : sumNat Py (fun j => ψ (i : Int) ((j : Int) + 1) * ψ (i : Int) (((j : Int) + 1) - 1)) =
               sumNat Py (fun j => ψ (i : Int) ((j : Int) + 1) * ψ (i : Int) (j : Int)) := by
      apply sumNat_eq_of_eq; intro j _; congr 2; omega
    rw [← hsh, heq]
  -- Expand both sides into sums of elementary products!
  have h2mul : ∀ n (f : Nat → Int), sumNat n (fun i => 2 * f i) = 2 * sumNat n f := by
    intro n f; induction n with | zero => simp [sumNat] | succ k ih => simp only [sumNat, ih]; omega
  have h4mul : ∀ n (f : Nat → Int), sumNat n (fun i => 4 * f i) = 4 * sumNat n f := by
    intro n f; induction n with | zero => simp [sumNat] | succ k ih => simp only [sumNat, ih]; omega
  let S00 := sumNat Px (fun i => sumNat Py (fun j => ψ (i : Int) (j : Int) * ψ (i : Int) (j : Int)))
  let Sx := sumNat Px (fun i => sumNat Py (fun j => ψ ((i : Int) + 1) (j : Int) * ψ (i : Int) (j : Int)))
  let Sy := sumNat Px (fun i => sumNat Py (fun j => ψ (i : Int) ((j : Int) + 1) * ψ (i : Int) (j : Int)))
  have hLHS :
      sumNat Px (fun i => sumNat Py (fun j =>
        (ψ ((i : Int) + 1) (j : Int) - ψ (i : Int) (j : Int)) *
          (ψ ((i : Int) + 1) (j : Int) - ψ (i : Int) (j : Int)) +
        (ψ (i : Int) ((j : Int) + 1) - ψ (i : Int) (j : Int)) *
          (ψ (i : Int) ((j : Int) + 1) - ψ (i : Int) (j : Int)))) =
      4 * S00 - 2 * Sx - 2 * Sy := by
    have hterm : ∀ i j : Nat,
        (ψ ((i : Int) + 1) (j : Int) - ψ (i : Int) (j : Int)) *
          (ψ ((i : Int) + 1) (j : Int) - ψ (i : Int) (j : Int)) +
        (ψ (i : Int) ((j : Int) + 1) - ψ (i : Int) (j : Int)) *
          (ψ (i : Int) ((j : Int) + 1) - ψ (i : Int) (j : Int)) =
        (ψ ((i : Int) + 1) (j : Int) * ψ ((i : Int) + 1) (j : Int) +
         ψ (i : Int) ((j : Int) + 1) * ψ (i : Int) ((j : Int) + 1) +
         2 * (ψ (i : Int) (j : Int) * ψ (i : Int) (j : Int))) -
        2 * (ψ ((i : Int) + 1) (j : Int) * ψ (i : Int) (j : Int)) -
        2 * (ψ (i : Int) ((j : Int) + 1) * ψ (i : Int) (j : Int)) := fun i j => by grind
    rw [sumNat_eq_of_eq Px _ _ (fun i _ => sumNat_eq_of_eq Py _ _ (fun j _ => hterm i j))]
    have hsplit : ∀ i,
        sumNat Py (fun j =>
          (ψ ((i : Int) + 1) (j : Int) * ψ ((i : Int) + 1) (j : Int) +
           ψ (i : Int) ((j : Int) + 1) * ψ (i : Int) ((j : Int) + 1) +
           2 * (ψ (i : Int) (j : Int) * ψ (i : Int) (j : Int))) -
          2 * (ψ ((i : Int) + 1) (j : Int) * ψ (i : Int) (j : Int)) -
          2 * (ψ (i : Int) ((j : Int) + 1) * ψ (i : Int) (j : Int))) =
        (sumNat Py (fun j => ψ ((i : Int) + 1) (j : Int) * ψ ((i : Int) + 1) (j : Int)) +
         sumNat Py (fun j => ψ (i : Int) ((j : Int) + 1) * ψ (i : Int) ((j : Int) + 1)) +
         2 * sumNat Py (fun j => ψ (i : Int) (j : Int) * ψ (i : Int) (j : Int))) -
        2 * sumNat Py (fun j => ψ ((i : Int) + 1) (j : Int) * ψ (i : Int) (j : Int)) -
        2 * sumNat Py (fun j => ψ (i : Int) ((j : Int) + 1) * ψ (i : Int) (j : Int)) := by
      intro i; rw [sumNat_sub, sumNat_sub, sumNat_add, sumNat_add, h2mul, h2mul, h2mul]
    rw [sumNat_eq_of_eq Px _ _ (fun i _ => hsplit i),
        sumNat_sub, sumNat_sub, sumNat_add, sumNat_add, h2mul, h2mul, h2mul, hxx, hyy]
    dsimp [S00, Sx, Sy]; omega
  have hRHS :
      sumNat Px (fun i => sumNat Py (fun j => ψ (i : Int) (j : Int) * lapZ2 ψ (i : Int) (j : Int))) =
      2 * Sx + 2 * Sy - 4 * S00 := by
    have hterm : ∀ i j : Nat,
        ψ (i : Int) (j : Int) * lapZ2 ψ (i : Int) (j : Int) =
        ψ ((i : Int) + 1) (j : Int) * ψ (i : Int) (j : Int) +
        ψ (i : Int) (j : Int) * ψ ((i : Int) - 1) (j : Int) +
        ψ (i : Int) ((j : Int) + 1) * ψ (i : Int) (j : Int) +
        ψ (i : Int) (j : Int) * ψ (i : Int) ((j : Int) - 1) -
        4 * (ψ (i : Int) (j : Int) * ψ (i : Int) (j : Int)) := fun i j => by unfold lapZ2; grind
    rw [sumNat_eq_of_eq Px _ _ (fun i _ => sumNat_eq_of_eq Py _ _ (fun j _ => hterm i j))]
    have hsplit : ∀ i,
        sumNat Py (fun j =>
          ψ ((i : Int) + 1) (j : Int) * ψ (i : Int) (j : Int) +
          ψ (i : Int) (j : Int) * ψ ((i : Int) - 1) (j : Int) +
          ψ (i : Int) ((j : Int) + 1) * ψ (i : Int) (j : Int) +
          ψ (i : Int) (j : Int) * ψ (i : Int) ((j : Int) - 1) -
          4 * (ψ (i : Int) (j : Int) * ψ (i : Int) (j : Int))) =
        sumNat Py (fun j => ψ ((i : Int) + 1) (j : Int) * ψ (i : Int) (j : Int)) +
        sumNat Py (fun j => ψ (i : Int) (j : Int) * ψ ((i : Int) - 1) (j : Int)) +
        sumNat Py (fun j => ψ (i : Int) ((j : Int) + 1) * ψ (i : Int) (j : Int)) +
        sumNat Py (fun j => ψ (i : Int) (j : Int) * ψ (i : Int) ((j : Int) - 1)) -
        4 * sumNat Py (fun j => ψ (i : Int) (j : Int) * ψ (i : Int) (j : Int)) := by
      intro i; rw [sumNat_sub, sumNat_add, sumNat_add, sumNat_add, h4mul]
    rw [sumNat_eq_of_eq Px _ _ (fun i _ => hsplit i),
        sumNat_sub, sumNat_add, sumNat_add, sumNat_add, h4mul, hxm, hym]
    dsimp [S00, Sx, Sy]; omega
  rw [hLHS, hRHS]; omega

/-- Periodic coordinate reduction modulo `(Px, Py)`. -/
theorem periodic_mod_eq {Px Py : Nat} {ψ : Int → Int → Int} (hper : IsPeriodic2D Px Py ψ) :
    ∀ x y : Int, ψ x y = ψ (x % (Px : Int)) (y % (Py : Int)) := by
  rcases hper with ⟨hPx, hPy, hx, hy⟩
  have hshiftX_nat : ∀ m : Nat, ∀ x y : Int, ψ (x + (Px : Int) * (m : Int)) y = ψ x y := by
    intro m
    induction m with
    | zero => intro x y; simp
    | succ n ih =>
      intro x y
      have : x + (Px : Int) * ((n + 1 : Nat) : Int) = (x + (Px : Int) * (n : Int)) + (Px : Int) := by grind
      rw [this, hx, ih]
  have hshiftX : ∀ k : Int, ∀ x y : Int, ψ (x + (Px : Int) * k) y = ψ x y := by
    intro k
    cases k with
    | ofNat m => exact hshiftX_nat m
    | negSucc m =>
      intro x y
      have hback : (x + (Px : Int) * Int.negSucc m) + (Px : Int) * ((m + 1 : Nat) : Int) = x := by
        have : Int.negSucc m = -((m + 1 : Nat) : Int) := rfl
        rw [this]; grind
      rw [← hshiftX_nat (m + 1) (x + (Px : Int) * Int.negSucc m) y, hback]
  have hshiftY_nat : ∀ m : Nat, ∀ x y : Int, ψ x (y + (Py : Int) * (m : Int)) = ψ x y := by
    intro m
    induction m with
    | zero => intro x y; simp
    | succ n ih =>
      intro x y
      have : y + (Py : Int) * ((n + 1 : Nat) : Int) = (y + (Py : Int) * (n : Int)) + (Py : Int) := by grind
      rw [this, hy, ih]
  have hshiftY : ∀ k : Int, ∀ x y : Int, ψ x (y + (Py : Int) * k) = ψ x y := by
    intro k
    cases k with
    | ofNat m => exact hshiftY_nat m
    | negSucc m =>
      intro x y
      have hback : (y + (Py : Int) * Int.negSucc m) + (Py : Int) * ((m + 1 : Nat) : Int) = y := by
        have : Int.negSucc m = -((m + 1 : Nat) : Int) := rfl
        rw [this]; grind
      rw [← hshiftY_nat (m + 1) x (y + (Py : Int) * Int.negSucc m), hback]
  intro x y
  have hx' : x = x % (Px : Int) + (Px : Int) * (x / (Px : Int)) := (Int.emod_add_mul_ediv x (Px : Int)).symm
  have hy' : y = y % (Py : Int) + (Py : Int) * (y / (Py : Int)) := (Int.emod_add_mul_ediv y (Py : Int)).symm
  conv => lhs; rw [hx', hy']
  rw [hshiftX, hshiftY]

/-- **Periodic Harmonic / Superharmonic Rigidity on `ℤ²`:**
    Any periodic `ψ` with `Δ_{ℤ²} ψ ≤ 0` everywhere is IDENTICALLY CONSTANT! -/
theorem periodic_superharmonic_Z2_const {Px Py : Nat} {ψ : Int → Int → Int}
    (hper : IsPeriodic2D Px Py ψ) (hsup : ∀ x y : Int, lapZ2 ψ x y ≤ 0) :
    ∀ x y : Int, ψ x y = ψ 0 0 := by
  have hsum0 := sum_lapZ2_periodic hper
  have hrow0 : ∀ i, i < Px → sumNat Py (fun j => lapZ2 ψ (i : Int) (j : Int)) = 0 :=
    sumNat_eq_zero_of_nonpos Px _ (fun i _ => sumNat_nonpos Py _ (fun j _ => hsup _ _)) hsum0
  have hcell0 : ∀ i j, i < Px → j < Py → lapZ2 ψ (i : Int) (j : Int) = 0 := fun i j hi hj =>
    sumNat_eq_zero_of_nonpos Py _ (fun j' _ => hsup _ _) (hrow0 i hi) j hj
  have hE0 : sumNat Px (fun i => sumNat Py (fun j =>
      (ψ ((i : Int) + 1) (j : Int) - ψ (i : Int) (j : Int)) *
        (ψ ((i : Int) + 1) (j : Int) - ψ (i : Int) (j : Int)) +
      (ψ (i : Int) ((j : Int) + 1) - ψ (i : Int) (j : Int)) *
        (ψ (i : Int) ((j : Int) + 1) - ψ (i : Int) (j : Int)))) = 0 := by
    rw [green_identity_Z2 hper]
    have hzero : sumNat Px (fun i => sumNat Py (fun j => ψ (i : Int) (j : Int) * lapZ2 ψ (i : Int) (j : Int))) = 0 := by
      have h1 : sumNat Px (fun i => sumNat Py (fun j => ψ (i : Int) (j : Int) * lapZ2 ψ (i : Int) (j : Int))) =
                sumNat Px (fun _ => 0) := by
        apply sumNat_eq_of_eq; intro i hi
        have h2 : sumNat Py (fun j => ψ (i : Int) (j : Int) * lapZ2 ψ (i : Int) (j : Int)) = sumNat Py (fun _ => 0) := by
          apply sumNat_eq_of_eq; intro j hj; rw [hcell0 i j hi hj]; simp
        rw [h2, sumNat_const]; simp
      rw [h1, sumNat_const]; simp
    rw [hzero]; simp
  have hErow : ∀ i, i < Px → sumNat Py (fun j =>
      (ψ ((i : Int) + 1) (j : Int) - ψ (i : Int) (j : Int)) *
        (ψ ((i : Int) + 1) (j : Int) - ψ (i : Int) (j : Int)) +
      (ψ (i : Int) ((j : Int) + 1) - ψ (i : Int) (j : Int)) *
        (ψ (i : Int) ((j : Int) + 1) - ψ (i : Int) (j : Int))) = 0 :=
    sumNat_eq_zero_of_nonneg Px _ (fun i _ => sumNat_nonneg Py _ (fun j _ => by
      have h1 := sq_nonneg (ψ ((i : Int) + 1) (j : Int) - ψ (i : Int) (j : Int))
      have h2 := sq_nonneg (ψ (i : Int) ((j : Int) + 1) - ψ (i : Int) (j : Int))
      omega)) hE0
  have hstep : ∀ i j, i < Px → j < Py →
      ψ ((i : Int) + 1) (j : Int) = ψ (i : Int) (j : Int) ∧
      ψ (i : Int) ((j : Int) + 1) = ψ (i : Int) (j : Int) := by
    intro i j hi hj
    have hz := sumNat_eq_zero_of_nonneg Py _ (fun j' _ => by
      have h1 := sq_nonneg (ψ ((i : Int) + 1) (j' : Int) - ψ (i : Int) (j' : Int))
      have h2 := sq_nonneg (ψ (i : Int) ((j' : Int) + 1) - ψ (i : Int) (j' : Int))
      omega) (hErow i hi) j hj
    have h1 := sq_nonneg (ψ ((i : Int) + 1) (j : Int) - ψ (i : Int) (j : Int))
    have h2 := sq_nonneg (ψ (i : Int) ((j : Int) + 1) - ψ (i : Int) (j : Int))
    have hs1 : (ψ ((i : Int) + 1) (j : Int) - ψ (i : Int) (j : Int)) *
               (ψ ((i : Int) + 1) (j : Int) - ψ (i : Int) (j : Int)) = 0 := by omega
    have hs2 : (ψ (i : Int) ((j : Int) + 1) - ψ (i : Int) (j : Int)) *
               (ψ (i : Int) ((j : Int) + 1) - ψ (i : Int) (j : Int)) = 0 := by omega
    have hd1 := (Int.mul_eq_zero.mp hs1).elim id id
    have hd2 := (Int.mul_eq_zero.mp hs2).elim id id
    omega
  have hbox : ∀ i j, i < Px → j < Py → ψ (i : Int) (j : Int) = ψ 0 0 := by
    intro i j hi hj
    have hxwalk : ∀ a, a ≤ i → ψ (a : Int) (j : Int) = ψ 0 (j : Int) := by
      intro a
      induction a with
      | zero => intro _; rfl
      | succ k ih =>
        intro hk
        have hst := (hstep k j (by omega) hj).1
        have hcast : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
        rw [hcast, hst, ih (by omega)]
    have hywalk : ∀ b, b ≤ j → ψ 0 (b : Int) = ψ 0 0 := by
      intro b
      induction b with
      | zero => intro _; rfl
      | succ k ih =>
        intro hk
        have hst := (hstep 0 k hper.1 (by omega)).2
        simp only [Int.natCast_zero] at hst
        have hcast : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
        rw [hcast, hst, ih (by omega)]
    rw [hxwalk i (Nat.le_refl i), hywalk j (Nat.le_refl j)]
  intro x y
  rw [periodic_mod_eq hper x y]
  rcases hper with ⟨hPx, hPy, _, _⟩
  have hxm0 : 0 ≤ x % (Px : Int) := Int.emod_nonneg x (by omega)
  have hxm1 : x % (Px : Int) < (Px : Int) := Int.emod_lt_of_pos x (by omega)
  have hym0 : 0 ≤ y % (Py : Int) := Int.emod_nonneg y (by omega)
  have hym1 : y % (Py : Int) < (Py : Int) := Int.emod_lt_of_pos y (by omega)
  have hcastx : ((x % (Px : Int)).toNat : Int) = x % (Px : Int) := Int.toNat_of_nonneg hxm0
  have hcasty : ((y % (Py : Int)).toNat : Int) = y % (Py : Int) := Int.toNat_of_nonneg hym0
  rw [← hcastx, ← hcasty]
  exact hbox _ _ (by omega) (by omega)

/-- **Isotropic `ℤ²` Max-Sea Obstruction (Levine–Pegden–Smart):**
    NO integer function `u : ℤ² → ℤ` with isotropic Hessian `(3/4) I_2` plus a periodic remainder
    `ψ` (`4 * u(x, y) = 3*(x^2 + y^2) + ψ(x, y)`) can satisfy `Δ_{ℤ²} u ≤ 3` everywhere! -/
theorem isotropic_z2_max_sea_obstruction {Px Py : Nat} {u ψ : Int → Int → Int}
    (hper : IsPeriodic2D Px Py ψ)
    (hform : ∀ x y : Int, 4 * u x y = 3 * (x * x + y * y) + ψ x y)
    (hsup : ∀ x y : Int, lapZ2 u x y ≤ 3) : False := by
  have hlap_psi : ∀ x y : Int, lapZ2 ψ x y ≤ 0 := by
    intro x y
    have h4 : 4 * lapZ2 u x y = 12 + lapZ2 ψ x y := by
      unfold lapZ2
      have h00 := hform x y
      have h10 := hform (x + 1) y
      have hm0 := hform (x - 1) y
      have h01 := hform x (y + 1)
      have h0m := hform x (y - 1)
      grind
    have hle := hsup x y
    omega
  have hconst := periodic_superharmonic_Z2_const hper hlap_psi
  have h0 := hform 0 0
  have h1 := hform 1 0
  have hc := hconst 1 0
  omega

/-- Concrete integer-superharmonic Apollonian witnesses on `ℤ²` (exact constant Laplacians 2 and 3). -/
def uZ2_lap2 (x y : Int) : Int := (x * (x - 1)) / 2 + (y * (y - 1)) / 2
def uZ2_lap3a (x y : Int) : Int := x * x + (y * (y - 1)) / 2
def uZ2_lap3b (x y : Int) : Int := (x * (x - 1)) / 2 + y * y
def uZ2_lap3c (x y : Int) : Int := x * x + x * y + (y * (y - 1)) / 2

theorem even_mul_pred (n : Int) : 2 * ((n * (n - 1)) / 2) = n * (n - 1) := by
  have hpar : n % 2 = 0 ∨ n % 2 = 1 := by omega
  have h0 : (n * (n - 1)) % 2 = 0 := by
    rcases hpar with h | h <;> (rw [Int.mul_emod, Int.sub_emod, h]; omega)
  omega

/-- **T2c Master Export.** -/
theorem t2c_lps_z2_superharmonic_and_isotropic_obstruction :
    (∀ {Px Py : Nat} {u ψ : Int → Int → Int},
      IsPeriodic2D Px Py ψ →
      (∀ x y, 4 * u x y = 3 * (x * x + y * y) + ψ x y) →
      (∀ x y, lapZ2 u x y ≤ 3) → False) ∧
    (∀ x y : Int,
      lapZ2 uZ2_lap2 x y = 2 ∧
      lapZ2 uZ2_lap3a x y = 3 ∧
      lapZ2 uZ2_lap3b x y = 3 ∧
      lapZ2 uZ2_lap3c x y = 3) := by
  refine ⟨fun h1 h2 h3 => isotropic_z2_max_sea_obstruction h1 h2 h3, ?_⟩
  intro x y
  have hx0 := even_mul_pred x; have hx1 := even_mul_pred (x + 1); have hxm := even_mul_pred (x - 1)
  have hy0 := even_mul_pred y; have hy1 := even_mul_pred (y + 1); have hym := even_mul_pred (y - 1)
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp only [lapZ2, uZ2_lap2, uZ2_lap3a, uZ2_lap3b, uZ2_lap3c]; grind)

/-! ### Part 5: Triangular Lattice `𝔸₂` (`deg = 6`) Even-Laplacian Parity Lemma (`T2d`) -/

/-- The 6-neighbor triangular lattice (`𝔸₂`) discrete Laplacian. -/
def lapA2 (u : Int → Int → Int) (x y : Int) : Int :=
  u (x + 1) y + u (x - 1) y + u x (y + 1) + u x (y - 1) +
  u (x + 1) (y - 1) + u (x - 1) (y + 1) - 6 * u x y

theorem sum_lapA2_periodic {Px Py : Nat} {ψ : Int → Int → Int} (hper : IsPeriodic2D Px Py ψ) :
    sumNat Px (fun i => sumNat Py (fun j => lapA2 ψ (i : Int) (j : Int))) = 0 := by
  have hz2 := sum_lapZ2_periodic hper
  rcases hper with ⟨_, _, hx, hy⟩
  have hd1 := sumNat2_shift_diag_periodic Px Py ψ hx hy
  have hd2 : sumNat Px (fun i => sumNat Py (fun j => ψ ((i : Int) - 1) ((j : Int) + 1))) =
             sumNat Px (fun i => sumNat Py (fun j => ψ (i : Int) (j : Int))) := by
    have hsh := sumNat2_shift_diag_periodic Px Py (fun x y => ψ (x - 1) (y + 1))
      (fun x y => by have h : x + (Px : Int) - 1 = (x - 1) + (Px : Int) := by omega
                     rw [h, hx])
      (fun x y => by have h : y + (Py : Int) + 1 = (y + 1) + (Py : Int) := by omega
                     rw [h, hy])
    have heq : sumNat Px (fun i => sumNat Py (fun j => ψ (((i : Int) + 1) - 1) (((j : Int) - 1) + 1))) =
               sumNat Px (fun i => sumNat Py (fun j => ψ (i : Int) (j : Int))) := by
      apply sumNat_eq_of_eq; intro i _; apply sumNat_eq_of_eq; intro j _
      have hi' : ((i : Int) + 1) - 1 = (i : Int) := by omega
      have hj' : ((j : Int) - 1) + 1 = (j : Int) := by omega
      rw [hi', hj']
    rw [heq] at hsh; exact hsh.symm
  have h2mul : ∀ n (f : Nat → Int), sumNat n (fun i => 2 * f i) = 2 * sumNat n f := by
    intro n f; induction n with | zero => simp [sumNat] | succ k ih => simp only [sumNat, ih]; omega
  have hsplit : sumNat Px (fun i => sumNat Py (fun j => lapA2 ψ (i : Int) (j : Int))) =
      sumNat Px (fun i => sumNat Py (fun j => lapZ2 ψ (i : Int) (j : Int))) +
      sumNat Px (fun i => sumNat Py (fun j => ψ ((i : Int) + 1) ((j : Int) - 1))) +
      sumNat Px (fun i => sumNat Py (fun j => ψ ((i : Int) - 1) ((j : Int) + 1))) -
      2 * sumNat Px (fun i => sumNat Py (fun j => ψ (i : Int) (j : Int))) := by
    have hterm : ∀ i j : Nat,
        lapA2 ψ (i : Int) (j : Int) =
        lapZ2 ψ (i : Int) (j : Int) + ψ ((i : Int) + 1) ((j : Int) - 1) +
        ψ ((i : Int) - 1) ((j : Int) + 1) - 2 * ψ (i : Int) (j : Int) := fun i j => by
      unfold lapA2 lapZ2; omega
    rw [sumNat_eq_of_eq Px _ _ (fun i _ => sumNat_eq_of_eq Py _ _ (fun j _ => hterm i j))]
    have hrow : ∀ i,
        sumNat Py (fun j => lapZ2 ψ (i : Int) (j : Int) + ψ ((i : Int) + 1) ((j : Int) - 1) +
          ψ ((i : Int) - 1) ((j : Int) + 1) - 2 * ψ (i : Int) (j : Int)) =
        sumNat Py (fun j => lapZ2 ψ (i : Int) (j : Int)) +
        sumNat Py (fun j => ψ ((i : Int) + 1) ((j : Int) - 1)) +
        sumNat Py (fun j => ψ ((i : Int) - 1) ((j : Int) + 1)) -
        2 * sumNat Py (fun j => ψ (i : Int) (j : Int)) := by
      intro i; rw [sumNat_sub, sumNat_add, sumNat_add, h2mul]
    rw [sumNat_eq_of_eq Px _ _ (fun i _ => hrow i),
        sumNat_sub, sumNat_add, sumNat_add, h2mul]
  rw [hsplit, hz2, hd1, hd2]; omega

/-- **Discrete Green's First Identity on the Triangular Lattice `𝔸₂` Torus:**
    `∑_Ω ((Δ_x ψ)^2 + (Δ_y ψ)^2 + (Δ_{x-y} ψ)^2) = - ∑_Ω ψ * Δ_{𝔸₂} ψ`! -/
theorem green_identity_A2 {Px Py : Nat} {ψ : Int → Int → Int} (hper : IsPeriodic2D Px Py ψ) :
    sumNat Px (fun i => sumNat Py (fun j =>
      (ψ ((i : Int) + 1) (j : Int) - ψ (i : Int) (j : Int)) *
        (ψ ((i : Int) + 1) (j : Int) - ψ (i : Int) (j : Int)) +
      (ψ (i : Int) ((j : Int) + 1) - ψ (i : Int) (j : Int)) *
        (ψ (i : Int) ((j : Int) + 1) - ψ (i : Int) (j : Int)) +
      (ψ ((i : Int) + 1) ((j : Int) - 1) - ψ (i : Int) (j : Int)) *
        (ψ ((i : Int) + 1) ((j : Int) - 1) - ψ (i : Int) (j : Int)))) =
    - sumNat Px (fun i => sumNat Py (fun j => ψ (i : Int) (j : Int) * lapA2 ψ (i : Int) (j : Int))) := by
  have hz2 := green_identity_Z2 hper
  rcases hper with ⟨_, _, hx, hy⟩
  have hdd : sumNat Px (fun i => sumNat Py (fun j =>
      ψ ((i : Int) + 1) ((j : Int) - 1) * ψ ((i : Int) + 1) ((j : Int) - 1))) =
      sumNat Px (fun i => sumNat Py (fun j => ψ (i : Int) (j : Int) * ψ (i : Int) (j : Int))) :=
    sumNat2_shift_diag_periodic Px Py (fun x y => ψ x y * ψ x y)
      (fun x y => by rw [hx]) (fun x y => by rw [hy])
  have hdm : sumNat Px (fun i => sumNat Py (fun j =>
      ψ (i : Int) (j : Int) * ψ ((i : Int) - 1) ((j : Int) + 1))) =
      sumNat Px (fun i => sumNat Py (fun j =>
      ψ ((i : Int) + 1) ((j : Int) - 1) * ψ (i : Int) (j : Int))) := by
    have hsh := sumNat2_shift_diag_periodic Px Py (fun x y => ψ x y * ψ (x - 1) (y + 1))
      (fun x y => by have h : x + (Px : Int) - 1 = (x - 1) + (Px : Int) := by omega
                     rw [hx, h, hx])
      (fun x y => by have h : y + (Py : Int) + 1 = (y + 1) + (Py : Int) := by omega
                     rw [hy, h, hy])
    have heq : sumNat Px (fun i => sumNat Py (fun j =>
        ψ ((i : Int) + 1) ((j : Int) - 1) * ψ (((i : Int) + 1) - 1) (((j : Int) - 1) + 1))) =
        sumNat Px (fun i => sumNat Py (fun j =>
        ψ ((i : Int) + 1) ((j : Int) - 1) * ψ (i : Int) (j : Int))) := by
      apply sumNat_eq_of_eq; intro i _; apply sumNat_eq_of_eq; intro j _
      have hi' : ((i : Int) + 1) - 1 = (i : Int) := by omega
      have hj' : ((j : Int) - 1) + 1 = (j : Int) := by omega
      rw [hi', hj']
    rw [← hsh, heq]
  have h2mul : ∀ n (f : Nat → Int), sumNat n (fun i => 2 * f i) = 2 * sumNat n f := by
    intro n f; induction n with | zero => simp [sumNat] | succ k ih => simp only [sumNat, ih]; omega
  have hdiag_green :
      sumNat Px (fun i => sumNat Py (fun j =>
        (ψ ((i : Int) + 1) ((j : Int) - 1) - ψ (i : Int) (j : Int)) *
          (ψ ((i : Int) + 1) ((j : Int) - 1) - ψ (i : Int) (j : Int)))) =
      - sumNat Px (fun i => sumNat Py (fun j =>
        ψ (i : Int) (j : Int) * (ψ ((i : Int) + 1) ((j : Int) - 1) +
          ψ ((i : Int) - 1) ((j : Int) + 1) - 2 * ψ (i : Int) (j : Int)))) := by
    have hL :
        sumNat Px (fun i => sumNat Py (fun j =>
          (ψ ((i : Int) + 1) ((j : Int) - 1) - ψ (i : Int) (j : Int)) *
            (ψ ((i : Int) + 1) ((j : Int) - 1) - ψ (i : Int) (j : Int)))) =
        2 * sumNat Px (fun i => sumNat Py (fun j => ψ (i : Int) (j : Int) * ψ (i : Int) (j : Int))) -
        2 * sumNat Px (fun i => sumNat Py (fun j => ψ ((i : Int) + 1) ((j : Int) - 1) * ψ (i : Int) (j : Int))) := by
      have ht : ∀ i j : Nat,
          (ψ ((i : Int) + 1) ((j : Int) - 1) - ψ (i : Int) (j : Int)) *
            (ψ ((i : Int) + 1) ((j : Int) - 1) - ψ (i : Int) (j : Int)) =
          ψ ((i : Int) + 1) ((j : Int) - 1) * ψ ((i : Int) + 1) ((j : Int) - 1) +
          ψ (i : Int) (j : Int) * ψ (i : Int) (j : Int) -
          2 * (ψ ((i : Int) + 1) ((j : Int) - 1) * ψ (i : Int) (j : Int)) := fun i j => by grind
      rw [sumNat_eq_of_eq Px _ _ (fun i _ => sumNat_eq_of_eq Py _ _ (fun j _ => ht i j))]
      have hr : ∀ i,
          sumNat Py (fun j =>
            ψ ((i : Int) + 1) ((j : Int) - 1) * ψ ((i : Int) + 1) ((j : Int) - 1) +
            ψ (i : Int) (j : Int) * ψ (i : Int) (j : Int) -
            2 * (ψ ((i : Int) + 1) ((j : Int) - 1) * ψ (i : Int) (j : Int))) =
          sumNat Py (fun j => ψ ((i : Int) + 1) ((j : Int) - 1) * ψ ((i : Int) + 1) ((j : Int) - 1)) +
          sumNat Py (fun j => ψ (i : Int) (j : Int) * ψ (i : Int) (j : Int)) -
          2 * sumNat Py (fun j => ψ ((i : Int) + 1) ((j : Int) - 1) * ψ (i : Int) (j : Int)) := by
        intro i; rw [sumNat_sub, sumNat_add, h2mul]
      rw [sumNat_eq_of_eq Px _ _ (fun i _ => hr i), sumNat_sub, sumNat_add, h2mul, hdd]; omega
    have hR :
        sumNat Px (fun i => sumNat Py (fun j =>
          ψ (i : Int) (j : Int) * (ψ ((i : Int) + 1) ((j : Int) - 1) +
            ψ ((i : Int) - 1) ((j : Int) + 1) - 2 * ψ (i : Int) (j : Int)))) =
        2 * sumNat Px (fun i => sumNat Py (fun j => ψ ((i : Int) + 1) ((j : Int) - 1) * ψ (i : Int) (j : Int))) -
        2 * sumNat Px (fun i => sumNat Py (fun j => ψ (i : Int) (j : Int) * ψ (i : Int) (j : Int))) := by
      have ht : ∀ i j : Nat,
          ψ (i : Int) (j : Int) * (ψ ((i : Int) + 1) ((j : Int) - 1) +
            ψ ((i : Int) - 1) ((j : Int) + 1) - 2 * ψ (i : Int) (j : Int)) =
          ψ ((i : Int) + 1) ((j : Int) - 1) * ψ (i : Int) (j : Int) +
          ψ (i : Int) (j : Int) * ψ ((i : Int) - 1) ((j : Int) + 1) -
          2 * (ψ (i : Int) (j : Int) * ψ (i : Int) (j : Int)) := fun i j => by grind
      rw [sumNat_eq_of_eq Px _ _ (fun i _ => sumNat_eq_of_eq Py _ _ (fun j _ => ht i j))]
      have hr : ∀ i,
          sumNat Py (fun j =>
            ψ ((i : Int) + 1) ((j : Int) - 1) * ψ (i : Int) (j : Int) +
            ψ (i : Int) (j : Int) * ψ ((i : Int) - 1) ((j : Int) + 1) -
            2 * (ψ (i : Int) (j : Int) * ψ (i : Int) (j : Int))) =
          sumNat Py (fun j => ψ ((i : Int) + 1) ((j : Int) - 1) * ψ (i : Int) (j : Int)) +
          sumNat Py (fun j => ψ (i : Int) (j : Int) * ψ ((i : Int) - 1) ((j : Int) + 1)) -
          2 * sumNat Py (fun j => ψ (i : Int) (j : Int) * ψ (i : Int) (j : Int)) := by
        intro i; rw [sumNat_sub, sumNat_add, h2mul]
      rw [sumNat_eq_of_eq Px _ _ (fun i _ => hr i), sumNat_sub, sumNat_add, h2mul, hdm]; omega
    rw [hL, hR]; omega
  -- Sum Z2 Green's identity and the diagonal Green's identity!
  have hsumL :
      sumNat Px (fun i => sumNat Py (fun j =>
        (ψ ((i : Int) + 1) (j : Int) - ψ (i : Int) (j : Int)) *
          (ψ ((i : Int) + 1) (j : Int) - ψ (i : Int) (j : Int)) +
        (ψ (i : Int) ((j : Int) + 1) - ψ (i : Int) (j : Int)) *
          (ψ (i : Int) ((j : Int) + 1) - ψ (i : Int) (j : Int)) +
        (ψ ((i : Int) + 1) ((j : Int) - 1) - ψ (i : Int) (j : Int)) *
          (ψ ((i : Int) + 1) ((j : Int) - 1) - ψ (i : Int) (j : Int)))) =
      sumNat Px (fun i => sumNat Py (fun j =>
        (ψ ((i : Int) + 1) (j : Int) - ψ (i : Int) (j : Int)) *
          (ψ ((i : Int) + 1) (j : Int) - ψ (i : Int) (j : Int)) +
        (ψ (i : Int) ((j : Int) + 1) - ψ (i : Int) (j : Int)) *
          (ψ (i : Int) ((j : Int) + 1) - ψ (i : Int) (j : Int)))) +
      sumNat Px (fun i => sumNat Py (fun j =>
        (ψ ((i : Int) + 1) ((j : Int) - 1) - ψ (i : Int) (j : Int)) *
          (ψ ((i : Int) + 1) ((j : Int) - 1) - ψ (i : Int) (j : Int)))) := by
    have hr : ∀ i,
        sumNat Py (fun j =>
          ((ψ ((i : Int) + 1) (j : Int) - ψ (i : Int) (j : Int)) *
            (ψ ((i : Int) + 1) (j : Int) - ψ (i : Int) (j : Int)) +
          (ψ (i : Int) ((j : Int) + 1) - ψ (i : Int) (j : Int)) *
            (ψ (i : Int) ((j : Int) + 1) - ψ (i : Int) (j : Int))) +
          (ψ ((i : Int) + 1) ((j : Int) - 1) - ψ (i : Int) (j : Int)) *
            (ψ ((i : Int) + 1) ((j : Int) - 1) - ψ (i : Int) (j : Int))) =
        sumNat Py (fun j =>
          (ψ ((i : Int) + 1) (j : Int) - ψ (i : Int) (j : Int)) *
            (ψ ((i : Int) + 1) (j : Int) - ψ (i : Int) (j : Int)) +
          (ψ (i : Int) ((j : Int) + 1) - ψ (i : Int) (j : Int)) *
            (ψ (i : Int) ((j : Int) + 1) - ψ (i : Int) (j : Int))) +
        sumNat Py (fun j =>
          (ψ ((i : Int) + 1) ((j : Int) - 1) - ψ (i : Int) (j : Int)) *
            (ψ ((i : Int) + 1) ((j : Int) - 1) - ψ (i : Int) (j : Int))) := fun i => sumNat_add Py _ _
    rw [sumNat_eq_of_eq Px _ _ (fun i _ => hr i), sumNat_add]
  have hsumR :
      sumNat Px (fun i => sumNat Py (fun j => ψ (i : Int) (j : Int) * lapA2 ψ (i : Int) (j : Int))) =
      sumNat Px (fun i => sumNat Py (fun j => ψ (i : Int) (j : Int) * lapZ2 ψ (i : Int) (j : Int))) +
      sumNat Px (fun i => sumNat Py (fun j =>
        ψ (i : Int) (j : Int) * (ψ ((i : Int) + 1) ((j : Int) - 1) +
          ψ ((i : Int) - 1) ((j : Int) + 1) - 2 * ψ (i : Int) (j : Int)))) := by
    have ht : ∀ i j : Nat,
        ψ (i : Int) (j : Int) * lapA2 ψ (i : Int) (j : Int) =
        ψ (i : Int) (j : Int) * lapZ2 ψ (i : Int) (j : Int) +
        ψ (i : Int) (j : Int) * (ψ ((i : Int) + 1) ((j : Int) - 1) +
          ψ ((i : Int) - 1) ((j : Int) + 1) - 2 * ψ (i : Int) (j : Int)) := fun i j => by
      unfold lapA2 lapZ2; grind
    rw [sumNat_eq_of_eq Px _ _ (fun i _ => sumNat_eq_of_eq Py _ _ (fun j _ => ht i j))]
    rw [sumNat_eq_of_eq Px _ _ (fun i _ => sumNat_add Py _ _), sumNat_add]
  rw [hsumL, hz2, hdiag_green, hsumR]; omega

/-- **Periodic Superharmonic Rigidity on `𝔸₂`:**
    Any periodic `ψ` with `Δ_{𝔸₂} ψ ≤ 0` everywhere is IDENTICALLY CONSTANT! -/
theorem periodic_superharmonic_A2_const {Px Py : Nat} {ψ : Int → Int → Int}
    (hper : IsPeriodic2D Px Py ψ) (hsup : ∀ x y : Int, lapA2 ψ x y ≤ 0) :
    ∀ x y : Int, ψ x y = ψ 0 0 := by
  have hsum0 := sum_lapA2_periodic hper
  have hrow0 : ∀ i, i < Px → sumNat Py (fun j => lapA2 ψ (i : Int) (j : Int)) = 0 :=
    sumNat_eq_zero_of_nonpos Px _ (fun i _ => sumNat_nonpos Py _ (fun j _ => hsup _ _)) hsum0
  have hcell0 : ∀ i j, i < Px → j < Py → lapA2 ψ (i : Int) (j : Int) = 0 := fun i j hi hj =>
    sumNat_eq_zero_of_nonpos Py _ (fun j' _ => hsup _ _) (hrow0 i hi) j hj
  have hE0 : sumNat Px (fun i => sumNat Py (fun j =>
      (ψ ((i : Int) + 1) (j : Int) - ψ (i : Int) (j : Int)) *
        (ψ ((i : Int) + 1) (j : Int) - ψ (i : Int) (j : Int)) +
      (ψ (i : Int) ((j : Int) + 1) - ψ (i : Int) (j : Int)) *
        (ψ (i : Int) ((j : Int) + 1) - ψ (i : Int) (j : Int)) +
      (ψ ((i : Int) + 1) ((j : Int) - 1) - ψ (i : Int) (j : Int)) *
        (ψ ((i : Int) + 1) ((j : Int) - 1) - ψ (i : Int) (j : Int)))) = 0 := by
    rw [green_identity_A2 hper]
    have hzero : sumNat Px (fun i => sumNat Py (fun j => ψ (i : Int) (j : Int) * lapA2 ψ (i : Int) (j : Int))) = 0 := by
      have h1 : sumNat Px (fun i => sumNat Py (fun j => ψ (i : Int) (j : Int) * lapA2 ψ (i : Int) (j : Int))) =
                sumNat Px (fun _ => 0) := by
        apply sumNat_eq_of_eq; intro i hi
        have h2 : sumNat Py (fun j => ψ (i : Int) (j : Int) * lapA2 ψ (i : Int) (j : Int)) = sumNat Py (fun _ => 0) := by
          apply sumNat_eq_of_eq; intro j hj; rw [hcell0 i j hi hj]; simp
        rw [h2, sumNat_const]; simp
      rw [h1, sumNat_const]; simp
    rw [hzero]; simp
  have hErow : ∀ i, i < Px → sumNat Py (fun j =>
      (ψ ((i : Int) + 1) (j : Int) - ψ (i : Int) (j : Int)) *
        (ψ ((i : Int) + 1) (j : Int) - ψ (i : Int) (j : Int)) +
      (ψ (i : Int) ((j : Int) + 1) - ψ (i : Int) (j : Int)) *
        (ψ (i : Int) ((j : Int) + 1) - ψ (i : Int) (j : Int)) +
      (ψ ((i : Int) + 1) ((j : Int) - 1) - ψ (i : Int) (j : Int)) *
        (ψ ((i : Int) + 1) ((j : Int) - 1) - ψ (i : Int) (j : Int))) = 0 :=
    sumNat_eq_zero_of_nonneg Px _ (fun i _ => sumNat_nonneg Py _ (fun j _ => by
      have h1 := sq_nonneg (ψ ((i : Int) + 1) (j : Int) - ψ (i : Int) (j : Int))
      have h2 := sq_nonneg (ψ (i : Int) ((j : Int) + 1) - ψ (i : Int) (j : Int))
      have h3 := sq_nonneg (ψ ((i : Int) + 1) ((j : Int) - 1) - ψ (i : Int) (j : Int))
      omega)) hE0
  have hstep : ∀ i j, i < Px → j < Py →
      ψ ((i : Int) + 1) (j : Int) = ψ (i : Int) (j : Int) ∧
      ψ (i : Int) ((j : Int) + 1) = ψ (i : Int) (j : Int) := by
    intro i j hi hj
    have hz := sumNat_eq_zero_of_nonneg Py _ (fun j' _ => by
      have h1 := sq_nonneg (ψ ((i : Int) + 1) (j' : Int) - ψ (i : Int) (j' : Int))
      have h2 := sq_nonneg (ψ (i : Int) ((j' : Int) + 1) - ψ (i : Int) (j' : Int))
      have h3 := sq_nonneg (ψ ((i : Int) + 1) ((j' : Int) - 1) - ψ (i : Int) (j' : Int))
      omega) (hErow i hi) j hj
    have h1 := sq_nonneg (ψ ((i : Int) + 1) (j : Int) - ψ (i : Int) (j : Int))
    have h2 := sq_nonneg (ψ (i : Int) ((j : Int) + 1) - ψ (i : Int) (j : Int))
    have h3 := sq_nonneg (ψ ((i : Int) + 1) ((j : Int) - 1) - ψ (i : Int) (j : Int))
    have hs1 : (ψ ((i : Int) + 1) (j : Int) - ψ (i : Int) (j : Int)) *
               (ψ ((i : Int) + 1) (j : Int) - ψ (i : Int) (j : Int)) = 0 := by omega
    have hs2 : (ψ (i : Int) ((j : Int) + 1) - ψ (i : Int) (j : Int)) *
               (ψ (i : Int) ((j : Int) + 1) - ψ (i : Int) (j : Int)) = 0 := by omega
    have hd1 := (Int.mul_eq_zero.mp hs1).elim id id
    have hd2 := (Int.mul_eq_zero.mp hs2).elim id id
    omega
  have hbox : ∀ i j, i < Px → j < Py → ψ (i : Int) (j : Int) = ψ 0 0 := by
    intro i j hi hj
    have hxwalk : ∀ a, a ≤ i → ψ (a : Int) (j : Int) = ψ 0 (j : Int) := by
      intro a; induction a with
      | zero => intro _; rfl
      | succ k ih =>
        intro hk
        have hst := (hstep k j (by omega) hj).1
        have hcast : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
        rw [hcast, hst, ih (by omega)]
    have hywalk : ∀ b, b ≤ j → ψ 0 (b : Int) = ψ 0 0 := by
      intro b; induction b with
      | zero => intro _; rfl
      | succ k ih =>
        intro hk
        have hst := (hstep 0 k hper.1 (by omega)).2
        simp only [Int.natCast_zero] at hst
        have hcast : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
        rw [hcast, hst, ih (by omega)]
    rw [hxwalk i (Nat.le_refl i), hywalk j (Nat.le_refl j)]
  intro x y
  rw [periodic_mod_eq hper x y]
  rcases hper with ⟨hPx, hPy, _, _⟩
  have hxm0 : 0 ≤ x % (Px : Int) := Int.emod_nonneg x (by omega)
  have hxm1 : x % (Px : Int) < (Px : Int) := Int.emod_lt_of_pos x (by omega)
  have hym0 : 0 ≤ y % (Py : Int) := Int.emod_nonneg y (by omega)
  have hym1 : y % (Py : Int) < (Py : Int) := Int.emod_lt_of_pos y (by omega)
  have hcastx : ((x % (Px : Int)).toNat : Int) = x % (Px : Int) := Int.toNat_of_nonneg hxm0
  have hcasty : ((y % (Py : Int)).toNat : Int) = y % (Py : Int) := Int.toNat_of_nonneg hym0
  rw [← hcastx, ← hcasty]
  exact hbox _ _ (by omega) (by omega)

/-- **`𝔸₂` Even-Laplacian Parity Lemma (no prior statement found in literature search):**
    For EVERY denominator `M ≥ 1`, EVERY quadratic form `Q(x, y) = A x^2 + B x y + C y^2 + D x + E y`,
    EVERY periodic remainder `ψ`, and EVERY integer `K`:
    if `M * u(x, y) = Q(x, y) + ψ(x, y)`, `M * K = 4*A - 2*B + 4*C`, and `Δ_{𝔸₂} u(x, y) ≤ K`
    everywhere, then **`K % 2 = 0`**. (This is a pure discrete-PDE parity obstruction for
    quadratic-plus-periodic integer functions; no link to finite-grid sandpile heights is proved.) -/
theorem a2_even_laplacian_rigidity {M : Int} (hM : 1 ≤ M)
    {A B C D E K : Int} {Px Py : Nat} {u ψ : Int → Int → Int}
    (hper : IsPeriodic2D Px Py ψ)
    (hform : ∀ x y : Int, M * u x y = A * x * x + B * x * y + C * y * y + D * x + E * y + ψ x y)
    (hmean : M * K = 4 * A - 2 * B + 4 * C)
    (hsup : ∀ x y : Int, lapA2 u x y ≤ K) :
    K % 2 = 0 := by
  have hlap_psi : ∀ x y : Int, lapA2 ψ x y ≤ 0 := by
    intro x y
    have hM_lap : M * lapA2 u x y = 4 * A - 2 * B + 4 * C + lapA2 ψ x y := by
      unfold lapA2
      have h00 := hform x y
      have h10 := hform (x + 1) y
      have hm0 := hform (x - 1) y
      have h01 := hform x (y + 1)
      have h0m := hform x (y - 1)
      have h1m := hform (x + 1) (y - 1)
      have hm1 := hform (x - 1) (y + 1)
      grind
    have hle : M * lapA2 u x y ≤ M * K := Int.mul_le_mul_of_nonneg_left (hsup x y) (by omega)
    omega
  have hconst := periodic_superharmonic_A2_const hper hlap_psi
  -- Discrete second differences of the integer function u!
  let dxx : Int := u 2 0 - 2 * u 1 0 + u 0 0
  let dyy : Int := u 0 2 - 2 * u 0 1 + u 0 0
  let dxy : Int := u 1 1 - u 1 0 - u 0 1 + u 0 0
  have h2A : M * dxx = 2 * A := by
    have h00 := hform 0 0; have h10 := hform 1 0; have h20 := hform 2 0
    have c1 := hconst 1 0; have c2 := hconst 2 0
    dsimp [dxx]; grind
  have h2C : M * dyy = 2 * C := by
    have h00 := hform 0 0; have h01 := hform 0 1; have h02 := hform 0 2
    have c1 := hconst 0 1; have c2 := hconst 0 2
    dsimp [dyy]; grind
  have hB : M * dxy = B := by
    have h00 := hform 0 0; have h10 := hform 1 0; have h01 := hform 0 1; have h11 := hform 1 1
    have c1 := hconst 1 0; have c2 := hconst 0 1; have c3 := hconst 1 1
    dsimp [dxy]; grind
  have hMK : M * K = M * (2 * (dxx - dxy + dyy)) := by grind
  have hK : K = 2 * (dxx - dxy + dyy) := Int.eq_of_mul_eq_mul_left (by omega) hMK
  omega

/-- Sharp `𝔸₂` even-Laplacian witnesses (`Δ_{𝔸₂} ≡ 4` and `Δ_{𝔸₂} ≡ 2`). -/
def uA2_lap4 (x y : Int) : Int := (x * (x - 1)) / 2 + (y * (y - 1)) / 2
def uA2_lap2 (x _y : Int) : Int := (x * (x - 1)) / 2

/-- **T2d Master Export:**
    1. `𝔸₂` Even-Laplacian parity lemma (`K % 2 = 0` under `1 ≤ M`, `IsPeriodic2D Px Py ψ`,
       `M * u = Q + ψ`, `M * K = 4*A - 2*B + 4*C`, and `Δ_{𝔸₂} u ≤ K`).
    2. Immediate corollary: no such quadratic-plus-periodic integer function has `K = 5`
       (no connection to finite-grid sandpile plateau heights is formalized or proved).
    3. Sharpness witnesses: `Δ_{𝔸₂} uA2_lap4 ≡ 4` and `Δ_{𝔸₂} uA2_lap2 ≡ 2` everywhere on `ℤ²`. -/
theorem t2d_triangular_a2_even_laplacian_rigidity_and_obstruction :
    (∀ {M A B C D E K : Int} {Px Py : Nat} {u ψ : Int → Int → Int},
      1 ≤ M → IsPeriodic2D Px Py ψ →
      (∀ x y, M * u x y = A * x * x + B * x * y + C * y * y + D * x + E * y + ψ x y) →
      M * K = 4 * A - 2 * B + 4 * C →
      (∀ x y, lapA2 u x y ≤ K) → K % 2 = 0) ∧
    (∀ {M A B C D E : Int} {Px Py : Nat} {u ψ : Int → Int → Int},
      1 ≤ M → IsPeriodic2D Px Py ψ →
      (∀ x y, M * u x y = A * x * x + B * x * y + C * y * y + D * x + E * y + ψ x y) →
      M * 5 = 4 * A - 2 * B + 4 * C →
      (∀ x y, lapA2 u x y ≤ 5) → False) ∧
    (∀ x y : Int, lapA2 uA2_lap4 x y = 4 ∧ lapA2 uA2_lap2 x y = 2) := by
  refine ⟨fun hM hper hform hmean hsup => a2_even_laplacian_rigidity hM hper hform hmean hsup,
          fun hM hper hform hmean hsup => by
            have := a2_even_laplacian_rigidity hM hper hform hmean hsup; omega, ?_⟩
  intro x y
  have hx0 := even_mul_pred x; have hx1 := even_mul_pred (x + 1); have hxm := even_mul_pred (x - 1)
  have hy0 := even_mul_pred y; have hy1 := even_mul_pred (y + 1); have hym := even_mul_pred (y - 1)
  constructor <;> (simp only [lapA2, uA2_lap4, uA2_lap2]; grind)

/-! ### Part 6: Lattice-Polygon Edge-Normal Balancing & `2×2` Determinant Identity (`T2e`)
    (Elementary algebraic identities motivated by Kalinin–Shkolnikov; the Kalinin–Shkolnikov
    tropical-curve sandpile theorem itself is NOT formalized.) -/

abbrev Vec2 := Int × Int

def vadd (a b : Vec2) : Vec2 := (a.1 + b.1, a.2 + b.2)
def vsub (a b : Vec2) : Vec2 := (a.1 - b.1, a.2 - b.2)
def rot90 (v : Vec2) : Vec2 := (-v.2, v.1)
def det2v (a b : Vec2) : Int := a.1 * b.2 - a.2 * b.1

def sumVec : List Vec2 → Vec2
  | [] => (0, 0)
  | v :: vs => vadd v (sumVec vs)

/-- Outgoing edge normals around an open polygonal chain from `first` through `vs` back to `last`. -/
def chainNormals : Vec2 → List Vec2 → List Vec2
  | _, [] => []
  | prev, v :: vs => rot90 (vsub v prev) :: chainNormals v vs

def cycleNormals : List Vec2 → List Vec2
  | [] => []
  | v0 :: vs => chainNormals v0 (vs ++ [v0])

theorem sumVec_chainNormals (a : Vec2) (vs : List Vec2) (b : Vec2) :
    sumVec (chainNormals a (vs ++ [b])) = rot90 (vsub b a) := by
  induction vs generalizing a with
  | nil =>
    simp [chainNormals, sumVec, vadd, rot90, vsub]
  | cons v rest ih =>
    simp only [List.cons_append, chainNormals, sumVec, ih v]
    cases a; cases v; cases b
    simp only [vadd, rot90, vsub]
    ext <;> omega

/-- **Lattice-Polygon Edge-Normal Closure Identity:**
    For every closed list of lattice points `vs`, the sum of the `90°`-rotated edge vectors
    telescopes identically to `(0, 0)`. -/
theorem tropical_cycle_balancing (vs : List Vec2) :
    sumVec (cycleNormals vs) = (0, 0) := by
  cases vs with
  | nil => rfl
  | cons v0 rest =>
    simp only [cycleNormals, sumVec_chainNormals]
    cases v0
    simp [vsub, rot90]

/-- **Exact Trivalent Unimodularity & 2/3-Soliton Tropical Scattering Conservation:**
    1. For ANY balanced triple `v1 + v2 + v3 = (0, 0)`, all three pairwise determinants agree:
       `det(v1, v2) = det(v2, v3) = det(v3, v1)` (area conservation at every tropical vertex!).
    2. Standard smooth tropical line vertex `(1, 0), (0, 1), (-1, -1)` is balanced & unimodular (`det = 1`).
    3. Exact 3-soliton scattering resolution of 4-valent boundary rays `[(1, 0), (0, 1), (-1, 1), (0, -2)]`
       into two smooth unimodular trivalent vertices bridged by the internal tropical edge `(1, 1)`
       / `(-1, -1)`! -/
theorem balanced_triple_det_eq {v1 v2 v3 : Vec2} (hbal : vadd (vadd v1 v2) v3 = (0, 0)) :
    det2v v1 v2 = det2v v2 v3 ∧ det2v v2 v3 = det2v v3 v1 := by
  cases v1; cases v2; cases v3
  simp only [vadd, Prod.mk.injEq] at hbal
  simp only [det2v]
  constructor <;> grind

/-- **T2e Master Export.** -/
theorem t2e_kalinin_shkolnikov_tropical_balancing_and_solitons :
    (∀ vs : List Vec2, sumVec (cycleNormals vs) = (0, 0)) ∧
    (∀ v1 v2 v3 : Vec2, vadd (vadd v1 v2) v3 = (0, 0) →
      det2v v1 v2 = det2v v2 v3 ∧ det2v v2 v3 = det2v v3 v1) ∧
    (vadd (vadd (1, 0) (0, 1)) (-1, -1) = (0, 0) ∧ det2v (1, 0) (0, 1) = 1) ∧
    (sumVec [(1, 0), (0, 1), (-1, 1), (0, -2)] = (0, 0) ∧
     vadd (vadd (1, 0) (0, 1)) (-1, -1) = (0, 0) ∧
     vadd (vadd (-1, 1) (0, -2)) (1, 1) = (0, 0) ∧
     det2v (-1, 1) (0, -2) = 2) :=
  ⟨tropical_cycle_balancing,
   fun _ _ _ h => balanced_triple_det_eq h,
   ⟨by decide, by decide⟩,
   ⟨by decide, by decide, by decide, by decide⟩⟩

/-! ### Part 7: Exact Triangular Lattice `𝔸₂` Matrix-Tree Orders (`1,092`, `5,393,920`) & Dhar Identities (`T2f`) -/

/-- Concrete `k × k` open-boundary triangular lattice `𝔸₂` sandpile graph (`deg = 6` everywhere),
    with 6 neighbors `(r±1,c)`, `(r,c±1)`, `(r-1,c+1)`, and `(r+1,c-1)`. -/
def a2GridGraph (k : Nat) : SandpileGraph (k * k) where
  adj i j :=
    let r1 := i.val / k; let c1 := i.val % k
    let r2 := j.val / k; let c2 := j.val % k
    let dr := if r1 ≥ r2 then r1 - r2 else r2 - r1
    let dc := if c1 ≥ c2 then c1 - c2 else c2 - c1
    if dr + dc == 1 then 1
    else if (r1 + 1 == r2 && c2 + 1 == c1) || (r2 + 1 == r1 && c1 + 1 == c2) then 1
    else 0
  deg _ := 6
  adj_diag i := by
    dsimp only
    have h1 : ¬ (i.val / k + 1 == i.val / k) := by
      simp only [beq_iff_eq]; omega
    have h2 : ¬ (i.val % k + 1 == i.val % k) := by
      simp only [beq_iff_eq]; omega
    simp [h1, h2]
  adj_symm i j := by
    dsimp only
    have h1 : (if i.val / k ≥ j.val / k then i.val / k - j.val / k else j.val / k - i.val / k) =
              (if j.val / k ≥ i.val / k then j.val / k - i.val / k else i.val / k - j.val / k) := by
      split <;> split <;> omega
    have h2 : (if i.val % k ≥ j.val % k then i.val % k - j.val % k else j.val % k - i.val % k) =
              (if j.val % k ≥ i.val % k then j.val % k - i.val % k else i.val % k - j.val % k) := by
      split <;> split <;> omega
    rw [h1, h2, Bool.or_comm]

/-- Exact `k × k` triangular lattice `𝔸₂` open-boundary Laplacian matrix `L_{ij} = 6 δ_{ij} - adj(i, j)`. -/
def a2GridLap (k : Nat) (i j : Fin (k * k)) : Int :=
  if i = j then 6 else - ((a2GridGraph k).adj i j : Int)

/-- Klein four-group (`σ(r,c)=(c,r)`, `τ(r,c)=(2-r,2-c)`) exact integer similarity basis `Q_{𝔸₂}`
    splitting `L_{𝔸₂, 3×3}` into `diag(7, B_{2a}, B_{2b}, B_4)` with
    `det(B_{2a}) = 28`, `det(B_{2b}) = 40`, `det(B_4) = 688`,
    yielding `det(L_{𝔸₂, 3×3}) = 7 * 28 * 40 * 688 = 5,393,920`! -/
def qA2Mat (i j : Fin 9) : Int :=
  match j.val, i.val with
  | 0, 1 => 1  | 0, 3 => -1 | 0, 5 => -1 | 0, 7 => 1
  | 1, 0 => 1  | 1, 8 => -1
  | 2, 1 => 1  | 2, 3 => 1  | 2, 5 => -1 | 2, 7 => -1
  | 3, 2 => 1  | 3, 6 => -1
  | 4, 1 => 1  | 4, 3 => -1 | 4, 5 => 1  | 4, 7 => -1
  | 5, 0 => 1  | 5, 8 => 1
  | 6, 2 => 1  | 6, 6 => 1
  | 7, 1 => 1  | 7, 3 => 1  | 7, 5 => 1  | 7, 7 => 1
  | 8, 4 => 1
  | _, _ => 0

def qA2Inv4 (i j : Fin 9) : Int :=
  match i.val, j.val with
  | 0, 1 => 1  | 0, 3 => -1 | 0, 5 => -1 | 0, 7 => 1
  | 1, 0 => 2  | 1, 8 => -2
  | 2, 1 => 1  | 2, 3 => 1  | 2, 5 => -1 | 2, 7 => -1
  | 3, 2 => 2  | 3, 6 => -2
  | 4, 1 => 1  | 4, 3 => -1 | 4, 5 => 1  | 4, 7 => -1
  | 5, 0 => 2  | 5, 8 => 2
  | 6, 2 => 2  | 6, 6 => 2
  | 7, 1 => 1  | 7, 3 => 1  | 7, 5 => 1  | 7, 7 => 1
  | 8, 4 => 4
  | _, _ => 0

def b2aA2 (r c : Fin 2) : Int :=
  match r.val, c.val with
  | 0, 0 => 6  | 0, 1 => -2
  | 1, 0 => -1 | 1, 1 => 5
  | _, _ => 0

def b2bA2 (r c : Fin 2) : Int :=
  match r.val, c.val with
  | 0, 0 => 6  | 0, 1 => -2
  | 1, 0 => -1 | 1, 1 => 7
  | _, _ => 0

def b4A2 (r c : Fin 4) : Int :=
  match r.val, c.val with
  | 0, 0 => 6  | 0, 1 => 0  | 0, 2 => -2 | 0, 3 => 0
  | 1, 0 => 0  | 1, 1 => 6  | 1, 2 => -2 | 1, 3 => -1
  | 2, 0 => -1 | 2, 1 => -1 | 2, 2 => 5  | 2, 3 => -1
  | 3, 0 => 0  | 3, 1 => -2 | 3, 2 => -4 | 3, 3 => 6
  | _, _ => 0

def blockDiagA2 (i j : Fin 9) : Int :=
  if i.val = 0 ∧ j.val = 0 then 7
  else if h1 : 1 ≤ i.val ∧ i.val ≤ 2 ∧ 1 ≤ j.val ∧ j.val ≤ 2 then
    b2aA2 ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩
  else if h2 : 3 ≤ i.val ∧ i.val ≤ 4 ∧ 3 ≤ j.val ∧ j.val ≤ 4 then
    b2bA2 ⟨i.val - 3, by omega⟩ ⟨j.val - 3, by omega⟩
  else if h3 : 5 ≤ i.val ∧ 5 ≤ j.val then
    b4A2 ⟨i.val - 5, by omega⟩ ⟨j.val - 5, by omega⟩
  else 0

/-- Exact `𝔸₂` `2×2` and `3×3` Dhar critical identity configurations and legal toppling traces. -/
def idA2_2x2 : Config 4 := fun i =>
  match i.val with
  | 0 => 4 | 1 => 3 | 2 => 3 | 3 => 4 | _ => 0

def s2MaxA2_2x2 : Config 4 := fun i =>
  match i.val with
  | 0 => 2 | 1 => 4 | 2 => 4 | 3 => 2 | _ => 0

def idA2_3x3 : Config 9 := fun i =>
  match i.val with
  | 0 => 4 | 1 => 2 | 2 => 3
  | 3 => 2 | 4 => 0 | 5 => 2
  | 6 => 3 | 7 => 2 | 8 => 4
  | _ => 0

def s2MaxA2_3x3 : Config 9 := fun i =>
  match i.val with
  | 0 => 4 | 1 => 4 | 2 => 2
  | 3 => 4 | 4 => 4 | 5 => 4
  | 6 => 2 | 7 => 4 | 8 => 4
  | _ => 0

def traceIdA2_2x2 : List (Fin 4) := [0, 1, 2, 3]
def trace2MaxA2_2x2 : List (Fin 4) := [0, 1, 2, 0, 1, 2, 3, 3]
def traceDharA2_2x2 : List (Fin 4) := [0, 1, 2, 3]

def traceIdA2_3x3 : List (Fin 9) := [0, 2, 1, 3, 6, 8, 5, 7, 4]
def trace2MaxA2_3x3 : List (Fin 9) :=
  [0, 1, 2, 1, 0, 2, 3, 3, 4, 4, 1, 5, 4, 3, 5, 2, 6, 6, 7, 4, 5, 6, 7, 7, 8, 8]
def traceDharA2_3x3 : List (Fin 9) :=
  [0, 1, 2, 3, 4, 5, 6, 7, 4, 2, 1, 3, 6, 8, 5, 7, 4]

def opsA2GridLap3 : List (RowOp 9) :=
  [.scale 1 6, .addMul 1 0 1, .scale 3 6, .addMul 3 0 1, .scale 2 35, .addMul 2 1 1,
   .scale 3 5, .addMul 3 1 1, .divRow 3 6, .cancel 6, .scale 4 35, .addMul 4 1 1,
   .scale 3 204, .addMul 3 2 1, .divRow 3 5, .cancel 5, .scale 4 204, .addMul 4 2 41,
   .divRow 4 35, .cancel 35, .scale 5 204, .addMul 5 2 1, .scale 4 1141, .addMul 4 3 253,
   .divRow 4 204, .cancel 204, .scale 5 163, .addMul 5 3 1, .divRow 5 204, .cancel 204,
   .scale 6 1141, .addMul 6 3 1, .scale 5 6068, .addMul 5 4 197, .divRow 5 163, .cancel 163,
   .scale 6 74, .addMul 6 4 17, .divRow 6 1141, .cancel 1141, .scale 7 6068, .addMul 7 4 1,
   .scale 6 11233, .addMul 6 5 7, .divRow 6 148, .cancel 148, .scale 7 33699, .addMul 7 5 7447,
   .divRow 7 84952, .cancel 84952, .scale 8 33699, .addMul 8 5 1, .divRow 8 14, .cancel 14,
   .scale 7 31037, .addMul 7 6 3111, .divRow 7 449320, .cancel 224660, .scale 8 757, .addMul 8 6 3,
   .divRow 8 89864, .cancel 11233, .scale 8 871, .addMul 8 7 25, .divRow 8 97653, .cancel 2271]

theorem detMat_a2GridLap3 : detMat 9 (a2GridLap 3) = 5393920 :=
  detMat_eq_of_rowOps (a2GridLap 3) opsA2GridLap3 5393920 (by decide)

/-- **T2f Master Export:**
    1. Exact `det4 (a2GridLap 2) = 1,092` and direct 9×9 Laplace determinant `detMat 9 (a2GridLap 3) = 5,393,920`.
    2. Exact Klein-4 integer block-diagonalization `Q_{𝔸₂} (4 Q_{𝔸₂}^{-1}) = 4 I_9`,
       `L_{𝔸₂,3×3} Q_{𝔸₂} = Q_{𝔸₂} diag(7, B_{2a}, B_{2b}, B_4)` with product `7 * 28 * 40 * 688 = 5,393,920`.
    3. Explicit legal Dhar toppling traces on `2×2` (`[4,3,3,4]`) and `3×3` (`[4,2,3,2,0,2,3,2,4]`).
       (No Matrix–Tree or critical-group-identity theorem is formalized.) -/
theorem t2f_a2_grid_orders_and_dhar_identity :
    det4 (a2GridLap 2) = 1092 ∧
    detMat 9 (a2GridLap 3) = 5393920 ∧
    (∀ i j : Fin 9, matMul9 qA2Mat qA2Inv4 i j = if i = j then 4 else 0) ∧
    (∀ i j : Fin 9, matMul9 (a2GridLap 3) qA2Mat i j = matMul9 qA2Mat blockDiagA2 i j) ∧
    (7 * det2 (b2aA2 0 0) (b2aA2 0 1) (b2aA2 1 0) (b2aA2 1 1) *
         det2 (b2bA2 0 0) (b2bA2 0 1) (b2bA2 1 0) (b2bA2 1 1) *
         det4 b4A2 = 5393920) ∧
    (LegalTrace (a2GridGraph 2) traceIdA2_2x2 (fun i => idA2_2x2 i + idA2_2x2 i) ∧
     toppleList (a2GridGraph 2) traceIdA2_2x2 (fun i => idA2_2x2 i + idA2_2x2 i) = idA2_2x2 ∧
     IsStable (a2GridGraph 2) idA2_2x2 ∧
     LegalTrace (a2GridGraph 2) trace2MaxA2_2x2 (fun _ => 10) ∧
     toppleList (a2GridGraph 2) trace2MaxA2_2x2 (fun _ => 10) = s2MaxA2_2x2 ∧
     IsStable (a2GridGraph 2) s2MaxA2_2x2 ∧
     LegalTrace (a2GridGraph 2) traceDharA2_2x2 (fun i => 10 - s2MaxA2_2x2 i) ∧
     toppleList (a2GridGraph 2) traceDharA2_2x2 (fun i => 10 - s2MaxA2_2x2 i) = idA2_2x2) ∧
    (LegalTrace (a2GridGraph 3) traceIdA2_3x3 (fun i => idA2_3x3 i + idA2_3x3 i) ∧
     toppleList (a2GridGraph 3) traceIdA2_3x3 (fun i => idA2_3x3 i + idA2_3x3 i) = idA2_3x3 ∧
     IsStable (a2GridGraph 3) idA2_3x3 ∧
     LegalTrace (a2GridGraph 3) trace2MaxA2_3x3 (fun _ => 10) ∧
     toppleList (a2GridGraph 3) trace2MaxA2_3x3 (fun _ => 10) = s2MaxA2_3x3 ∧
     IsStable (a2GridGraph 3) s2MaxA2_3x3 ∧
     LegalTrace (a2GridGraph 3) traceDharA2_3x3 (fun i => 10 - s2MaxA2_3x3 i) ∧
     toppleList (a2GridGraph 3) traceDharA2_3x3 (fun i => 10 - s2MaxA2_3x3 i) = idA2_3x3) := by
  have h2_id := toppleListArr_sound (a2GridGraph 2) traceIdA2_2x2 (fun i => idA2_2x2 i + idA2_2x2 i)
    ((List.finRange 4).map (fun i => idA2_2x2 i + idA2_2x2 i)) (by decide) (by decide)
  have h2_2m := toppleListArr_sound (a2GridGraph 2) trace2MaxA2_2x2 (fun _ => 10)
    ((List.finRange 4).map (fun _ => 10)) (by decide) (by decide)
  have h2_dh := toppleListArr_sound (a2GridGraph 2) traceDharA2_2x2 (fun i => 10 - s2MaxA2_2x2 i)
    ((List.finRange 4).map (fun i => 10 - s2MaxA2_2x2 i)) (by decide) (by decide)
  have h3_id := toppleListArr_sound (a2GridGraph 3) traceIdA2_3x3 (fun i => idA2_3x3 i + idA2_3x3 i)
    ((List.finRange 9).map (fun i => idA2_3x3 i + idA2_3x3 i)) (by decide) (by decide)
  have h3_2m := toppleListArr_sound (a2GridGraph 3) trace2MaxA2_3x3 (fun _ => 10)
    ((List.finRange 9).map (fun _ => 10)) (by decide) (by decide)
  have h3_dh := toppleListArr_sound (a2GridGraph 3) traceDharA2_3x3 (fun i => 10 - s2MaxA2_3x3 i)
    ((List.finRange 9).map (fun i => 10 - s2MaxA2_3x3 i)) (by decide) (by decide)
  refine ⟨by decide, detMat_a2GridLap3, by decide, by decide, by decide, ?_, ?_⟩
  · refine ⟨h2_id.1, funext (fun i => by rw [← h2_id.2 i]; revert i; decide),
            isStable_of_bool _ _ (by decide),
            h2_2m.1, funext (fun i => by rw [← h2_2m.2 i]; revert i; decide),
            isStable_of_bool _ _ (by decide),
            h2_dh.1, funext (fun i => by rw [← h2_dh.2 i]; revert i; decide)⟩
  · refine ⟨h3_id.1, funext (fun i => by rw [← h3_id.2 i]; revert i; decide),
            isStable_of_bool _ _ (by decide),
            h3_2m.1, funext (fun i => by rw [← h3_2m.2 i]; revert i; decide),
            isStable_of_bool _ _ (by decide),
            h3_dh.1, funext (fun i => by rw [← h3_dh.2 i]; revert i; decide)⟩

end

end ApollonianSandpileMarkov.SandpileTropical
