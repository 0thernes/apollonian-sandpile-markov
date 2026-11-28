module
-- SPDX-License-Identifier: Apache-2.0
public import Challenge

/-!
# Standalone Palomar Comparator Verified Solution (`apollonian-sandpile-markov` v3.0.1)

Complete kernel-checked implementation of all 17 Palomar Registry Comparator theorems,
discharged directly from the verified `ApollonianSandpileMarkov.*` library with zero `sorry`,
zero `admit`, zero `native_decide`, and zero custom axioms. The definition block matches
the standalone `PalomarChallenge.lean` contract verbatim.
-/

namespace ApollonianSandpileMarkov.Palomar
@[expose] public section

/-! ### Pillar I Definitions (Jacobi, Descartes/Apollonian, Octahedral, General d-Dim Soddy) -/

def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

def signNeg1 (n : Nat) : Int :=
  if n % 4 == 1 then 1 else -1

def signTwo (n : Nat) : Int :=
  if n % 8 == 1 || n % 8 == 7 then 1 else -1

def signQR (m n : Nat) : Int :=
  if m % 4 == 3 && n % 4 == 3 then -1 else 1

def legendreNat (a p : Nat) : Int :=
  if a % p == 0 then 0
  else if (a ^ ((p - 1) / 2)) % p == 1 then 1
  else -1

def smallestFactorAux (n d fuel : Nat) : Nat :=
  match fuel with
  | 0 => n
  | fuel' + 1 =>
    if d * d > n then n
    else if n % d = 0 then d
    else smallestFactorAux n (d + 1) fuel'

def smallestFactor (n : Nat) : Nat :=
  if n ≤ 1 then n else smallestFactorAux n 2 n

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

def legendreListProd (a : Nat) : List Nat → Int
  | [] => 1
  | p :: ps => legendreNat a p * legendreListProd a ps

def jacobiNat (a n : Nat) : Int :=
  legendreListProd a (primeFactors n)

def jacobi (a : Int) (n : Nat) : Int :=
  if n == 0 then 0 else jacobiNat (a % (n : Int)).toNat n

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

def halfK (a b c d : Int) : Int := (a + b + c - d) / 2

def bqf (a b c d x y : Int) : Int :=
  (a + b) * x * x + 2 * halfK a b c d * x * y + (a + c) * y * y

def rootHKRS1 : Quad := ⟨-3, 5, 8, 8⟩
def rootHKRS2 : Quad := ⟨-7, 17, 12, 20⟩
def rootHKRS3 : Quad := ⟨-11, 21, 24, 28⟩
def rootSquareContrast : Quad := ⟨9, 9, -4, 8⟩

structure OctSext where
  b1 : Int
  b2 : Int
  b3 : Int
  b4 : Int
  b5 : Int
  b6 : Int
deriving DecidableEq, Repr

def IsOctahedral (x : OctSext) : Prop :=
  let S := x.b1 + x.b4
  x.b2 + x.b5 = S ∧ x.b3 + x.b6 = S ∧
  (x.b1 - x.b4) * (x.b1 - x.b4) + (x.b2 - x.b5) * (x.b2 - x.b5) +
  (x.b3 - x.b6) * (x.b3 - x.b6) = 2 * S * S

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

def octRootObstructed : OctSext := ⟨-6, 10, 17, 40, 24, 17⟩
def octRootStrip : OctSext := ⟨0, 0, 1, 2, 2, 1⟩

def HasOctMod8Pattern (x : OctSext) : Prop :=
  x.b1 % 8 = 2 ∧ x.b4 % 8 = 0 ∧ x.b2 % 8 = 2 ∧ x.b5 % 8 = 0 ∧ x.b3 % 8 = 1 ∧ x.b6 % 8 = 1

def sumNatInt (n : Nat) (f : Nat → Int) : Int :=
  match n with
  | 0 => 0
  | k + 1 => sumNatInt k f + f k

def sumFinInt {n : Nat} (f : Fin n → Int) : Int :=
  sumNatInt n (fun i => if h : i < n then f ⟨i, h⟩ else 0)

def soddyQ (d : Nat) (b : Fin (d + 2) → Int) : Int :=
  (sumFinInt b) ^ 2 - (d : Int) * sumFinInt (fun i => b i * b i)

def soddyRefl (d : Nat) (α : Int) (k : Fin (d + 2)) (b : Fin (d + 2) → Int) : Fin (d + 2) → Int :=
  fun i => if i = k then α * (sumFinInt b - b k) - b k else b i

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

/-! ### Pillar II Definitions (Sandpiles, Grid Laplacians, Determinants, Lattice PDEs, Polygons) -/

def sumNat (n : Nat) (f : Nat → Int) : Int :=
  match n with
  | 0 => 0
  | k + 1 => sumNat k f + f k

def sumFin {n : Nat} (f : Fin n → Int) : Int :=
  sumNat n (fun i => if h : i < n then f ⟨i, h⟩ else 0)

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

def IsStabilizingOdometer {n : Nat} (G : SandpileGraph n) (s : Config n) (w : Fin n → Nat) : Prop :=
  ∀ i : Fin n,
    s i - (G.deg i : Int) * (w i : Int) +
    sumFin (fun j => (G.adj j i : Int) * (w j : Int)) < (G.deg i : Int)

def sumAdj {n : Nat} (G : SandpileGraph n) (i : Fin n) : Int :=
  sumFin (fun j => (G.adj i j : Int))

def IsDissipative {n : Nat} (G : SandpileGraph n) : Prop :=
  ∀ i : Fin n, sumAdj G i ≤ (G.deg i : Int)

inductive ReachesSink {n : Nat} (G : SandpileGraph n) : Nat → Fin n → Prop
  | base {i : Fin n} : sumAdj G i < (G.deg i : Int) → ReachesSink G 0 i
  | step {d : Nat} {i j : Fin n} : 0 < G.adj i j → ReachesSink G d j → ReachesSink G (d + 1) i

def HasReachableSink {n : Nat} (G : SandpileGraph n) : Prop :=
  ∀ i : Fin n, ∃ d : Nat, ReachesSink G d i

def gridAdj (k : Nat) (i j : Fin (k * k)) : Nat :=
  let r1 := i.val / k; let c1 := i.val % k
  let r2 := j.val / k; let c2 := j.val % k
  let dr := if r1 ≥ r2 then r1 - r2 else r2 - r1
  let dc := if c1 ≥ c2 then c1 - c2 else c2 - c1
  if dr + dc == 1 then 1 else 0

theorem gridAdj_diag (k : Nat) (i : Fin (k * k)) : gridAdj k i i = 0 := by
  unfold gridAdj; simp

theorem gridAdj_symm (k : Nat) (i j : Fin (k * k)) : gridAdj k i j = gridAdj k j i := by
  unfold gridAdj
  dsimp only
  have h1 : (if i.val / k ≥ j.val / k then i.val / k - j.val / k else j.val / k - i.val / k) =
            (if j.val / k ≥ i.val / k then j.val / k - i.val / k else i.val / k - j.val / k) := by
    split <;> split <;> omega
  have h2 : (if i.val % k ≥ j.val % k then i.val % k - j.val % k else j.val % k - i.val % k) =
            (if j.val % k ≥ i.val % k then j.val % k - i.val % k else i.val % k - j.val % k) := by
    split <;> split <;> omega
  rw [h1, h2]

def gridGraph (k : Nat) : SandpileGraph (k * k) where
  adj := gridAdj k
  deg _ := 4
  adj_diag := gridAdj_diag k
  adj_symm := gridAdj_symm k

def gridLap (k : Nat) (i j : Fin (k * k)) : Int :=
  if i = j then 4 else - ((gridGraph k).adj i j : Int)

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

def skipFin {n : Nat} (k : Fin (n + 1)) (i : Fin n) : Fin (n + 1) :=
  if i.val < k.val then ⟨i.val, by omega⟩ else ⟨i.val + 1, by omega⟩

def minorMat {n : Nat} (M : Fin (n + 1) → Fin (n + 1) → Int) (r c : Fin (n + 1)) :
    Fin n → Fin n → Int :=
  fun i j => M (skipFin r i) (skipFin c j)

def signNat (j : Nat) : Int := if j % 2 = 0 then 1 else -1

def detMat : (n : Nat) → (Fin n → Fin n → Int) → Int
  | 0, _ => 1
  | n + 1, M =>
    sumFin (fun j : Fin (n + 1) => signNat j.val * M 0 j * detMat n (minorMat M 0 j))

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

def id2x2 : Config 4 := fun _ => 2

def id3x3 : Config 9 := fun i =>
  match i.val with
  | 0 => 2 | 1 => 1 | 2 => 2
  | 3 => 1 | 4 => 0 | 5 => 1
  | 6 => 2 | 7 => 1 | 8 => 2
  | _ => 0

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

def lapZ2 (u : Int → Int → Int) (x y : Int) : Int :=
  u (x + 1) y + u (x - 1) y + u x (y + 1) + u x (y - 1) - 4 * u x y

def IsPeriodic2D (Px Py : Nat) (ψ : Int → Int → Int) : Prop :=
  1 ≤ Px ∧ 1 ≤ Py ∧
  (∀ x y : Int, ψ (x + (Px : Int)) y = ψ x y) ∧
  (∀ x y : Int, ψ x (y + (Py : Int)) = ψ x y)

def uZ2_lap2 (x y : Int) : Int := (x * (x - 1)) / 2 + (y * (y - 1)) / 2
def uZ2_lap3a (x y : Int) : Int := x * x + (y * (y - 1)) / 2
def uZ2_lap3b (x y : Int) : Int := (x * (x - 1)) / 2 + y * y
def uZ2_lap3c (x y : Int) : Int := x * x + x * y + (y * (y - 1)) / 2

def lapA2 (u : Int → Int → Int) (x y : Int) : Int :=
  u (x + 1) y + u (x - 1) y + u x (y + 1) + u x (y - 1) +
  u (x + 1) (y - 1) + u (x - 1) (y + 1) - 6 * u x y

def uA2_lap4 (x y : Int) : Int := (x * (x - 1)) / 2 + (y * (y - 1)) / 2
def uA2_lap2 (x _y : Int) : Int := (x * (x - 1)) / 2

abbrev Vec2 := Int × Int

def vadd (a b : Vec2) : Vec2 := (a.1 + b.1, a.2 + b.2)
def vsub (a b : Vec2) : Vec2 := (a.1 - b.1, a.2 - b.2)
def rot90 (v : Vec2) : Vec2 := (-v.2, v.1)
def det2v (a b : Vec2) : Int := a.1 * b.2 - a.2 * b.1

def sumVec : List Vec2 → Vec2
  | [] => (0, 0)
  | v :: vs => vadd v (sumVec vs)

def chainNormals : Vec2 → List Vec2 → List Vec2
  | _, [] => []
  | prev, v :: vs => rot90 (vsub v prev) :: chainNormals v vs

def cycleNormals : List Vec2 → List Vec2
  | [] => []
  | v0 :: vs => chainNormals v0 (vs ++ [v0])

def a2GridAdj (k : Nat) (i j : Fin (k * k)) : Nat :=
  let r1 := i.val / k; let c1 := i.val % k
  let r2 := j.val / k; let c2 := j.val % k
  let dr := if r1 ≥ r2 then r1 - r2 else r2 - r1
  let dc := if c1 ≥ c2 then c1 - c2 else c2 - c1
  if dr + dc == 1 then 1
  else if (r1 + 1 == r2 && c2 + 1 == c1) || (r2 + 1 == r1 && c1 + 1 == c2) then 1
  else 0

theorem a2GridAdj_diag (k : Nat) (i : Fin (k * k)) : a2GridAdj k i i = 0 := by
  unfold a2GridAdj
  have h1 : ¬ (i.val / k + 1 == i.val / k) := by simp only [beq_iff_eq]; omega
  have h2 : ¬ (i.val % k + 1 == i.val % k) := by simp only [beq_iff_eq]; omega
  simp [h1, h2]

theorem a2GridAdj_symm (k : Nat) (i j : Fin (k * k)) : a2GridAdj k i j = a2GridAdj k j i := by
  unfold a2GridAdj
  dsimp only
  have h1 : (if i.val / k ≥ j.val / k then i.val / k - j.val / k else j.val / k - i.val / k) =
            (if j.val / k ≥ i.val / k then j.val / k - i.val / k else i.val / k - j.val / k) := by
    split <;> split <;> omega
  have h2 : (if i.val % k ≥ j.val % k then i.val % k - j.val % k else j.val % k - i.val % k) =
            (if j.val % k ≥ i.val % k then j.val % k - i.val % k else i.val % k - j.val % k) := by
    split <;> split <;> omega
  rw [h1, h2, Bool.or_comm]

def a2GridGraph (k : Nat) : SandpileGraph (k * k) where
  adj := a2GridAdj k
  deg _ := 6
  adj_diag := a2GridAdj_diag k
  adj_symm := a2GridAdj_symm k

def a2GridLap (k : Nat) (i j : Fin (k * k)) : Int :=
  if i = j then 6 else - ((a2GridGraph k).adj i j : Int)

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

/-! ### Pillar III Definitions (SL2(Z) Cohn Tree, Markov Tree, 5-Step Quiver, Hurwitz n=4) -/

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
def Mat2.comm (A B : Mat2) : Mat2 := Mat2.mul (Mat2.mul (Mat2.mul A B) A.inv) B.inv

def cohnA0 : Mat2 := ⟨1, 1, 1, 2⟩
def cohnB0 : Mat2 := ⟨1, 2, 2, 5⟩

inductive InCohnTree : Mat2 → Mat2 → Prop
  | base : InCohnTree cohnA0 cohnB0
  | left {A B} : InCohnTree A B → InCohnTree A (Mat2.mul A B)
  | right {A B} : InCohnTree A B → InCohnTree (Mat2.mul A B) B

inductive InMarkovTree : Int → Int → Int → Prop
  | base : InMarkovTree 1 1 1
  | s1 {x y z} : InMarkovTree x y z → InMarkovTree (3 * y * z - x) y z
  | s2 {x y z} : InMarkovTree x y z → InMarkovTree x (3 * x * z - y) z
  | s3 {x y z} : InMarkovTree x y z → InMarkovTree x y (3 * x * y - z)

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

def IsHurwitz4 (a x1 x2 x3 x4 : Nat) : Prop :=
  1 ≤ a ∧ 1 ≤ x1 ∧ 1 ≤ x2 ∧ 1 ≤ x3 ∧ 1 ≤ x4 ∧
  x1 * x1 + x2 * x2 + x3 * x3 + x4 * x4 = a * x1 * x2 * x3 * x4

inductive InHurwitz4Orbit (a r1 r2 r3 r4 : Nat) : Nat → Nat → Nat → Nat → Prop
  | base : InHurwitz4Orbit a r1 r2 r3 r4 r1 r2 r3 r4
  | swap12 {x1 x2 x3 x4} : InHurwitz4Orbit a r1 r2 r3 r4 x1 x2 x3 x4 → InHurwitz4Orbit a r1 r2 r3 r4 x2 x1 x3 x4
  | swap23 {x1 x2 x3 x4} : InHurwitz4Orbit a r1 r2 r3 r4 x1 x2 x3 x4 → InHurwitz4Orbit a r1 r2 r3 r4 x1 x3 x2 x4
  | swap34 {x1 x2 x3 x4} : InHurwitz4Orbit a r1 r2 r3 r4 x1 x2 x3 x4 → InHurwitz4Orbit a r1 r2 r3 r4 x1 x2 x4 x3
  | vieta4 {x1 x2 x3 x4} : InHurwitz4Orbit a r1 r2 r3 r4 x1 x2 x3 x4 →
      InHurwitz4Orbit a r1 r2 r3 r4 x1 x2 x3 (a * x1 * x2 * x3 - x4)

/-! ### 17 Headline Comparator Theorem Contracts -/

abbrev T1a_DescartesLorentzianAndGaussianNorm : Prop :=
  (∀ q : Quad, refl1 (refl1 q) = q ∧ refl2 (refl2 q) = q ∧ refl3 (refl3 q) = q ∧ refl4 (refl4 q) = q ∧
    (refl1 q).descartes = q.descartes ∧ (refl2 q).descartes = q.descartes ∧
    (refl3 q).descartes = q.descartes ∧ (refl4 q).descartes = q.descartes) ∧
  (∀ a b c d : Int, descartesQ a b c d = 0 →
    (a + b) * (a + c) = a * a + halfK a b c d * halfK a b c d) ∧
  (∀ a b c d x1 y1 x2 y2 : Int, descartesQ a b c d = 0 →
    bqf a b c d x1 y1 * bqf a b c d x2 y2 =
    ((a + b) * x1 * x2 + halfK a b c d * (x1 * y2 + x2 * y1) + (a + c) * y1 * y2) ^ 2 +
    a * a * (x1 * y2 - x2 * y1) ^ 2)

abbrev T1b_JacobiReciprocityMaster : Prop :=
  (∀ (n : Nat), 1 ≤ n → n % 2 = 1 → jacobi (-1) n = signNeg1 n) ∧
  (∀ (n : Nat), 1 ≤ n → n % 2 = 1 → jacobi 2 n = signTwo n) ∧
  (∀ (m n : Nat), 1 ≤ m → 1 ≤ n → m % 2 = 1 → n % 2 = 1 → Nat.Coprime m n →
    jacobi (m : Int) n * jacobi (n : Int) m = signQR m n) ∧
  (∀ (n : Nat) (a b : Int), 1 ≤ n → n % 2 = 1 → jacobi (a * b) n = jacobi a n * jacobi b n) ∧
  (∀ (n : Nat) (a : Int), 1 ≤ n → n % 2 = 1 → Nat.Coprime a.natAbs n → jacobi (a * a) n = 1)

abbrev T1c_HKRSApollonianReciprocityObstruction : Prop :=
  (∀ q, InApollonianOrbit rootHKRS1 q → ∀ m : Int, q.a ≠ m * m ∧ q.b ≠ m * m ∧ q.c ≠ m * m ∧ q.d ≠ m * m) ∧
  (∀ q, InApollonianOrbit rootHKRS2 q → ∀ m : Int, q.a ≠ m * m ∧ q.b ≠ m * m ∧ q.c ≠ m * m ∧ q.d ≠ m * m) ∧
  (∀ q, InApollonianOrbit rootHKRS3 q → ∀ m : Int, q.a ≠ m * m ∧ q.b ≠ m * m ∧ q.c ≠ m * m ∧ q.d ≠ m * m) ∧
  (rootSquareContrast.descartes = 0 ∧ rootSquareContrast.a = 3 * 3)

abbrev T1d_OctahedralLorentzianAndSqrtNeg2Obstruction : Prop :=
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
   IsOctahedral octRootStrip ∧ octRootStrip.b3 = 1 * 1 ∧ octRootStrip.b4 = 2 * (1 * 1))

abbrev T1e_SoddyDimensionDichotomyAnd3DContrast : Prop :=
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
   (soddy3Refl2 ⟨-6, 13, 13, 13, 18⟩).b2 = 25 ∧ 25 = 5 * 5)

abbrev T2a_AbelianSandpileConfluenceAndLeastAction : Prop :=
  (∀ {n} (G : SandpileGraph n) (u v : Fin n) (s : Config n),
    topple G u (topple G v s) = topple G v (topple G u s)) ∧
  (∀ {n} (G : SandpileGraph n) (L : List (Fin n)) (s : Config n) (w : Fin n → Nat),
    LegalTrace G L s → IsStabilizingOdometer G s w → ∀ i, countFin L i ≤ w i) ∧
  (∀ {n} (G : SandpileGraph n) (s : Config n) (L1 L2 : List (Fin n)),
    LegalTrace G L1 s → IsStable G (toppleList G L1 s) →
    LegalTrace G L2 s → IsStable G (toppleList G L2 s) →
    (∀ i, countFin L1 i = countFin L2 i) ∧ toppleList G L1 s = toppleList G L2 s) ∧
  (∀ {n} (G : SandpileGraph n), IsDissipative G → HasReachableSink G → ∀ s : Config n,
    (∃ B : Nat, ∀ L : List (Fin n), LegalTrace G L s → L.length ≤ B) ∧
    (∃ L : List (Fin n), LegalTrace G L s ∧ IsStable G (toppleList G L s)))

abbrev T2b_DharCriticalIdentityAndGridOrders : Prop :=
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
   toppleList (gridGraph 3) traceDhar3x3 (fun i => 6 - s2Max3x3 i) = id3x3)

abbrev T2c_LPSZ2SuperharmonicAndIsotropicObstruction : Prop :=
  (∀ {Px Py : Nat} {u ψ : Int → Int → Int},
    IsPeriodic2D Px Py ψ →
    (∀ x y, 4 * u x y = 3 * (x * x + y * y) + ψ x y) →
    (∀ x y, lapZ2 u x y ≤ 3) → False) ∧
  (∀ x y : Int,
    lapZ2 uZ2_lap2 x y = 2 ∧
    lapZ2 uZ2_lap3a x y = 3 ∧
    lapZ2 uZ2_lap3b x y = 3 ∧
    lapZ2 uZ2_lap3c x y = 3)

abbrev T2d_TriangularA2EvenLaplacianRigidityAndObstruction : Prop :=
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
  (∀ x y : Int, lapA2 uA2_lap4 x y = 4 ∧ lapA2 uA2_lap2 x y = 2)

abbrev T2e_KalininShkolnikovTropicalBalancingAndSolitons : Prop :=
  (∀ vs : List Vec2, sumVec (cycleNormals vs) = (0, 0)) ∧
  (∀ v1 v2 v3 : Vec2, vadd (vadd v1 v2) v3 = (0, 0) →
    det2v v1 v2 = det2v v2 v3 ∧ det2v v2 v3 = det2v v3 v1) ∧
  (vadd (vadd (1, 0) (0, 1)) (-1, -1) = (0, 0) ∧ det2v (1, 0) (0, 1) = 1) ∧
  (sumVec [(1, 0), (0, 1), (-1, 1), (0, -2)] = (0, 0) ∧
   vadd (vadd (1, 0) (0, 1)) (-1, -1) = (0, 0) ∧
   vadd (vadd (-1, 1) (0, -2)) (1, 1) = (0, 0) ∧
   det2v (-1, 1) (0, -2) = 2)

abbrev T2f_A2GridOrdersAndDharIdentity : Prop :=
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
   toppleList (a2GridGraph 3) traceDharA2_3x3 (fun i => 10 - s2MaxA2_3x3 i) = idA2_3x3)

abbrev T3a_SL2ZFrickeCohnMarkovCorrespondence : Prop :=
  (∀ A B : Mat2, A.det = 1 → B.det = 1 →
    (A.tr) ^ 2 + (B.tr) ^ 2 + (Mat2.mul A B).tr ^ 2 =
    A.tr * B.tr * (Mat2.mul A B).tr + (Mat2.comm A B).tr + 2) ∧
  (∀ A B : Mat2, InCohnTree A B →
    A.det = 1 ∧ B.det = 1 ∧ (Mat2.comm A B).tr = -2 ∧
    (3 : Int) ∣ A.tr ∧ (3 : Int) ∣ B.tr ∧ (3 : Int) ∣ (Mat2.mul A B).tr ∧
    (A.tr / 3) ^ 2 + (B.tr / 3) ^ 2 + ((Mat2.mul A B).tr / 3) ^ 2 =
    3 * (A.tr / 3) * (B.tr / 3) * ((Mat2.mul A B).tr / 3)) ∧
  (cohnA0.tr / 3 = 1 ∧ cohnB0.tr / 3 = 2 ∧ (Mat2.mul cohnA0 cohnB0).tr / 3 = 5)

abbrev T3b_MarkovCoprimalityOddPrimesAndMod32 : Prop :=
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
  (InMarkovTree 2 1 1 ∧ InMarkovTree 34 13 1 ∧ (2 : Int) % 64 = 2 ∧ (34 : Int) % 64 = 34)

abbrev T3c_HenselSqrtNeg1PrimePowerUniqueness : Prop :=
  ∀ {p k : Nat}, IsPrime p → p % 2 = 1 → 1 ≤ k →
    ∀ r1 r2 : Int,
      ((p ^ k : Nat) : Int) ∣ (r1 * r1 + 1) →
      ((p ^ k : Nat) : Int) ∣ (r2 * r2 + 1) →
      ((p ^ k : Nat) : Int) ∣ (r1 - r2) ∨ ((p ^ k : Nat) : Int) ∣ (r1 + r2)

abbrev T3d_ClusterAlgebraMarkovLaurentPositivity : Prop :=
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
   markovP4 1 1 1 = 433 ∧ markovP5 1 1 1 = 37666)

abbrev T3e_MarkovHurwitzN4CompleteClassification : Prop :=
  (∀ a x1 x2 x3 x4 : Nat, IsHurwitz4 a x1 x2 x3 x4 →
    (a = 1 ∧ x1 % 4 = 2 ∧ x2 % 4 = 2 ∧ x3 % 4 = 2 ∧ x4 % 4 = 2) ∨
    (a = 4 ∧ x1 % 2 = 1 ∧ x2 % 2 = 1 ∧ x3 % 2 = 1 ∧ x4 % 2 = 1)) ∧
  (∀ a x1 x2 x3 x4 : Nat, (a = 2 ∨ a = 3 ∨ 5 ≤ a) → ¬ IsHurwitz4 a x1 x2 x3 x4) ∧
  (∀ x1 x2 x3 x4 : Nat, IsHurwitz4 1 x1 x2 x3 x4 ↔ InHurwitz4Orbit 1 2 2 2 2 x1 x2 x3 x4) ∧
  (∀ x1 x2 x3 x4 : Nat, IsHurwitz4 4 x1 x2 x3 x4 ↔ InHurwitz4Orbit 4 1 1 1 1 x1 x2 x3 x4) ∧
  (IsHurwitz4 1 2 2 2 2 ∧ IsHurwitz4 1 2 2 2 6 ∧
   IsHurwitz4 4 1 1 1 1 ∧ IsHurwitz4 4 1 1 1 3)

abbrev AllApollonianSandpileMarkovTheorems : Prop :=
  T1a_DescartesLorentzianAndGaussianNorm ∧
  T1b_JacobiReciprocityMaster ∧
  T1c_HKRSApollonianReciprocityObstruction ∧
  T1d_OctahedralLorentzianAndSqrtNeg2Obstruction ∧
  T1e_SoddyDimensionDichotomyAnd3DContrast ∧
  T2a_AbelianSandpileConfluenceAndLeastAction ∧
  T2b_DharCriticalIdentityAndGridOrders ∧
  T2c_LPSZ2SuperharmonicAndIsotropicObstruction ∧
  T2d_TriangularA2EvenLaplacianRigidityAndObstruction ∧
  T2e_KalininShkolnikovTropicalBalancingAndSolitons ∧
  T2f_A2GridOrdersAndDharIdentity ∧
  T3a_SL2ZFrickeCohnMarkovCorrespondence ∧
  T3b_MarkovCoprimalityOddPrimesAndMod32 ∧
  T3c_HenselSqrtNeg1PrimePowerUniqueness ∧
  T3d_ClusterAlgebraMarkovLaurentPositivity ∧
  T3e_MarkovHurwitzN4CompleteClassification

/-! ### Structural Equivalence Bridges to Verified `ApollonianSandpileMarkov.*` Library -/

private theorem smallestFactorAux_eq_core (n d fuel : Nat) :
    smallestFactorAux n d fuel = JacobiReciprocity.smallestFactorAux n d fuel := by
  induction fuel generalizing d with
  | zero => rfl
  | succ f ih =>
    simp only [smallestFactorAux, JacobiReciprocity.smallestFactorAux]
    split
    · rfl
    · split
      · rfl
      · exact ih (d + 1)

private theorem smallestFactor_eq_core (n : Nat) :
    smallestFactor n = JacobiReciprocity.smallestFactor n := by
  unfold smallestFactor JacobiReciprocity.smallestFactor
  split
  · rfl
  · exact smallestFactorAux_eq_core n 2 n

private theorem primeFactorsAux_eq_core (n fuel : Nat) :
    primeFactorsAux n fuel = JacobiReciprocity.primeFactorsAux n fuel := by
  induction fuel generalizing n with
  | zero => rfl
  | succ f ih =>
    simp only [primeFactorsAux, JacobiReciprocity.primeFactorsAux]
    split
    · rfl
    · rw [smallestFactor_eq_core, ih]

private theorem legendreListProd_eq_core (a : Nat) (ps : List Nat) :
    legendreListProd a ps = JacobiReciprocity.legendreListProd a ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [legendreListProd, JacobiReciprocity.legendreListProd, ih]
    rfl

private theorem jacobi_eq_core (a : Int) (n : Nat) :
    jacobi a n = JacobiReciprocity.jacobi a n := by
  unfold jacobi JacobiReciprocity.jacobi jacobiNat JacobiReciprocity.jacobiNat
    primeFactors JacobiReciprocity.primeFactors
  split
  · rfl
  · rw [primeFactorsAux_eq_core, legendreListProd_eq_core]

private theorem sumNatInt_eq_core (n : Nat) (f : Nat → Int) :
    sumNatInt n f = ApollonianReciprocity.sumNatInt n f := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumNatInt, ApollonianReciprocity.sumNatInt, ih]

private theorem sumFinInt_eq_core {n : Nat} (f : Fin n → Int) :
    sumFinInt f = ApollonianReciprocity.sumFinInt f :=
  sumNatInt_eq_core n _

private theorem soddyQ_eq_core (d : Nat) (b : Fin (d + 2) → Int) :
    soddyQ d b = ApollonianReciprocity.soddyQ d b := by
  unfold soddyQ ApollonianReciprocity.soddyQ
  rw [sumFinInt_eq_core, sumFinInt_eq_core]

private theorem soddyRefl_eq_core (d : Nat) (α : Int) (k : Fin (d + 2)) (b : Fin (d + 2) → Int) :
    soddyRefl d α k b = ApollonianReciprocity.soddyRefl d α k b := by
  funext i
  unfold soddyRefl ApollonianReciprocity.soddyRefl
  rw [sumFinInt_eq_core]

private theorem sumNat_eq_core (n : Nat) (f : Nat → Int) :
    sumNat n f = SandpileTropical.sumNat n f := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumNat, SandpileTropical.sumNat, ih]

private theorem sumFin_eq_core {n : Nat} (f : Fin n → Int) :
    sumFin f = SandpileTropical.sumFin f :=
  sumNat_eq_core n _

private theorem countFin_eq_core {n : Nat} (L : List (Fin n)) (i : Fin n) :
    countFin L i = SandpileTropical.countFin L i := by
  induction L with
  | nil => rfl
  | cons u us ih => simp only [countFin, SandpileTropical.countFin, ih]

private theorem detMat_eq_core : ∀ (n : Nat) (M : Fin n → Fin n → Int),
    detMat n M = SandpileTropical.detMat n M
  | 0, _ => rfl
  | n + 1, M => by
    simp only [detMat, SandpileTropical.detMat]
    rw [sumFin_eq_core]
    congr 1
    funext j
    rw [detMat_eq_core n]
    rfl

private theorem matMul9_eq_core (A B : Fin 9 → Fin 9 → Int) (i j : Fin 9) :
    matMul9 A B i j = SandpileTropical.matMul9 A B i j :=
  sumFin_eq_core _

private theorem sumVec_eq_core (vs : List Vec2) :
    sumVec vs = SandpileTropical.sumVec vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [sumVec, SandpileTropical.sumVec, ih]; rfl

private theorem chainNormals_eq_core (a : Vec2) (vs : List Vec2) :
    chainNormals a vs = SandpileTropical.chainNormals a vs := by
  induction vs generalizing a with
  | nil => rfl
  | cons v vs ih => simp only [chainNormals, SandpileTropical.chainNormals, ih]; rfl

private theorem cycleNormals_eq_core (vs : List Vec2) :
    cycleNormals vs = SandpileTropical.cycleNormals vs := by
  cases vs with
  | nil => rfl
  | cons v0 vs => exact chainNormals_eq_core v0 (vs ++ [v0])

private def toCoreQuad (q : Quad) : ApollonianReciprocity.Quad := ⟨q.a, q.b, q.c, q.d⟩

private theorem inApollonianOrbit_toCore {r q : Quad} (h : InApollonianOrbit r q) :
    ApollonianReciprocity.InApollonianOrbit (toCoreQuad r) (toCoreQuad q) := by
  induction h with
  | base => exact .base
  | s1 _ ih => exact .s1 ih
  | s2 _ ih => exact .s2 ih
  | s3 _ ih => exact .s3 ih
  | s4 _ ih => exact .s4 ih

private def toCoreOct (x : OctSext) : ApollonianReciprocity.OctSext :=
  ⟨x.b1, x.b2, x.b3, x.b4, x.b5, x.b6⟩

private theorem toCoreOct_inj {x y : OctSext} (h : toCoreOct x = toCoreOct y) : x = y := by
  cases x; cases y
  injection h with h1 h2 h3 h4 h5 h6
  subst h1; subst h2; subst h3; subst h4; subst h5; subst h6; rfl

private theorem toCoreOct_octRefl (s1 s2 s3 : Bool) (x : OctSext) :
    toCoreOct (octRefl s1 s2 s3 x) = ApollonianReciprocity.octRefl s1 s2 s3 (toCoreOct x) := by
  cases s1 <;> cases s2 <;> cases s3 <;> rfl

private theorem inOctOrbit_toCore {r x : OctSext} (h : InOctOrbit r x) :
    ApollonianReciprocity.InOctOrbit (toCoreOct r) (toCoreOct x) := by
  induction h with
  | base => exact .base
  | step s1 s2 s3 _ ih =>
    rw [toCoreOct_octRefl]
    exact .step s1 s2 s3 ih

private def toCoreSoddy3 (s : Soddy3) : ApollonianReciprocity.Soddy3 :=
  ⟨s.b1, s.b2, s.b3, s.b4, s.b5⟩

private def toCoreGraph {n : Nat} (G : SandpileGraph n) : SandpileTropical.SandpileGraph n :=
  ⟨G.adj, G.deg, G.adj_diag, G.adj_symm⟩

private theorem sumAdj_eq_core {n : Nat} (G : SandpileGraph n) (i : Fin n) :
    sumAdj G i = SandpileTropical.sumAdj (toCoreGraph G) i :=
  sumFin_eq_core _

private theorem isDissipative_toCore {n : Nat} (G : SandpileGraph n) (h : IsDissipative G) :
    SandpileTropical.IsDissipative (toCoreGraph G) := fun i => by
  rw [← sumAdj_eq_core]; exact h i

private theorem isStabilizingOdometer_toCore {n : Nat} (G : SandpileGraph n) (s : Config n) (w : Fin n → Nat)
    (h : IsStabilizingOdometer G s w) : SandpileTropical.IsStabilizingOdometer (toCoreGraph G) s w := fun i => by
  have hi := h i
  rw [sumFin_eq_core] at hi
  exact hi

private theorem legalTrace_iff_core {n : Nat} (G : SandpileGraph n) (L : List (Fin n)) (s : Config n) :
    LegalTrace G L s ↔ SandpileTropical.LegalTrace (toCoreGraph G) L s := by
  induction L generalizing s with
  | nil => exact Iff.rfl
  | cons u us ih =>
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (ih _).mp h2⟩, fun ⟨h1, h2⟩ => ⟨h1, (ih _).mpr h2⟩⟩

private theorem toppleList_eq_core {n : Nat} (G : SandpileGraph n) (L : List (Fin n)) (s : Config n) :
    toppleList G L s = SandpileTropical.toppleList (toCoreGraph G) L s := by
  induction L generalizing s with
  | nil => rfl
  | cons u us ih => exact ih _

private theorem reachesSink_toCore {n : Nat} (G : SandpileGraph n) {d : Nat} {i : Fin n}
    (h : ReachesSink G d i) : SandpileTropical.ReachesSink (toCoreGraph G) d i := by
  induction h with
  | base hb => exact .base (by rw [← sumAdj_eq_core]; exact hb)
  | step ha _ ih => exact .step ha ih

private def toCoreMat2 (X : Mat2) : MarkovHurwitzCluster.Mat2 := ⟨X.a, X.b, X.c, X.d⟩

private theorem inCohnTree_toCore {A B : Mat2} (h : InCohnTree A B) :
    MarkovHurwitzCluster.InCohnTree (toCoreMat2 A) (toCoreMat2 B) := by
  induction h with
  | base => exact .base
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih

private theorem inMarkovTree_toCore {x y z : Int} (h : InMarkovTree x y z) :
    MarkovHurwitzCluster.InMarkovTree x y z := by
  induction h with
  | base => exact .base
  | s1 _ ih => exact .s1 ih
  | s2 _ ih => exact .s2 ih
  | s3 _ ih => exact .s3 ih

private theorem inMarkovTree_fromCore {x y z : Int} (h : MarkovHurwitzCluster.InMarkovTree x y z) :
    InMarkovTree x y z := by
  induction h with
  | base => exact .base
  | s1 _ ih => exact .s1 ih
  | s2 _ ih => exact .s2 ih
  | s3 _ ih => exact .s3 ih

private theorem inHurwitz4Orbit_toCore {a r1 r2 r3 r4 x1 x2 x3 x4 : Nat}
    (h : InHurwitz4Orbit a r1 r2 r3 r4 x1 x2 x3 x4) :
    MarkovHurwitzCluster.InHurwitz4Orbit a r1 r2 r3 r4 x1 x2 x3 x4 := by
  induction h with
  | base => exact .base
  | swap12 _ ih => exact .swap12 ih
  | swap23 _ ih => exact .swap23 ih
  | swap34 _ ih => exact .swap34 ih
  | vieta4 _ ih => exact .vieta4 ih

private theorem inHurwitz4Orbit_fromCore {a r1 r2 r3 r4 x1 x2 x3 x4 : Nat}
    (h : MarkovHurwitzCluster.InHurwitz4Orbit a r1 r2 r3 r4 x1 x2 x3 x4) :
    InHurwitz4Orbit a r1 r2 r3 r4 x1 x2 x3 x4 := by
  induction h with
  | base => exact .base
  | swap12 _ ih => exact .swap12 ih
  | swap23 _ ih => exact .swap23 ih
  | swap34 _ ih => exact .swap34 ih
  | vieta4 _ ih => exact .vieta4 ih

/-! ### 17 Verified Palomar Comparator Theorem Proofs -/

theorem t1a_descartes_lorentzian_and_gaussian_norm : T1a_DescartesLorentzianAndGaussianNorm := by
  have h := ApollonianReciprocity.t1a_descartes_lorentzian_and_gaussian_norm
  refine ⟨fun q => ?_, h.2.1, h.2.2⟩
  have hq := h.1 (toCoreQuad q)
  cases q with
  | mk a b c d =>
    rcases hq with ⟨h1, h2, h3, h4, d1, d2, d3, d4⟩
    refine ⟨?_, ?_, ?_, ?_, d1, d2, d3, d4⟩
    · injection h1 with ha hb hc hd; simp only [refl1]; congr
    · injection h2 with ha hb hc hd; simp only [refl2]; congr
    · injection h3 with ha hb hc hd; simp only [refl3]; congr
    · injection h4 with ha hb hc hd; simp only [refl4]; congr

theorem t1b_jacobi_reciprocity_master : T1b_JacobiReciprocityMaster := by
  have h := JacobiReciprocity.t1b_jacobi_reciprocity_master
  refine ⟨fun n h1 h2 => by rw [jacobi_eq_core]; exact h.1 n h1 h2,
          fun n h1 h2 => by rw [jacobi_eq_core]; exact h.2.1 n h1 h2,
          fun m n h1 h2 h3 h4 h5 => by rw [jacobi_eq_core, jacobi_eq_core]; exact h.2.2.1 m n h1 h2 h3 h4 h5,
          fun n a b h1 h2 => by rw [jacobi_eq_core, jacobi_eq_core, jacobi_eq_core]; exact h.2.2.2.1 n a b h1 h2,
          fun n a h1 h2 h3 => by rw [jacobi_eq_core]; exact h.2.2.2.2 n a h1 h2 h3⟩

theorem t1c_hkrs_apollonian_reciprocity_obstruction : T1c_HKRSApollonianReciprocityObstruction := by
  have h := ApollonianReciprocity.t1c_hkrs_apollonian_reciprocity_obstruction
  exact ⟨fun q hq => h.1 (toCoreQuad q) (inApollonianOrbit_toCore hq),
         fun q hq => h.2.1 (toCoreQuad q) (inApollonianOrbit_toCore hq),
         fun q hq => h.2.2.1 (toCoreQuad q) (inApollonianOrbit_toCore hq),
         h.2.2.2⟩

theorem t1d_octahedral_lorentzian_and_sqrt_neg2_obstruction : T1d_OctahedralLorentzianAndSqrtNeg2Obstruction := by
  have h := ApollonianReciprocity.t1d_octahedral_lorentzian_and_sqrt_neg2_obstruction
  refine ⟨fun s1 s2 s3 x => ?_, fun x hx => h.2.1 (toCoreOct x) hx, fun x hx => h.2.2.1 (toCoreOct x) (inOctOrbit_toCore hx), ?_⟩
  · have hx := h.1 s1 s2 s3 (toCoreOct x)
    constructor
    · apply toCoreOct_inj
      rw [toCoreOct_octRefl, toCoreOct_octRefl]
      exact hx.1
    · intro ho
      have h2 := hx.2 ho
      rw [← toCoreOct_octRefl] at h2
      exact h2
  · rcases h.2.2.2 with ⟨j1, j2, j3, j4, j5, hs1, hs2, hs3⟩
    exact ⟨by rw [jacobi_eq_core]; exact j1,
           by rw [jacobi_eq_core]; exact j2,
           by rw [jacobi_eq_core]; exact j3,
           by rw [jacobi_eq_core]; exact j4,
           by rw [jacobi_eq_core]; exact j5, hs1, hs2, hs3⟩

theorem t1e_soddy_dimension_dichotomy_and_3d_contrast : T1e_SoddyDimensionDichotomyAnd3DContrast := by
  have h := ApollonianReciprocity.t1e_soddy_dimension_dichotomy_and_3d_contrast
  refine ⟨fun d hd => ?_, fun d α k b => by rw [soddyRefl_eq_core, soddyRefl_eq_core]; exact h.2.1 d α k b, h.2.2.1, fun s => ?_, h.2.2.2.2⟩
  · have hiff := h.1 d hd
    constructor
    · rintro ⟨α, hα⟩
      refine hiff.mp ⟨α, fun b k => ?_⟩
      have := hα b k
      rw [soddyQ_eq_core, soddyRefl_eq_core, soddyQ_eq_core] at this
      exact this
    · intro h23
      rcases hiff.mpr h23 with ⟨α, hα⟩
      refine ⟨α, fun b k => ?_⟩
      rw [soddyQ_eq_core, soddyRefl_eq_core, soddyQ_eq_core]
      exact hα b k
  · have hs := h.2.2.2.1 (toCoreSoddy3 s)
    cases s with
    | mk b1 b2 b3 b4 b5 =>
      rcases hs with ⟨r1, r2, r3, r4, r5, q1, q2, q3, q4, q5⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, q1, q2, q3, q4, q5⟩
      · injection r1 with h1 h2 h3 h4 h5; simp only [soddy3Refl1]; congr
      · injection r2 with h1 h2 h3 h4 h5; simp only [soddy3Refl2]; congr
      · injection r3 with h1 h2 h3 h4 h5; simp only [soddy3Refl3]; congr
      · injection r4 with h1 h2 h3 h4 h5; simp only [soddy3Refl4]; congr
      · injection r5 with h1 h2 h3 h4 h5; simp only [soddy3Refl5]; congr

theorem t2a_abelian_sandpile_confluence_and_least_action : T2a_AbelianSandpileConfluenceAndLeastAction := by
  have h := SandpileTropical.t2a_abelian_sandpile_confluence_and_least_action
  refine ⟨fun G u v s => h.1 (toCoreGraph G) u v s,
          fun G L s w hL hw i => by
            rw [countFin_eq_core]
            exact h.2.1 (toCoreGraph G) L s w ((legalTrace_iff_core G L s).mp hL) (isStabilizingOdometer_toCore G s w hw) i,
          fun G s L1 L2 hL1 hs1 hL2 hs2 => ?_,
          fun G hdisp hsink s => ?_⟩
  · have hc := h.2.2.1 (toCoreGraph G) s L1 L2
      ((legalTrace_iff_core G L1 s).mp hL1) (by rw [← toppleList_eq_core]; exact hs1)
      ((legalTrace_iff_core G L2 s).mp hL2) (by rw [← toppleList_eq_core]; exact hs2)
    exact ⟨fun i => by rw [countFin_eq_core, countFin_eq_core]; exact hc.1 i,
           by rw [toppleList_eq_core, toppleList_eq_core]; exact hc.2⟩
  · have hsink' : SandpileTropical.HasReachableSink (toCoreGraph G) := fun i =>
      let ⟨d, hd⟩ := hsink i; ⟨d, reachesSink_toCore G hd⟩
    have ht := h.2.2.2 (toCoreGraph G) (isDissipative_toCore G hdisp) hsink' s
    exact ⟨let ⟨B, hB⟩ := ht.1; ⟨B, fun L hL => hB L ((legalTrace_iff_core G L s).mp hL)⟩,
           let ⟨L, hL, hs⟩ := ht.2; ⟨L, (legalTrace_iff_core G L s).mpr hL, by rw [toppleList_eq_core]; exact hs⟩⟩

theorem t2b_dhar_critical_identity_and_grid_orders : T2b_DharCriticalIdentityAndGridOrders := by
  have h := SandpileTropical.t2b_dhar_critical_identity_and_grid_orders
  rcases h with ⟨d1, d2, m1, m2, b1, g2, g3⟩
  rcases g2 with ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩
  rcases g3 with ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩
  refine ⟨d1, by rw [detMat_eq_core]; exact d2,
          fun i j => by rw [matMul9_eq_core]; exact m1 i j,
          fun i j => by rw [matMul9_eq_core, matMul9_eq_core]; exact m2 i j,
          b1, ?_, ?_⟩
  · exact ⟨(legalTrace_iff_core (gridGraph 2) _ _).mpr a1, by rw [toppleList_eq_core]; exact a2, a3,
           (legalTrace_iff_core (gridGraph 2) _ _).mpr a4, by rw [toppleList_eq_core]; exact a5, a6,
           (legalTrace_iff_core (gridGraph 2) _ _).mpr a7, by rw [toppleList_eq_core]; exact a8⟩
  · exact ⟨(legalTrace_iff_core (gridGraph 3) _ _).mpr c1, by rw [toppleList_eq_core]; exact c2, c3,
           (legalTrace_iff_core (gridGraph 3) _ _).mpr c4, by rw [toppleList_eq_core]; exact c5, c6,
           (legalTrace_iff_core (gridGraph 3) _ _).mpr c7, by rw [toppleList_eq_core]; exact c8⟩

theorem t2c_lps_z2_superharmonic_and_isotropic_obstruction : T2c_LPSZ2SuperharmonicAndIsotropicObstruction :=
  SandpileTropical.t2c_lps_z2_superharmonic_and_isotropic_obstruction

theorem t2d_triangular_a2_even_laplacian_rigidity_and_obstruction : T2d_TriangularA2EvenLaplacianRigidityAndObstruction :=
  SandpileTropical.t2d_triangular_a2_even_laplacian_rigidity_and_obstruction

theorem t2e_kalinin_shkolnikov_tropical_balancing_and_solitons : T2e_KalininShkolnikovTropicalBalancingAndSolitons := by
  have h := SandpileTropical.t2e_kalinin_shkolnikov_tropical_balancing_and_solitons
  refine ⟨fun vs => by rw [cycleNormals_eq_core, sumVec_eq_core]; exact h.1 vs,
          h.2.1, h.2.2.1,
          ⟨by rw [sumVec_eq_core]; exact h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩⟩

theorem t2f_a2_grid_orders_and_dhar_identity : T2f_A2GridOrdersAndDharIdentity := by
  have h := SandpileTropical.t2f_a2_grid_orders_and_dhar_identity
  rcases h with ⟨d1, d2, m1, m2, b1, g2, g3⟩
  rcases g2 with ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩
  rcases g3 with ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩
  refine ⟨d1, by rw [detMat_eq_core]; exact d2,
          fun i j => by rw [matMul9_eq_core]; exact m1 i j,
          fun i j => by rw [matMul9_eq_core, matMul9_eq_core]; exact m2 i j,
          b1, ?_, ?_⟩
  · exact ⟨(legalTrace_iff_core (a2GridGraph 2) _ _).mpr a1, by rw [toppleList_eq_core]; exact a2, a3,
           (legalTrace_iff_core (a2GridGraph 2) _ _).mpr a4, by rw [toppleList_eq_core]; exact a5, a6,
           (legalTrace_iff_core (a2GridGraph 2) _ _).mpr a7, by rw [toppleList_eq_core]; exact a8⟩
  · exact ⟨(legalTrace_iff_core (a2GridGraph 3) _ _).mpr c1, by rw [toppleList_eq_core]; exact c2, c3,
           (legalTrace_iff_core (a2GridGraph 3) _ _).mpr c4, by rw [toppleList_eq_core]; exact c5, c6,
           (legalTrace_iff_core (a2GridGraph 3) _ _).mpr c7, by rw [toppleList_eq_core]; exact c8⟩

theorem t3a_sl2z_fricke_cohn_markov_correspondence : T3a_SL2ZFrickeCohnMarkovCorrespondence := by
  have h := MarkovHurwitzCluster.t3a_sl2z_fricke_cohn_markov_correspondence
  exact ⟨fun A B hA hB => h.1 (toCoreMat2 A) (toCoreMat2 B) hA hB,
         fun A B hAB => h.2.1 (toCoreMat2 A) (toCoreMat2 B) (inCohnTree_toCore hAB),
         h.2.2⟩

theorem t3b_markov_coprimality_odd_primes_and_mod32 : T3b_MarkovCoprimalityOddPrimesAndMod32 := by
  have h := MarkovHurwitzCluster.t3b_markov_coprimality_odd_primes_and_mod32
  exact ⟨fun x y z hx hy hz heq => inMarkovTree_fromCore (h.1 x y z hx hy hz heq),
         fun x y z hm => h.2.1 x y z (inMarkovTree_toCore hm),
         h.2.2.1,
         h.2.2.2.1,
         h.2.2.2.2.1,
         ⟨inMarkovTree_fromCore h.2.2.2.2.2.1, inMarkovTree_fromCore h.2.2.2.2.2.2.1,
          h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩⟩

theorem t3c_hensel_sqrt_neg1_prime_power_uniqueness : T3c_HenselSqrtNeg1PrimePowerUniqueness :=
  MarkovHurwitzCluster.t3c_hensel_sqrt_neg1_prime_power_uniqueness

theorem t3d_cluster_algebra_markov_laurent_positivity : T3d_ClusterAlgebraMarkovLaurentPositivity :=
  MarkovHurwitzCluster.t3d_cluster_algebra_markov_laurent_positivity

theorem t3e_markov_hurwitz_n4_complete_classification : T3e_MarkovHurwitzN4CompleteClassification := by
  have h := MarkovHurwitzCluster.t3e_markov_hurwitz_n4_complete_classification
  exact ⟨h.1, h.2.1,
         fun x1 x2 x3 x4 =>
           ⟨fun hs => inHurwitz4Orbit_fromCore ((h.2.2.1 x1 x2 x3 x4).mp hs),
            fun ho => (h.2.2.1 x1 x2 x3 x4).mpr (inHurwitz4Orbit_toCore ho)⟩,
         fun x1 x2 x3 x4 =>
           ⟨fun hs => inHurwitz4Orbit_fromCore ((h.2.2.2.1 x1 x2 x3 x4).mp hs),
            fun ho => (h.2.2.2.1 x1 x2 x3 x4).mpr (inHurwitz4Orbit_toCore ho)⟩,
         h.2.2.2.2⟩

theorem prove_all_apollonian_sandpile_markov_theorems : AllApollonianSandpileMarkovTheorems :=
  ⟨t1a_descartes_lorentzian_and_gaussian_norm,
   t1b_jacobi_reciprocity_master,
   t1c_hkrs_apollonian_reciprocity_obstruction,
   t1d_octahedral_lorentzian_and_sqrt_neg2_obstruction,
   t1e_soddy_dimension_dichotomy_and_3d_contrast,
   t2a_abelian_sandpile_confluence_and_least_action,
   t2b_dhar_critical_identity_and_grid_orders,
   t2c_lps_z2_superharmonic_and_isotropic_obstruction,
   t2d_triangular_a2_even_laplacian_rigidity_and_obstruction,
   t2e_kalinin_shkolnikov_tropical_balancing_and_solitons,
   t2f_a2_grid_orders_and_dhar_identity,
   t3a_sl2z_fricke_cohn_markov_correspondence,
   t3b_markov_coprimality_odd_primes_and_mod32,
   t3c_hensel_sqrt_neg1_prime_power_uniqueness,
   t3d_cluster_algebra_markov_laurent_positivity,
   t3e_markov_hurwitz_n4_complete_classification⟩

end
end ApollonianSandpileMarkov.Palomar
