-- SPDX-License-Identifier: Apache-2.0
module

public import ApollonianSandpileMarkov.JacobiReciprocity
public import ApollonianSandpileMarkov.ApollonianReciprocity
public import ApollonianSandpileMarkov.SandpileTropical
public import ApollonianSandpileMarkov.MarkovHurwitzCluster

/-!
# Formal Statement Contract (`Challenge.lean`, v1.0.0)

Collects the exact formal statements of all 15 headline theorems (`T1a`–`T3e`) and their master
conjunction `AllApollonianSandpileMarkovTheorems`. Zero `sorry`, zero axioms.
-/

namespace ApollonianSandpileMarkov.Challenge

open ApollonianSandpileMarkov.JacobiReciprocity
open ApollonianSandpileMarkov.ApollonianReciprocity
open ApollonianSandpileMarkov.SandpileTropical
open ApollonianSandpileMarkov.MarkovHurwitzCluster

@[expose] public section

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
  (rootUnobstructed.descartes = 0 ∧ rootUnobstructed.a = 3 * 3)

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
  (∀ d : Nat, 2 ≤ d → ((d - 1) ∣ 2 ↔ d = 2 ∨ d = 3)) ∧
  (∀ s : Soddy3,
    soddy3Refl1 (soddy3Refl1 s) = s ∧ soddy3Refl2 (soddy3Refl2 s) = s ∧
    soddy3Refl3 (soddy3Refl3 s) = s ∧ soddy3Refl4 (soddy3Refl4 s) = s ∧
    soddy3Refl5 (soddy3Refl5 s) = s ∧
    soddy3Q (soddy3Refl1 s).b1 (soddy3Refl1 s).b2 (soddy3Refl1 s).b3 (soddy3Refl1 s).b4 (soddy3Refl1 s).b5 =
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
    (∀ i, countFin L1 i = countFin L2 i) ∧ toppleList G L1 s = toppleList G L2 s)

abbrev T2b_DharCriticalIdentityAndGridOrders : Prop :=
  det4 (gridLap 2) = 192 ∧
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

abbrev T3a_SL2ZFrickeCohnMarkovCorrespondence : Prop :=
  (∀ A B : Mat2, A.det = 1 → B.det = 1 →
    (A.tr) ^ 2 + (B.tr) ^ 2 + (Mat2.mul A B).tr ^ 2 =
    A.tr * B.tr * (Mat2.mul A B).tr + (Mat2.comm A B).tr + 2) ∧
  (∀ A B : Mat2, InCohnTree A B →
    A.det = 1 ∧ B.det = 1 ∧ (Mat2.comm A B).tr = -2 ∧
    (A.tr / 3) ^ 2 + (B.tr / 3) ^ 2 + ((Mat2.mul A B).tr / 3) ^ 2 =
    3 * (A.tr / 3) * (B.tr / 3) * ((Mat2.mul A B).tr / 3)) ∧
  (cohnA0.tr / 3 = 1 ∧ cohnB0.tr / 3 = 2 ∧ (Mat2.mul cohnA0 cohnB0).tr / 3 = 5)

abbrev T3b_MarkovCoprimalityOddPrimesAndMod32 : Prop :=
  (∀ x y z, InMarkovTree x y z →
    1 ≤ x ∧ 1 ≤ y ∧ 1 ≤ z ∧ x * x + y * y + z * z = 3 * x * y * z ∧
    Nat.Coprime x.natAbs y.natAbs ∧ Nat.Coprime y.natAbs z.natAbs ∧ Nat.Coprime z.natAbs x.natAbs) ∧
  (∀ x y z p, InMarkovTree x y z → IsPrime p → p % 2 = 1 → p ∣ x.natAbs → p % 4 = 1) ∧
  (∀ x y z, InMarkovTree x y z → x % 2 = 1 → x % 4 = 1) ∧
  (∀ x y z, InMarkovTree x y z → x % 2 = 0 → x % 32 = 2) ∧
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
  T3a_SL2ZFrickeCohnMarkovCorrespondence ∧
  T3b_MarkovCoprimalityOddPrimesAndMod32 ∧
  T3c_HenselSqrtNeg1PrimePowerUniqueness ∧
  T3d_ClusterAlgebraMarkovLaurentPositivity ∧
  T3e_MarkovHurwitzN4CompleteClassification

end

end ApollonianSandpileMarkov.Challenge
