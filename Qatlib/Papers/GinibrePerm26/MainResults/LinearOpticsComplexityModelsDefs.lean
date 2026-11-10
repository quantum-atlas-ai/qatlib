/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BosonFock.PermAnalysis.GaussianComparison
import Mathlib.Analysis.Quaternion
import Mathlib.Data.Real.Star

open Qatlib.Concepts.BosonFock.PermAnalysis

namespace Qatlib.Papers.GinibrePerm26.MainResults

set_option autoImplicit false

open scoped BigOperators ComplexOrder Quaternion RealInnerProductSpace InnerProductSpace
open MeasureTheory ProbabilityTheory

instance instMeasurableSpaceMatrix {S : Type*} [MeasurableSpace S] (m n : ℕ) :
    MeasurableSpace (Matrix (Fin m) (Fin n) S) :=
  show MeasurableSpace (Fin m → Fin n → S) from inferInstance

noncomputable def rowOrderedPermanent {n : ℕ} (S : Type*) [AddCommMonoid S] [Monoid S]
    (M : Matrix (Fin n) (Fin n) S) : S :=
  ∑ σ : Equiv.Perm (Fin n), (List.ofFn (fun i : Fin n => M i (σ i))).prod

noncomputable def dimR (S : Type*) [AddCommGroup S] [Module ℝ S] : ℕ :=
  Module.finrank ℝ S

noncomputable def kGaussianLaw (S : Type*) [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S] [Module ℝ S] : Measure S :=
  Measure.map (fun x : S => (Real.sqrt (Module.finrank ℝ S : ℝ))⁻¹ • x) (stdGaussian S)

noncomputable def gaussianMatrixLaw (S : Type*) [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S] [Module ℝ S]
    (m n : ℕ) : Measure (Matrix (Fin m) (Fin n) S) :=
  Measure.map (fun f : (Fin m × Fin n) → S => fun i j => f (i, j))
    (Measure.pi fun _ : Fin m × Fin n => kGaussianLaw S)

noncomputable def ginibreLaw (S : Type*) [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S] [Module ℝ S] (n : ℕ) :
    Measure (Matrix (Fin n) (Fin n) S) :=
  gaussianMatrixLaw S n n

noncomputable def normalizedPermanent (S : Type*) [NormedDivisionRing S] [Module ℝ S]
    (n : ℕ) (M : Matrix (Fin n) (Fin n) S) : S :=
  ((Real.sqrt (Nat.factorial n : ℝ)) : ℝ)⁻¹ • rowOrderedPermanent S M

noncomputable def normalizedPermanentLaw (S : Type*) [NormedDivisionRing S]
    [NormedAlgebra ℝ S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
    [MeasurableSpace S] [BorelSpace S] (n : ℕ) : Measure S :=
  Measure.map (normalizedPermanent S n) (ginibreLaw S n)

def HasLebesgueDensity (S : Type*) [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
    (μ : Measure S) (p : S → ℝ) : Prop :=
  μ = Measure.withDensity volume (fun x => ENNReal.ofReal (p x))

def IsRadialNonincDensity (S : Type*) [Zero S] [Norm S] (p : S → ℝ) : Prop :=
  ∃ f : ℝ → ℝ, (∀ z : S, p z = f ‖z‖) ∧ AntitoneOn f (Set.Ici 0) ∧ (∀ z : S, p z ≤ p (0 : S))

def Thm11Density (S : Type*) [NormedDivisionRing S] [NormedAlgebra ℝ S]
    [InnerProductSpace ℝ S] [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
    (C : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ p : S → ℝ,
    HasLebesgueDensity S (normalizedPermanentLaw S n) p ∧
    IsRadialNonincDensity S p ∧
    p 0 ≤ C * (n : ℝ) ^ (((Module.finrank ℝ S : ℝ) + 2) / 4)

def Thm11SmallBall (S : Type*) [NormedDivisionRing S] [NormedAlgebra ℝ S]
    [InnerProductSpace ℝ S] [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
    (C : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 < ε → ∀ z : S,
    ((normalizedPermanentLaw S n) (Metric.closedBall z ε)).toReal ≤
      C * (n : ℝ) ^ (((Module.finrank ℝ S : ℝ) + 2) / 4) * ε ^ Module.finrank ℝ S

def GaussianPermanentAnticoncentration (S : Type*) [NormedDivisionRing S] [NormedAlgebra ℝ S]
    [InnerProductSpace ℝ S] [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S] : Prop :=
  (∃ C : ℝ, 0 < C ∧ Thm11Density S C) ∧ (∃ C : ℝ, 0 < C ∧ Thm11SmallBall S C)

def ComplexSmallBallCnT2 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, 0 < t → ∀ z : ℂ,
    ((normalizedPermanentLaw ℂ n) (Metric.closedBall z t)).toReal ≤ C * (n : ℝ) * t ^ 2

def deleteColumn {n : ℕ} (j : Fin n) (i : Fin (n - 1)) : Fin n :=
  if h : i.val < j.val then ⟨i.val, by omega⟩ else ⟨i.val + 1, by omega⟩

noncomputable def perCofactor (S : Type*) [AddCommMonoid S] [Monoid S] {n : ℕ}
    (B : Matrix (Fin (n - 1)) (Fin n) S) (j : Fin n) : S :=
  rowOrderedPermanent S (fun i k => B i (deleteColumn j k))

noncomputable def perCofactorColumn (S : Type*) [AddCommMonoid S] [Monoid S] {n : ℕ}
    (B : Matrix (Fin (n - 1)) (Fin n) S) : Fin n → S :=
  fun j => perCofactor S B j

noncomputable def cofactorColumnLaw (S : Type*) [NormedDivisionRing S] [NormedAlgebra ℝ S]
    [InnerProductSpace ℝ S] [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
    (n : ℕ) : Measure (Fin n → S) :=
  Measure.map (fun B : Matrix (Fin (n - 1)) (Fin n) S => perCofactorColumn S B)
    (gaussianMatrixLaw S (n - 1) n)

noncomputable def vecNormSq (S : Type*) [Norm S] {n : ℕ} (x : Fin n → S) : ℝ :=
  ∑ j : Fin n, ‖x j‖ ^ 2

noncomputable def vecNorm (S : Type*) [NormedDivisionRing S] {n : ℕ} (x : Fin n → S) : ℝ :=
  Real.sqrt (vecNormSq S x)

noncomputable def vecInner (S : Type*) [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    {n : ℕ} (x y : Fin n → S) : ℝ :=
  ∑ j : Fin n, ⟪x j, y j⟫_ℝ

noncomputable def unitFirst (S : Type*) [Semiring S] [Algebra ℝ S] (n : ℕ) (r : ℝ) : Fin n → S :=
  fun j => if j.val = 0 then algebraMap ℝ S r else 0

noncomputable def gammaMeasure (a s : ℝ) : Measure ℝ :=
  Measure.withDensity volume
    (fun x : ℝ => ENNReal.ofReal
      (if 0 < x then x ^ (a - 1) * Real.exp (-x / s) / (Real.Gamma a * s ^ a) else 0))

noncomputable def gammaProductLaw (m β : ℕ) : Measure ℝ :=
  if m ≤ 1 then Measure.dirac (1 : ℝ)
  else
    Measure.map (fun g : Fin (m - 1) → ℝ => ∏ k : Fin (m - 1), g k)
      (Measure.pi fun k : Fin (m - 1) =>
        gammaMeasure (((β : ℝ) * (k.val + 2)) / 2) (2 / (β : ℝ)))

noncomputable def gammaFullProductLaw (n β : ℕ) : Measure ℝ :=
  Measure.map (fun g : Fin n → ℝ => ∏ k : Fin n, g k)
    (Measure.pi fun k : Fin n => gammaMeasure (((β : ℝ) * (k.val + 1)) / 2) (2 / (β : ℝ)))

noncomputable def gammaRampLaw (n β : ℕ) : Measure ℝ :=
  Measure.map (fun g : Fin n → ℝ => ∏ k : Fin n, g k / ((k.val + 1 : ℕ) : ℝ))
    (Measure.pi fun k : Fin n => gammaMeasure (((β : ℝ) * (k.val + 1)) / 2) (2 / (β : ℝ)))

noncomputable def gammaScaledGaussianColumnLaw (S : Type*) [NormedDivisionRing S]
    [NormedAlgebra ℝ S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
    [MeasurableSpace S] [BorelSpace S] (m : ℕ) : Measure (Fin m → S) :=
  Measure.map (fun p : ℝ × (Fin m → S) => (Real.sqrt p.1 : ℝ) • p.2)
    ((gammaProductLaw (m - 1) (dimR S)).prod (Measure.pi fun _ : Fin m => kGaussianLaw S))

noncomputable def outerColumn (S : Type*) [Mul S] [Star S] {n : ℕ} (x : Fin n → S) :
    Matrix (Fin n) (Fin n) S :=
  fun i j => x i * star (x j)

noncomputable def detCofactor (S : Type*) [CommRing S] {n : ℕ}
    (B : Matrix (Fin (n - 1)) (Fin n) S) (j : Fin n) : S :=
  (-1) ^ j.val * Matrix.det (fun i k => B i (deleteColumn j k))

noncomputable def detCofactorColumn (S : Type*) [CommRing S] {n : ℕ}
    (B : Matrix (Fin (n - 1)) (Fin n) S) : Fin n → S :=
  fun j => detCofactor S B j

def DetGammaBenchmark (S : Type*) [NormedField S] [NormedAlgebra ℝ S]
    [InnerProductSpace ℝ S] [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
    [StarRing S] : Prop :=
  (∀ n : ℕ, 2 ≤ n →
    Measure.map (fun B : Matrix (Fin (n - 1)) (Fin n) S => detCofactorColumn S B)
      (gaussianMatrixLaw S (n - 1) n)
      = gammaScaledGaussianColumnLaw S n) ∧
  (∀ n : ℕ, 2 ≤ n →
    Measure.map (fun B : Matrix (Fin (n - 1)) (Fin n) S => outerColumn S (detCofactorColumn S B))
      (gaussianMatrixLaw S (n - 1) n)
      = Measure.map
          (fun p : ℝ × (Fin n → S) => fun i j => algebraMap ℝ S p.1 * p.2 i * star (p.2 j))
          ((gammaProductLaw (n - 1) (dimR S)).prod (Measure.pi fun _ : Fin n => kGaussianLaw S))) ∧
  (∀ n : ℕ, 1 ≤ n →
    Measure.map (fun B : Matrix (Fin (n - 1)) (Fin n) S => vecNormSq S (detCofactorColumn S B))
      (gaussianMatrixLaw S (n - 1) n)
      = gammaProductLaw n (dimR S)) ∧
  (∀ n : ℕ, 1 ≤ n →
    Measure.map
      (fun G : Matrix (Fin n) (Fin n) S => ‖Matrix.det G‖ ^ 2 / (Nat.factorial n : ℝ))
      (ginibreLaw S n)
      = gammaRampLaw n (dimR S))

noncomputable instance instMeasurableSpaceQuaternion : MeasurableSpace ℍ := borel ℍ

noncomputable instance instBorelSpaceQuaternion : BorelSpace ℍ := ⟨rfl⟩

noncomputable def quaternionLeftMul (q : ℍ) : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![q.re, -q.imI, -q.imJ, -q.imK],
    ![q.imI, q.re, -q.imK, q.imJ],
    ![q.imJ, q.imK, q.re, -q.imI],
    ![q.imK, -q.imJ, q.imI, q.re]]

noncomputable def quaternionRealify {n : ℕ} (A : Matrix (Fin n) (Fin n) ℍ) :
    Matrix (Fin (4 * n)) (Fin (4 * n)) ℝ :=
  fun u v =>
    quaternionLeftMul (A (finProdFinEquiv.symm u).2 (finProdFinEquiv.symm v).2)
      (finProdFinEquiv.symm u).1 (finProdFinEquiv.symm v).1

noncomputable def studyDetSq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℍ) : ℝ :=
  Real.sqrt (Matrix.det (quaternionRealify A))

def StudyGammaBenchmark : Prop :=
  (∀ n : ℕ, 1 ≤ n →
    Measure.map (fun G : Matrix (Fin n) (Fin n) ℍ => studyDetSq G) (ginibreLaw ℍ n)
      = gammaFullProductLaw n 4) ∧
  (∀ n : ℕ, 1 ≤ n →
    Measure.map (fun G : Matrix (Fin n) (Fin n) ℍ => studyDetSq G / (Nat.factorial n : ℝ))
      (ginibreLaw ℍ n)
      = gammaRampLaw n 4)

noncomputable def vecCF (S : Type*) [NormedDivisionRing S] [InnerProductSpace ℝ S]
    [MeasurableSpace S] {n : ℕ} (μ : Measure (Fin n → S)) (z : Fin n → S) : ℂ :=
  ∫ x : Fin n → S, Complex.exp (Complex.I * ((vecInner S z x : ℝ) : ℂ)) ∂μ

def matrixLaplaceLEVec (S : Type*) [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    [MeasurableSpace S] {n : ℕ} (μ ν : Measure (Fin n → S)) : Prop :=
  ∀ Q : (Fin n → S) →ₗ[ℝ] (Fin n → S), (∀ x : Fin n → S, 0 ≤ vecInner S x (Q x)) →
    ∫ y : Fin n → S, Real.exp (-vecInner S y (Q y)) ∂μ ≥
      ∫ x : Fin n → S, Real.exp (-vecInner S x (Q x)) ∂ν

def IsRealNonneg (w : ℂ) : Prop := w.im = 0 ∧ 0 ≤ w.re

def FourierCofactorCompression (S : Type*) [NormedDivisionRing S] [NormedAlgebra ℝ S]
    [InnerProductSpace ℝ S] [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S] : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ z : Fin n → S,
    IsRealNonneg (vecCF S (cofactorColumnLaw S n) z) ∧
    IsRealNonneg (vecCF S (cofactorColumnLaw S n) (unitFirst S n (vecNorm S z))) ∧
    (vecCF S (cofactorColumnLaw S n) z).re ≤
      (vecCF S (cofactorColumnLaw S n) (unitFirst S n (vecNorm S z))).re

def GaussianCofactorInduction (S : Type*) [NormedDivisionRing S] [NormedAlgebra ℝ S]
    [InnerProductSpace ℝ S] [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S] : Prop :=
  (∀ n : ℕ, 1 ≤ n →
    matrixLaplaceLEVec S (gammaScaledGaussianColumnLaw S n) (cofactorColumnLaw S n)) ∧
  (∀ n : ℕ, 1 ≤ n →
    Qatlib.Concepts.BosonFock.PermAnalysis.laplaceLE (gammaProductLaw n (dimR S))
      (Measure.map (fun x : Fin n → S => vecNormSq S x) (cofactorColumnLaw S n))) ∧
  (∀ n : ℕ, 1 ≤ n → ∀ z : Fin (n + 1) → S,
    IsRealNonneg (vecCF S (cofactorColumnLaw S (n + 1)) z) ∧
    IsRealNonneg (vecCF S (gammaScaledGaussianColumnLaw S (n + 1)) z) ∧
    (vecCF S (cofactorColumnLaw S (n + 1)) z).re ≤
      (vecCF S (gammaScaledGaussianColumnLaw S (n + 1)) z).re)

end Qatlib.Papers.GinibrePerm26.MainResults
