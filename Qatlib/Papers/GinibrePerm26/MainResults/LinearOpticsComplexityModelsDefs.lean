/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BosonFock.PermAnalysis.GaussianComparison
import Mathlib.Analysis.Quaternion
import Mathlib.Data.Real.Star

/-!
# Gaussian permanent and cofactor comparison models

This module defines row-ordered permanents, dimension-normalized Gaussian matrix measures, and
the density and small-ball predicates for normalized permanents. It also specifies cofactor
vectors, gamma product measures, determinant benchmarks, and the Fourier and Laplace comparison
predicates `FourierCofactorCompression` and `GaussianCofactorInduction`. See [KoehlerLeung2026].

## Main statements

* `GaussianPermanentAnticoncentration`: The conjunction of the density and small-ball
  predicates, each with some positive constant uniform in the matrix size.
* `DetGammaBenchmark`: The conjunction of gamma-distribution identities for determinant cofactor
  vectors, their outer products and squared norms, and normalized squared determinants of
  Gaussian matrices.
* `GaussianCofactorInduction`: The conjunction of vector Laplace comparison, squared-norm
  Laplace comparison with a gamma product measure, and a real nonnegative Fourier comparison for
  the cofactor and gamma-scaled Gaussian measures.

## References

* [Koehler and Leung, 2026][KoehlerLeung2026]
-/

open Qatlib.Concepts.BosonFock.PermAnalysis

namespace Qatlib.Papers.GinibrePerm26.MainResults

set_option autoImplicit false

open scoped BigOperators ComplexOrder Quaternion RealInnerProductSpace InnerProductSpace
open MeasureTheory ProbabilityTheory

instance instMeasurableSpaceMatrix {S : Type*} [MeasurableSpace S] (m n : ℕ) :
    MeasurableSpace (Matrix (Fin m) (Fin n) S) :=
  show MeasurableSpace (Fin m → Fin n → S) from inferInstance

/-- The sum over column permutations of matrix-entry products taken in increasing row order,
allowing noncommutative multiplication. -/
noncomputable def rowOrderedPermanent {n : ℕ} (S : Type*) [AddCommMonoid S] [Monoid S]
    (M : Matrix (Fin n) (Fin n) S) : S :=
  ∑ σ : Equiv.Perm (Fin n), (List.ofFn (fun i : Fin n => M i (σ i))).prod

/-- The finite-rank value `Module.finrank ℝ S` used as the real dimension parameter. -/
noncomputable def dimR (S : Type*) [AddCommGroup S] [Module ℝ S] : ℕ :=
  Module.finrank ℝ S

/-- The pushforward of the standard real Gaussian measure on `S` by scaling with the reciprocal
square root of its real dimension. -/
noncomputable def kGaussianLaw (S : Type*) [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S] [Module ℝ S] : Measure S :=
  Measure.map (fun x : S => (Real.sqrt (Module.finrank ℝ S : ℝ))⁻¹ • x) (stdGaussian S)

/-- The measure on rectangular matrices whose entries are independently distributed according to
`kGaussianLaw S`. -/
noncomputable def gaussianMatrixLaw (S : Type*) [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S] [Module ℝ S]
    (m n : ℕ) : Measure (Matrix (Fin m) (Fin n) S) :=
  Measure.map (fun f : (Fin m × Fin n) → S => fun i j => f (i, j))
    (Measure.pi fun _ : Fin m × Fin n => kGaussianLaw S)

/-- The square-matrix specialization of `gaussianMatrixLaw S`. -/
noncomputable def ginibreLaw (S : Type*) [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S] [Module ℝ S] (n : ℕ) :
    Measure (Matrix (Fin n) (Fin n) S) :=
  gaussianMatrixLaw S n n

/-- The row-ordered permanent scaled by the reciprocal square root of `n!`. -/
noncomputable def normalizedPermanent (S : Type*) [NormedDivisionRing S] [Module ℝ S]
    (n : ℕ) (M : Matrix (Fin n) (Fin n) S) : S :=
  ((Real.sqrt (Nat.factorial n : ℝ)) : ℝ)⁻¹ • rowOrderedPermanent S M

/-- The pushforward of the square Gaussian matrix measure by the normalized permanent. -/
noncomputable def normalizedPermanentLaw (S : Type*) [NormedDivisionRing S]
    [NormedAlgebra ℝ S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
    [MeasurableSpace S] [BorelSpace S] (n : ℕ) : Measure S :=
  Measure.map (normalizedPermanent S n) (ginibreLaw S n)

/-- The measure `μ` equals Lebesgue measure weighted by `ENNReal.ofReal ∘ p`. -/
def HasLebesgueDensity (S : Type*) [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
    (μ : Measure S) (p : S → ℝ) : Prop :=
  μ = Measure.withDensity volume (fun x => ENNReal.ofReal (p x))

/-- The function depends only on the norm through a function antitone on nonnegative radii, and
its value at zero bounds all its values above. -/
def IsRadialNonincDensity (S : Type*) [Zero S] [Norm S] (p : S → ℝ) : Prop :=
  ∃ f : ℝ → ℝ, (∀ z : S, p z = f ‖z‖) ∧ AntitoneOn f (Set.Ici 0) ∧ (∀ z : S, p z ≤ p (0 : S))

/-- For every `n ≥ 1`, the normalized permanent measure has a radial nonincreasing Lebesgue
density whose value at zero is at most `C * n^((dimR S + 2)/4)`. -/
def Thm11Density (S : Type*) [NormedDivisionRing S] [NormedAlgebra ℝ S]
    [InnerProductSpace ℝ S] [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
    (C : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ p : S → ℝ,
    HasLebesgueDensity S (normalizedPermanentLaw S n) p ∧
    IsRadialNonincDensity S p ∧
    p 0 ≤ C * (n : ℝ) ^ (((Module.finrank ℝ S : ℝ) + 2) / 4)

/-- For every `n ≥ 1`, every positive radius, and every center, the normalized permanent measure
of the closed ball is bounded by `C * n^((dimR S + 2)/4)` times the radius to the real
dimension. -/
def Thm11SmallBall (S : Type*) [NormedDivisionRing S] [NormedAlgebra ℝ S]
    [InnerProductSpace ℝ S] [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
    (C : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 < ε → ∀ z : S,
    ((normalizedPermanentLaw S n) (Metric.closedBall z ε)).toReal ≤
      C * (n : ℝ) ^ (((Module.finrank ℝ S : ℝ) + 2) / 4) * ε ^ Module.finrank ℝ S

/-- The conjunction of the density and small-ball predicates, each with some positive constant
uniform in the matrix size. -/
def GaussianPermanentAnticoncentration (S : Type*) [NormedDivisionRing S] [NormedAlgebra ℝ S]
    [InnerProductSpace ℝ S] [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S] : Prop :=
  (∃ C : ℝ, 0 < C ∧ Thm11Density S C) ∧ (∃ C : ℝ, 0 < C ∧ Thm11SmallBall S C)

/-- The existence of a positive uniform constant bounding complex normalized-permanent
closed-ball masses by `C * n * t²` for `n ≥ 1` and `t > 0`. -/
def ComplexSmallBallCnT2 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, 0 < t → ∀ z : ℂ,
    ((normalizedPermanentLaw ℂ n) (Metric.closedBall z t)).toReal ≤ C * (n : ℝ) * t ^ 2

/-- The increasing index map from `Fin (n - 1)` to `Fin n` that skips column `j`. -/
def deleteColumn {n : ℕ} (j : Fin n) (i : Fin (n - 1)) : Fin n :=
  if h : i.val < j.val then ⟨i.val, by omega⟩ else ⟨i.val + 1, by omega⟩

/-- The row-ordered permanent of the square submatrix obtained by deleting column `j` from `B`. -/
noncomputable def perCofactor (S : Type*) [AddCommMonoid S] [Monoid S] {n : ℕ}
    (B : Matrix (Fin (n - 1)) (Fin n) S) (j : Fin n) : S :=
  rowOrderedPermanent S (fun i k => B i (deleteColumn j k))

/-- The vector of permanent cofactors indexed by the deleted column. -/
noncomputable def perCofactorColumn (S : Type*) [AddCommMonoid S] [Monoid S] {n : ℕ}
    (B : Matrix (Fin (n - 1)) (Fin n) S) : Fin n → S :=
  fun j => perCofactor S B j

/-- The pushforward of the `(n - 1)`-by-`n` Gaussian matrix measure by its permanent cofactor
vector. -/
noncomputable def cofactorColumnLaw (S : Type*) [NormedDivisionRing S] [NormedAlgebra ℝ S]
    [InnerProductSpace ℝ S] [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
    (n : ℕ) : Measure (Fin n → S) :=
  Measure.map (fun B : Matrix (Fin (n - 1)) (Fin n) S => perCofactorColumn S B)
    (gaussianMatrixLaw S (n - 1) n)

/-- The sum of the squared norms of a finite vector's coordinates. -/
noncomputable def vecNormSq (S : Type*) [Norm S] {n : ℕ} (x : Fin n → S) : ℝ :=
  ∑ j : Fin n, ‖x j‖ ^ 2

/-- The square root of `vecNormSq`. -/
noncomputable def vecNorm (S : Type*) [NormedDivisionRing S] {n : ℕ} (x : Fin n → S) : ℝ :=
  Real.sqrt (vecNormSq S x)

/-- The sum of the real inner products of corresponding vector coordinates. -/
noncomputable def vecInner (S : Type*) [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    {n : ℕ} (x y : Fin n → S) : ℝ :=
  ∑ j : Fin n, ⟪x j, y j⟫_ℝ

/-- The vector whose zeroth coordinate is the real scalar `r` embedded in `S`, with all other
coordinates zero. -/
noncomputable def unitFirst (S : Type*) [Semiring S] [Algebra ℝ S] (n : ℕ) (r : ℝ) : Fin n → S :=
  fun j => if j.val = 0 then algebraMap ℝ S r else 0

/-- The measure with density `x^(a - 1) * exp(-x/s) / (Γ(a) * s^a)` on positive `x` and zero
elsewhere, converted to nonnegative extended reals. -/
noncomputable def gammaMeasure (a s : ℝ) : Measure ℝ :=
  Measure.withDensity volume
    (fun x : ℝ => ENNReal.ofReal
      (if 0 < x then x ^ (a - 1) * Real.exp (-x / s) / (Real.Gamma a * s ^ a) else 0))

/-- For `m > 1`, the pushforward product of gamma measures with shapes `β*j/2` for `j = 2, …, m`
and scale `2/β`; for `m ≤ 1`, the Dirac measure at one. -/
noncomputable def gammaProductLaw (m β : ℕ) : Measure ℝ :=
  if m ≤ 1 then Measure.dirac (1 : ℝ)
  else
    Measure.map (fun g : Fin (m - 1) → ℝ => ∏ k : Fin (m - 1), g k)
      (Measure.pi fun k : Fin (m - 1) =>
        gammaMeasure (((β : ℝ) * (k.val + 2)) / 2) (2 / (β : ℝ)))

/-- The pushforward product of `n` gamma measures with shapes `β*j/2` for `j = 1, …, n` and
common scale `2/β`. -/
noncomputable def gammaFullProductLaw (n β : ℕ) : Measure ℝ :=
  Measure.map (fun g : Fin n → ℝ => ∏ k : Fin n, g k)
    (Measure.pi fun k : Fin n => gammaMeasure (((β : ℝ) * (k.val + 1)) / 2) (2 / (β : ℝ)))

/-- The product measure construction using gamma factors of shape `β*j/2` and scale `2/β`, with
the `j`th factor divided by `j`. -/
noncomputable def gammaRampLaw (n β : ℕ) : Measure ℝ :=
  Measure.map (fun g : Fin n → ℝ => ∏ k : Fin n, g k / ((k.val + 1 : ℕ) : ℝ))
    (Measure.pi fun k : Fin n => gammaMeasure (((β : ℝ) * (k.val + 1)) / 2) (2 / (β : ℝ)))

/-- The distribution obtained by scaling an independent vector of `kGaussianLaw S` coordinates
by the square root of a scalar drawn from `gammaProductLaw (m - 1) (dimR S)`. -/
noncomputable def gammaScaledGaussianColumnLaw (S : Type*) [NormedDivisionRing S]
    [NormedAlgebra ℝ S] [InnerProductSpace ℝ S] [FiniteDimensional ℝ S]
    [MeasurableSpace S] [BorelSpace S] (m : ℕ) : Measure (Fin m → S) :=
  Measure.map (fun p : ℝ × (Fin m → S) => (Real.sqrt p.1 : ℝ) • p.2)
    ((gammaProductLaw (m - 1) (dimR S)).prod (Measure.pi fun _ : Fin m => kGaussianLaw S))

/-- The matrix with entries `x i * star (x j)` associated to a vector `x`. -/
noncomputable def outerColumn (S : Type*) [Mul S] [Star S] {n : ℕ} (x : Fin n → S) :
    Matrix (Fin n) (Fin n) S :=
  fun i j => x i * star (x j)

/-- The determinant of the submatrix formed by deleting column `j`, multiplied by the
alternating sign `(-1)^j.val`. -/
noncomputable def detCofactor (S : Type*) [CommRing S] {n : ℕ}
    (B : Matrix (Fin (n - 1)) (Fin n) S) (j : Fin n) : S :=
  (-1) ^ j.val * Matrix.det (fun i k => B i (deleteColumn j k))

/-- The vector of signed determinant cofactors indexed by the deleted column. -/
noncomputable def detCofactorColumn (S : Type*) [CommRing S] {n : ℕ}
    (B : Matrix (Fin (n - 1)) (Fin n) S) : Fin n → S :=
  fun j => detCofactor S B j

/-- The conjunction of gamma-distribution identities for determinant cofactor vectors, their
outer products and squared norms, and normalized squared determinants of Gaussian matrices. -/
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

/-- The real four-by-four matrix representing left multiplication by the quaternion `q` in the
standard basis. -/
noncomputable def quaternionLeftMul (q : ℍ) : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![q.re, -q.imI, -q.imJ, -q.imK],
    ![q.imI, q.re, -q.imK, q.imJ],
    ![q.imJ, q.imK, q.re, -q.imI],
    ![q.imK, -q.imJ, q.imI, q.re]]

/-- The real matrix representing a quaternionic matrix by replacing each entry with its real
left-multiplication matrix using the specified product indexing. -/
noncomputable def quaternionRealify {n : ℕ} (A : Matrix (Fin n) (Fin n) ℍ) :
    Matrix (Fin (4 * n)) (Fin (4 * n)) ℝ :=
  fun u v =>
    quaternionLeftMul (A (finProdFinEquiv.symm u).2 (finProdFinEquiv.symm v).2)
      (finProdFinEquiv.symm u).1 (finProdFinEquiv.symm v).1

/-- The real square root of the determinant of the realification of a quaternionic matrix. -/
noncomputable def studyDetSq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℍ) : ℝ :=
  Real.sqrt (Matrix.det (quaternionRealify A))

/-- **Statement only — not proved in Qatlib.** The gamma product identities for `studyDetSq` of quaternionic Gaussian matrices and for its
factorial-normalized version, in positive dimensions. -/
def StudyGammaBenchmark : Prop :=
  (∀ n : ℕ, 1 ≤ n →
    Measure.map (fun G : Matrix (Fin n) (Fin n) ℍ => studyDetSq G) (ginibreLaw ℍ n)
      = gammaFullProductLaw n 4) ∧
  (∀ n : ℕ, 1 ≤ n →
    Measure.map (fun G : Matrix (Fin n) (Fin n) ℍ => studyDetSq G / (Nat.factorial n : ℝ))
      (ginibreLaw ℍ n)
      = gammaRampLaw n 4)

/-- The characteristic function of a vector measure using the real coordinate inner product in
the complex exponential. -/
noncomputable def vecCF (S : Type*) [NormedDivisionRing S] [InnerProductSpace ℝ S]
    [MeasurableSpace S] {n : ℕ} (μ : Measure (Fin n → S)) (z : Fin n → S) : ℂ :=
  ∫ x : Fin n → S, Complex.exp (Complex.I * ((vecInner S z x : ℝ) : ℂ)) ∂μ

/-- For every real linear map with nonnegative quadratic form, the integral of its negative
quadratic exponential under `μ` is at least that under `ν`. -/
def matrixLaplaceLEVec (S : Type*) [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    [MeasurableSpace S] {n : ℕ} (μ ν : Measure (Fin n → S)) : Prop :=
  ∀ Q : (Fin n → S) →ₗ[ℝ] (Fin n → S), (∀ x : Fin n → S, 0 ≤ vecInner S x (Q x)) →
    ∫ y : Fin n → S, Real.exp (-vecInner S y (Q y)) ∂μ ≥
      ∫ x : Fin n → S, Real.exp (-vecInner S x (Q x)) ∂ν

/-- The complex number has zero imaginary part and nonnegative real part. -/
def IsRealNonneg (w : ℂ) : Prop := w.im = 0 ∧ 0 ≤ w.re

/-- In dimensions at least two, the cofactor characteristic function is real and nonnegative
both at a vector and at its norm in the first coordinate, and the latter value bounds the
former above. -/
def FourierCofactorCompression (S : Type*) [NormedDivisionRing S] [NormedAlgebra ℝ S]
    [InnerProductSpace ℝ S] [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S] : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ z : Fin n → S,
    IsRealNonneg (vecCF S (cofactorColumnLaw S n) z) ∧
    IsRealNonneg (vecCF S (cofactorColumnLaw S n) (unitFirst S n (vecNorm S z))) ∧
    (vecCF S (cofactorColumnLaw S n) z).re ≤
      (vecCF S (cofactorColumnLaw S n) (unitFirst S n (vecNorm S z))).re

/-- The conjunction of vector Laplace comparison, squared-norm Laplace comparison with a gamma
product measure, and a real nonnegative Fourier comparison for the cofactor and gamma-scaled
Gaussian measures. -/
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
