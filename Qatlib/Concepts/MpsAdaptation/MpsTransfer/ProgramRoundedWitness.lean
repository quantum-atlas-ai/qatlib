/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpDuality.StrongDuality.SdpDuality
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Rational certificates for rounded SDP witnesses

`ProgramRoundedTable` stores Gaussian-rational SDP data and auxiliary witnesses, while
`programRoundedCertificate` checks exact finite conditions and returns residual and error data.
`toProgram` interprets the table as a real semidefinite program on Hermitian matrices.

`frontier1` transports successful checks to positivity, residual and norm bounds, a common
primal and dual optimal value with dual attainment, and quantitative objective estimates. For
the semidefinite-programming framework, see [Watrous2018].

## Main statements

* `checks_of_certificate`: Successful generation implies the checked rational and matrix
  conditions.
* `realConstraintMap_adjoint`: The adjoint is a linear combination of constraint matrices.
* `frontier1`: A successful certificate yields feasibility estimates, strong duality, dual
  attainment, and objective error bounds.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open Qatlib.Concepts.SdpDuality.StrongDuality

open Qatlib.Concepts.DyadicFloor.FloorRounding
open Qatlib.Concepts.DyadicFloor.FloorRounding.Program
open Qatlib.Concepts.SdpDuality.StrongDuality.Program

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer.ProgramRoundedWitness

open Qatlib.Concepts.DyadicFloor.FloorRounding Qatlib.Concepts.SdpDuality.StrongDuality
open scoped InnerProductSpace RealInnerProductSpace

section Rational

variable {n m : ℕ}

/-- The identity matrix over the Gaussian rationals. -/
def gaussianOne (n : ℕ) : Matrix (Fin n) (Fin n) GaussianRational :=
  Matrix.diagonal fun _ => 1

/-- The Gaussian-rational trace pairing `Matrix.trace (Q * W)`. -/
def rationalInner {I : Type*} [Fintype I] (Q W : Matrix I I GaussianRational) :
    GaussianRational := (Q * W).trace

/-- The complex Hermitian matrix obtained by embedding a Gaussian-rational matrix with a
supplied Hermitian proof. -/
def hermMat {I : Type*} [Fintype I] [DecidableEq I]
    (Q : Matrix I I GaussianRational) (hQ : Q.IsHermitian) : HermitianMat I ℂ :=
  ⟨gaussianRationalMatrix Q, (gaussianRationalMatrix_hermitian_iff Q).mpr hQ⟩

/-- The complex Hermitian embedding of a Gaussian-rational matrix when it is Hermitian, and zero
otherwise. -/
noncomputable def hermMatC {I : Type*} [Fintype I] [DecidableEq I]
    (Q : Matrix I I GaussianRational) : HermitianMat I ℂ :=
  if h : Q.IsHermitian then hermMat Q h else 0

/-- For a Hermitian Gaussian-rational matrix, the conditional embedding equals its
proof-carrying Hermitian embedding. -/
theorem hermMatC_eq {I : Type*} [Fintype I] [DecidableEq I]
    {Q : Matrix I I GaussianRational} (hQ : Q.IsHermitian) :
    hermMatC Q = hermMat Q hQ := by
  unfold hermMatC
  exact dif_pos hQ

/-- For a Hermitian Gaussian-rational matrix, the underlying matrix of the conditional embedding
is its entrywise complex embedding. -/
theorem hermMatC_mat {I : Type*} [Fintype I] [DecidableEq I]
    {Q : Matrix I I GaussianRational} (hQ : Q.IsHermitian) :
    (hermMatC Q).mat = gaussianRationalMatrix Q := by
  rw [hermMatC_eq hQ]; rfl

/-- Entrywise embedding of Gaussian-rational matrices into complex matrices preserves
multiplication. -/
theorem gaussianRationalMatrix_mul {I : Type*} [Fintype I] [DecidableEq I]
    (Q W : Matrix I I GaussianRational) :
    gaussianRationalMatrix (Q * W) =
      gaussianRationalMatrix Q * gaussianRationalMatrix W := by
  ext i j
  simp [gaussianRationalMatrix, Matrix.mul_apply, map_sum]

/-- The trace of an embedded Gaussian-rational matrix equals the embedding of its trace. -/
theorem gaussianRationalMatrix_trace {I : Type*} [Fintype I] [DecidableEq I]
    (Q : Matrix I I GaussianRational) :
    (gaussianRationalMatrix Q).trace = gaussianRationalEmbed Q.trace := by
  simp [gaussianRationalMatrix, Matrix.trace, Matrix.diag]

/-- The real inner product of two embedded Hermitian matrices equals the real part of their
Gaussian-rational trace pairing. -/
theorem rationalInner_real {I : Type*} [Fintype I] [DecidableEq I]
    {Q W : Matrix I I GaussianRational} (hQ : Q.IsHermitian) (hW : W.IsHermitian) :
    inner ℝ (hermMat Q hQ) (hermMat W hW) = ((rationalInner Q W).re : ℝ) := by
  show ((gaussianRationalMatrix Q * gaussianRationalMatrix W).trace.re : ℝ) = _
  rw [← gaussianRationalMatrix_mul,
    gaussianRationalMatrix_trace, gaussianRationalEmbed_re]
  rfl

end Rational

section Table

variable {n m : ℕ}

/-- Rational SDP data together with primal and dual candidates, a Slater candidate and margin,
correction matrices, trace and dual certificates, and error tolerances. -/
structure ProgramRoundedTable (n m : ℕ) where

  consA : Fin m → Matrix (Fin n) (Fin n) GaussianRational

  rhs : Fin m → ℚ

  objective : Matrix (Fin n) (Fin n) GaussianRational

  primal : Matrix (Fin n) (Fin n) GaussianRational

  dual : Fin m → ℚ

  slater : Matrix (Fin n) (Fin n) GaussianRational

  margin : ℚ

  dualExact : Fin m → ℚ

  traceCert : Fin m → ℚ

  corrBasis : Fin m → Matrix (Fin n) (Fin n) GaussianRational

  epsP : ℚ

  epsD : ℚ

/-- The Gaussian-rational linear combination of constraint matrices with the supplied rational
coefficients. -/
def tableDualCombo (t : ProgramRoundedTable n m) (y : Fin m → ℚ) :
    Matrix (Fin n) (Fin n) GaussianRational :=
  ∑ k, (y k : GaussianRational) • t.consA k

/-- The real part of the constraint-primal trace pairing minus the corresponding rational
right-hand side. -/
def tableResidual (t : ProgramRoundedTable n m) (k : Fin m) : ℚ :=
  (rationalInner (t.consA k) t.primal).re - t.rhs k

/-- The linear combination of correction-basis matrices weighted by the primal constraint
residuals. -/
def tableCorrection (t : ProgramRoundedTable n m) :
    Matrix (Fin n) (Fin n) GaussianRational :=
  ∑ k, (tableResidual t k : GaussianRational) • t.corrBasis k

/-- The rational primal matrix with its residual-based correction subtracted. -/
def tableCorrectedPrimal (t : ProgramRoundedTable n m) :
    Matrix (Fin n) (Fin n) GaussianRational :=
  t.primal - tableCorrection t

/-- The Gaussian-rational matrix norm bound computed from the table's primal matrix. -/
def tableNormBound (t : ProgramRoundedTable n m) : ℚ :=
  gaussianRationalNormBound t.primal

/-- The sum of absolute real objective pairings with the correction-basis matrices. -/
def tableGapCoeff (t : ProgramRoundedTable n m) : ℚ :=
  ∑ k, |(rationalInner t.objective (t.corrBasis k)).re|

/-- The rational pairing of the right-hand side with the trace-certificate coefficients. -/
def tableTraceBound (t : ProgramRoundedTable n m) : ℚ :=
  ∑ k, t.rhs k * t.traceCert k

/-- The residual vector, norm bound, objective-gap coefficient, trace bound, and error
tolerances returned by the rational certificate checker. -/
structure ProgramRoundedCertificate (m : ℕ) where

  residual : Fin m → ℚ

  normBound : ℚ

  gapCoeff : ℚ

  traceBound : ℚ

  epsP : ℚ

  epsD : ℚ

end Table

section Check

variable {n m : ℕ}

/-- The Boolean positive semidefiniteness check applied to the finite table of a
Gaussian-rational matrix. -/
def psdCheckTable (Q : Matrix (Fin n) (Fin n) GaussianRational) : Bool :=
  gaussianRationalPsdCheck (gaussianRationalTable Q)

/-- The Boolean conjunction of Hermitian, positivity, Slater, dual, trace, correction-basis, and
residual checks for a rounded SDP table. -/
def programRoundedCheckBool (t : ProgramRoundedTable n m) : Bool :=
  decide (∀ k : Fin m, (t.consA k).IsHermitian)
    && (decide (t.objective.IsHermitian)
    && (psdCheckTable t.primal
    && (psdCheckTable (tableCorrectedPrimal t)
    && (psdCheckTable (t.slater - (t.margin : GaussianRational) • gaussianOne n)
    && (decide (∀ k : Fin m,
          rationalInner (t.consA k) t.slater = ((t.rhs k : ℚ) : GaussianRational))
    && (psdCheckTable (tableDualCombo t t.dualExact - t.objective)
    && (psdCheckTable (tableDualCombo t t.traceCert - gaussianOne n)
    && (psdCheckTable (tableDualCombo t t.dual - t.objective
        + (t.epsD : GaussianRational) • gaussianOne n)
    && (decide (∀ j : Fin m, ∀ k : Fin m,
          rationalInner (t.consA j) (t.corrBasis k) = if j = k then 1 else 0)
    && (decide (0 < t.margin)
    && (decide (0 ≤ t.epsP)
    && (decide (0 ≤ t.epsD)
    && decide (∀ k : Fin m, |tableResidual t k| ≤ t.epsP)))))))))))))

/-- The computed rounded certificate when all table checks succeed, and `none` otherwise. -/
def programRoundedCertificate (t : ProgramRoundedTable n m) :
    Option (ProgramRoundedCertificate m) :=
  if programRoundedCheckBool t = true then
    some ⟨fun k => tableResidual t k, tableNormBound t, tableGapCoeff t,
      tableTraceBound t, t.epsP, t.epsD⟩
  else none

end Check

section Real

variable {n m : ℕ}

/-- The continuous real-linear constraint map whose coordinates are inner products with a finite
family of Hermitian matrices. -/
noncomputable def realConstraintMap (A : Fin m → HermitianMat (Fin n) ℂ) :
    HermitianMat (Fin n) ℂ →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  LinearMap.toContinuousLinearMap
    ((WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).symm.toLinearMap.comp
      (LinearMap.pi fun k => innerSL ℝ (A k)))

/-- Each coordinate of the real constraint map is the inner product with the corresponding
constraint matrix. -/
theorem realConstraintMap_apply (A : Fin m → HermitianMat (Fin n) ℂ)
    (X : HermitianMat (Fin n) ℂ) (k : Fin m) :
    (realConstraintMap A X).ofLp k = inner ℝ (A k) X := by
  simp [realConstraintMap, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.pi_apply, WithLp.linearEquiv_symm_apply]

/-- The adjoint of the real constraint map is the linear combination of its Hermitian constraint
matrices with the input coordinates. -/
theorem realConstraintMap_adjoint (A : Fin m → HermitianMat (Fin n) ℂ)
    (y : EuclideanSpace ℝ (Fin m)) :
    (realConstraintMap A).adjoint y = ∑ k, y.ofLp k • A k := by
  apply ext_inner_right ℝ
  intro X
  rw [ContinuousLinearMap.adjoint_inner_left, PiLp.inner_apply, sum_inner]
  simp only [real_inner_smul_left, RCLike.inner_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  show inner ℝ (A x) X * (starRingEnd ℝ) (y.ofLp x) = y.ofLp x * inner ℝ (A x) X
  simp
  ring

/-- A Euclidean vector whose coordinates agree with a function equals that function's
`WithLp.toLp` representation. -/
theorem eq_toLp_of_forall {v : Fin m → ℝ} {y : EuclideanSpace ℝ (Fin m)}
    (h : ∀ k, y.ofLp k = v k) : y = WithLp.toLp 2 v :=
  PiLp.ext h

/-- The real SDP encoded by a rounded rational table, using conditional Hermitian embeddings for
its constraint and objective matrices. -/
noncomputable def toProgram (t : ProgramRoundedTable n m) :
    Program (Fin n) (EuclideanSpace ℝ (Fin m)) where
  constraint := realConstraintMap fun k => hermMatC (t.consA k)
  rhs := WithLp.toLp 2 (fun k => (t.rhs k : ℝ))
  objective := hermMatC t.objective

/-- The constraint coordinates of the encoded program are the inner products with the
conditionally embedded table constraints. -/
theorem toProgram_constraint_apply (t : ProgramRoundedTable n m)
    (X : HermitianMat (Fin n) ℂ) (k : Fin m) :
    ((toProgram t).constraint X).ofLp k = inner ℝ (hermMatC (t.consA k)) X :=
  realConstraintMap_apply _ _ _

/-- The encoded program's constraint adjoint is the coordinate-weighted sum of its conditionally
embedded constraint matrices. -/
theorem toProgram_adjoint (t : ProgramRoundedTable n m)
    (y : EuclideanSpace ℝ (Fin m)) :
    (toProgram t).constraint.adjoint y = ∑ k, y.ofLp k • hermMatC (t.consA k) :=
  realConstraintMap_adjoint _ _

/-- The Euclidean real vector obtained by casting a finite rational dual vector coordinatewise. -/
def tableDualVec (y : Fin m → ℚ) :
    EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun k => (y k : ℝ))

end Real

section Transport

variable {n m : ℕ}

/-- Embedding a rational scalar through the Gaussian rationals agrees with its real-to-complex
cast. -/
theorem gaussianRationalEmbed_ratCast (q : ℚ) :
    gaussianRationalEmbed (q : GaussianRational) = ((q : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [gaussianRationalEmbed]

/-- Entrywise complex embedding of Gaussian-rational matrices preserves subtraction. -/
theorem gaussianRationalMatrix_sub {I : Type*} [Fintype I] [DecidableEq I]
    (Q W : Matrix I I GaussianRational) :
    gaussianRationalMatrix (Q - W) =
      gaussianRationalMatrix Q - gaussianRationalMatrix W := by
  ext i j; simp [gaussianRationalMatrix, map_sub]

/-- Entrywise complex embedding of Gaussian-rational matrices preserves addition. -/
theorem gaussianRationalMatrix_add {I : Type*} [Fintype I] [DecidableEq I]
    (Q W : Matrix I I GaussianRational) :
    gaussianRationalMatrix (Q + W) =
      gaussianRationalMatrix Q + gaussianRationalMatrix W := by
  ext i j; simp [gaussianRationalMatrix, map_add]

/-- Embedding a Gaussian-rational scalar multiple of a matrix equals the corresponding complex
scalar multiple of the embedded matrix. -/
theorem gaussianRationalMatrix_smul {I : Type*} [Fintype I] [DecidableEq I]
    (c : GaussianRational) (Q : Matrix I I GaussianRational) :
    gaussianRationalMatrix (c • Q) = gaussianRationalEmbed c • gaussianRationalMatrix Q := by
  ext i j; simp [gaussianRationalMatrix, smul_eq_mul]

/-- Entrywise complex embedding of Gaussian-rational matrices commutes with finite sums. -/
theorem gaussianRationalMatrix_sum {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (F : J → Matrix I I GaussianRational) :
    gaussianRationalMatrix (∑ k, F k) = ∑ k, gaussianRationalMatrix (F k) := by
  ext i j
  simp only [gaussianRationalMatrix, Matrix.map_apply]
  rw [Matrix.sum_apply i j Finset.univ F, Matrix.sum_apply i j Finset.univ
    (fun k => (F k).map ⇑gaussianRationalEmbed), map_sum]
  rfl

/-- The complex embedding of the Gaussian-rational identity matrix is the identity matrix. -/
theorem gaussianOne_matrix (n : ℕ) : gaussianRationalMatrix (gaussianOne n) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [gaussianOne, gaussianRationalMatrix]
  · simp [gaussianOne, gaussianRationalMatrix, h]

/-- The Gaussian-rational identity matrix is Hermitian. -/
theorem gaussianOne_isHermitian (n : ℕ) : (gaussianOne n).IsHermitian := by
  rw [gaussianOne, Matrix.diagonal_one]
  exact Matrix.isHermitian_one

/-- If subtracting a rational scalar identity from a Gaussian-rational matrix gives a Hermitian
matrix, then the original matrix is Hermitian. -/
theorem isHermitian_of_margin {Q : Matrix (Fin n) (Fin n) GaussianRational} {r : ℚ}
    (h : (Q - (r : GaussianRational) • gaussianOne n).IsHermitian) : Q.IsHermitian := by
  have h1 : (gaussianOne n).IsHermitian := gaussianOne_isHermitian n
  have h1' : star (gaussianOne n) = gaussianOne n := by
    rw [Matrix.star_eq_conjTranspose]; exact h1
  unfold Matrix.IsHermitian at h ⊢
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, star_ratCast,
    show (gaussianOne n).conjTranspose = gaussianOne n from h1] at h
  have h2 : Q.conjTranspose - (↑r : GaussianRational) • gaussianOne n
        + (↑r : GaussianRational) • gaussianOne n
      = Q - (↑r : GaussianRational) • gaussianOne n
        + (↑r : GaussianRational) • gaussianOne n := by rw [h]
  rw [sub_add_cancel, sub_add_cancel] at h2
  exact h2

/-- The real inner product of conditional Hermitian embeddings equals the real part of the
rational trace pairing when both inputs are Hermitian. -/
theorem rationalInner_real' {I : Type*} [Fintype I] [DecidableEq I]
    {Q W : Matrix I I GaussianRational} (hQ : Q.IsHermitian) (hW : W.IsHermitian) :
    inner ℝ (hermMatC Q) (hermMatC W) = ((rationalInner Q W).re : ℝ) := by
  rw [hermMatC_eq hQ, hermMatC_eq hW]
  exact rationalInner_real hQ hW

end Transport

section Main

open scoped ComplexOrder

variable {n m : ℕ}

/-- For a finite family of nonnegative real values, the sum of squares is at most the square of
the sum. -/
theorem sum_sq_le_sq_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h : ∀ i, 0 ≤ f i) :
    ∑ i ∈ s, f i ^ 2 ≤ (∑ i ∈ s, f i) ^ 2 := by
  calc ∑ i ∈ s, f i ^ 2 = ∑ i ∈ s, f i * f i := by
        refine Finset.sum_congr rfl fun i _ => by ring
    _ ≤ ∑ i ∈ s, f i * ∑ j ∈ s, f j := Finset.sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun i _ => h i) hi) (h i)
    _ = (∑ i ∈ s, f i) * (∑ j ∈ s, f j) :=
        (Finset.sum_mul s f (∑ j ∈ s, f j)).symm
    _ = (∑ i ∈ s, f i) ^ 2 := by ring_nf

set_option maxHeartbeats 800000 in

/-- The norm of a Hermitian Gaussian-rational matrix's complex embedding is bounded by its
computed Gaussian-rational norm bound. -/
theorem hermMat_norm_le (Q : Matrix (Fin n) (Fin n) GaussianRational) (hQ : Q.IsHermitian) :
    ‖hermMat Q hQ‖ ≤ (gaussianRationalNormBound Q : ℝ) := by
  have hB : 0 ≤ (gaussianRationalNormBound Q : ℝ) := by
    rw [gaussianRationalNormBound]
    simp only [Rat.cast_sum, Rat.cast_abs, Rat.cast_add]
    exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _)
  refine (sq_le_sq₀ (norm_nonneg _) hB).mp ?_
  rw [← real_inner_self_eq_norm_sq, inner_eq_real_trace]
  have hM : (hermMat Q hQ).mat = gaussianRationalMatrix Q := rfl
  have htrace : ((hermMat Q hQ).mat * (hermMat Q hQ).mat).trace
      = ∑ i, ∑ j, (gaussianRationalMatrix Q i j * gaussianRationalMatrix Q j i : ℂ) := by
    simp [Matrix.trace, Matrix.mul_apply, hM]
  have hresum : (∑ i, ∑ j, (gaussianRationalMatrix Q i j
        * gaussianRationalMatrix Q j i : ℂ)).re
      = ∑ i, ∑ j, ((gaussianRationalMatrix Q i j * gaussianRationalMatrix Q j i : ℂ)).re := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => Complex.re_sum _ _
  rw [htrace, hresum]
  have hterm : ∀ i j, ((gaussianRationalMatrix Q i j * gaussianRationalMatrix Q j i : ℂ)).re
      ≤ (|((Q i j).re : ℝ)| + |((Q i j).im : ℝ)|) ^ 2 := by
    intro i j
    have h2 := Matrix.IsHermitian.apply ((gaussianRationalMatrix_hermitian_iff Q).mpr hQ) i j
    have hconj : gaussianRationalMatrix Q j i
        = star (gaussianRationalMatrix Q i j) := by
      rw [← h2, star_star]
    have hval : (gaussianRationalMatrix Q i j * gaussianRationalMatrix Q j i).re
        = ((gaussianRationalMatrix Q i j).re ^ 2
          + (gaussianRationalMatrix Q i j).im ^ 2 : ℝ) := by
      rw [hconj, Complex.star_def, Complex.mul_conj, Complex.normSq_apply,
        Complex.ofReal_re]
      ring
    rw [hval]
    have heqre : ((gaussianRationalMatrix Q i j).re : ℝ) = ((Q i j).re : ℝ) := rfl
    have heqim : ((gaussianRationalMatrix Q i j).im : ℝ) = ((Q i j).im : ℝ) := rfl
    rw [heqre, heqim]
    have hcross : 0 ≤ |((Q i j).re : ℝ)| * |((Q i j).im : ℝ)| :=
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have h1 := sq_abs ((Q i j).re : ℝ)
    have h2' := sq_abs ((Q i j).im : ℝ)
    nlinarith [hcross, h1, h2']
  have hfinal : (gaussianRationalNormBound Q : ℝ)
      = ∑ i, ∑ j, (|((Q i j).re : ℝ)| + |((Q i j).im : ℝ)|) := by
    simp only [gaussianRationalNormBound, Rat.cast_sum, Rat.cast_abs, Rat.cast_add]
  calc (∑ i, ∑ j, ((gaussianRationalMatrix Q i j * gaussianRationalMatrix Q j i : ℂ)).re)
      ≤ ∑ i, ∑ j, (|((Q i j).re : ℝ)| + |((Q i j).im : ℝ)|) ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ ≤ (∑ i, ∑ j, (|((Q i j).re : ℝ)| + |((Q i j).im : ℝ)|)) ^ 2 := by
      have e1 := (Finset.sum_product (Finset.univ : Finset (Fin n))
        (Finset.univ : Finset (Fin n))
        (fun p : Fin n × Fin n =>
          (|((Q p.1 p.2).re : ℝ)| + |((Q p.1 p.2).im : ℝ)|) ^ 2)).symm
      have e2 := (Finset.sum_product (Finset.univ : Finset (Fin n))
        (Finset.univ : Finset (Fin n))
        (fun p : Fin n × Fin n =>
          (|((Q p.1 p.2).re : ℝ)| + |((Q p.1 p.2).im : ℝ)|))).symm
      rw [e1, e2]
      exact sum_sq_le_sq_sum _ _ fun _ => add_nonneg (abs_nonneg _) (abs_nonneg _)
    _ = (gaussianRationalNormBound Q : ℝ) ^ 2 := by rw [hfinal]

/-- A Hermitian Gaussian-rational matrix is positive definite after embedding if subtracting a
strictly positive rational identity margin leaves a positive semidefinite matrix. -/
theorem posDef_of_margin_psd {Q : Matrix (Fin n) (Fin n) GaussianRational} {r : ℚ}
    (hQ : Q.IsHermitian)
    (hpsd : (gaussianRationalMatrix (Q - (r : GaussianRational) • gaussianOne n)).PosSemidef)
    (hr : 0 < r) :
    (gaussianRationalMatrix Q).PosDef := by
  have h1 : gaussianRationalMatrix (Q - (r : GaussianRational) • gaussianOne n)
      + ((r : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)
      = gaussianRationalMatrix Q := by
    rw [gaussianRationalMatrix_sub, gaussianRationalMatrix_smul,
      gaussianRationalEmbed_ratCast, gaussianOne_matrix, sub_add_cancel]
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨(gaussianRationalMatrix_hermitian_iff Q).mpr hQ, ?_⟩
  intro x hx
  have hquad : 0 ≤ star x ⬝ᵥ
      ((gaussianRationalMatrix (Q - (r : GaussianRational) • gaussianOne n)).mulVec x) :=
    (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 x
  have hself : 0 < star x ⬝ᵥ x := Matrix.dotProduct_star_self_pos_iff.mpr hx
  have hpos : 0 < ((r : ℝ) : ℂ) * (star x ⬝ᵥ x) := by
    rw [Complex.pos_iff]
    simp only [Complex.mul_im, Complex.ofReal_im, zero_mul, add_zero]
    rw [Complex.pos_iff] at hself
    refine ⟨?_, ?_⟩
    · rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_pos (by exact_mod_cast hr) hself.1
    · rw [show ((r : ℝ) : ℂ).re = (r : ℝ) from Complex.ofReal_re _, ← hself.2, mul_zero]
  rw [← h1, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_add]
  rw [show star x ⬝ᵥ (((r : ℝ) : ℂ) • x) = ((r : ℝ) : ℂ) * (star x ⬝ᵥ x) by
    rw [dotProduct_smul, smul_eq_mul]]
  exact add_pos_of_nonneg_of_pos hquad hpos

/-- The rational trace pairing distributes over subtraction in its second argument. -/
theorem rationalInner_sub_right {I : Type*} [Fintype I] [DecidableEq I]
    (Q W1 W2 : Matrix I I GaussianRational) :
    rationalInner Q (W1 - W2) = rationalInner Q W1 - rationalInner Q W2 := by
  simp [rationalInner, Matrix.mul_sub]

/-- The rational trace pairing commutes with finite sums in its second argument. -/
theorem rationalInner_sum_right {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (Q : Matrix I I GaussianRational) (F : J → Matrix I I GaussianRational) :
    rationalInner Q (∑ k, F k) = ∑ k, rationalInner Q (F k) := by
  simp [rationalInner, Matrix.mul_sum]

/-- A Gaussian-rational scalar in the second argument of the trace pairing factors out
multiplicatively. -/
theorem rationalInner_smul {I : Type*} [Fintype I] [DecidableEq I]
    (c : GaussianRational) (Q W : Matrix I I GaussianRational) :
    rationalInner Q (c • W) = c * rationalInner Q W := by
  rw [rationalInner, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  rfl

/-- The real part of the rational trace pairing scales by a rational scalar applied to its
second argument. -/
theorem rationalInner_smul_re (q : ℚ) {I : Type*} [Fintype I] [DecidableEq I]
    (Q W : Matrix I I GaussianRational) :
    (rationalInner Q ((q : GaussianRational) • W)).re = q * (rationalInner Q W).re := by
  rw [rationalInner_smul, QuadraticAlgebra.re_mul]
  have h0 : ((q : GaussianRational).im) = 0 := QuadraticAlgebra.im_ratCast q
  have h1 : ((q : GaussianRational).re) = q := QuadraticAlgebra.algebraMap_re q
  rw [h0, h1, mul_zero, zero_mul, add_zero]

/-- The real part of the rational trace pairing with a finite sum equals the sum of the real
parts of the pairings. -/
theorem rationalInner_sum_re {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J]
    (Q : Matrix I I GaussianRational) (F : J → Matrix I I GaussianRational) :
    (rationalInner Q (∑ k, F k)).re = ∑ k, (rationalInner Q (F k)).re := by
  rw [rationalInner_sum_right]
  induction (Finset.univ : Finset J) using Finset.induction_on with
  | empty => simp
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk,
      QuadraticAlgebra.re_add, ih]

/-- Taking the underlying matrix of a finite sum of Hermitian matrices commutes with that sum. -/
theorem hermMat_sum_mat {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (f : J → HermitianMat I ℂ) :
    (∑ k, f k).mat = ∑ k, (f k).mat := by
  induction (Finset.univ : Finset J) using Finset.induction_on with
  | empty => simp
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, HermitianMat.mat_add, ih]

/-- For Hermitian table constraints, the underlying matrix of their real dual combination equals
the complex embedding of the rational dual combination. -/
theorem dualCombo_mat (t : ProgramRoundedTable n m) (y : Fin m → ℚ)
    (hA : ∀ k, (t.consA k).IsHermitian) :
    (∑ k, (y k : ℝ) • hermMatC (t.consA k)).mat = gaussianRationalMatrix (tableDualCombo t y) := by
  rw [hermMat_sum_mat, tableDualCombo, gaussianRationalMatrix_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [HermitianMat.mat_smul, hermMatC_mat (hA k)]
  ext i j
  simp [Matrix.smul_apply, Complex.real_smul, gaussianRationalMatrix,
    Matrix.map_apply, smul_eq_mul, map_mul]

/-- For Hermitian Gaussian-rational inputs, the underlying matrix of the difference of
conditional embeddings equals the embedding of their difference. -/
theorem hermMatC_sub_mat {I : Type*} [Fintype I] [DecidableEq I]
    {Q W : Matrix I I GaussianRational} (hQ : Q.IsHermitian) (hW : W.IsHermitian) :
    (hermMatC Q - hermMatC W).mat = gaussianRationalMatrix (Q - W) := by
  rw [HermitianMat.mat_sub, hermMatC_mat hQ, hermMatC_mat hW,
    gaussianRationalMatrix_sub]

/-- For a Hermitian Gaussian-rational matrix, adding a real rational scalar identity after
embedding agrees with embedding the rational identity shift. -/
theorem hermMatC_add_one_mat {n : ℕ} {Q : Matrix (Fin n) (Fin n) GaussianRational}
    (q : ℚ) (hQ : Q.IsHermitian) :
    (hermMatC Q + (q : ℝ) • (1 : HermitianMat (Fin n) ℂ)).mat
      = gaussianRationalMatrix (Q + (q : GaussianRational) • gaussianOne n) := by
  rw [HermitianMat.mat_add, HermitianMat.mat_smul, HermitianMat.mat_one,
    hermMatC_mat hQ,
    gaussianRationalMatrix_add, gaussianRationalMatrix_smul,
    gaussianRationalEmbed_ratCast, gaussianOne_matrix]
  ext i j
  by_cases h : i = j
  · subst h; simp [Matrix.smul_apply]
  · simp [h, Matrix.smul_apply]

/-- Successful certificate generation implies all checked algebraic, positivity, margin, and
residual conditions, and identifies every field of the returned certificate. -/
theorem checks_of_certificate {t : ProgramRoundedTable n m} {c : ProgramRoundedCertificate m}
    (h : programRoundedCertificate t = some c) :
    (∀ k : Fin m, (t.consA k).IsHermitian) ∧
    t.objective.IsHermitian ∧
    (gaussianRationalMatrix t.primal).PosSemidef ∧
    (gaussianRationalMatrix (tableCorrectedPrimal t)).PosSemidef ∧
    (gaussianRationalMatrix (t.slater - (t.margin : GaussianRational) • gaussianOne n)).PosSemidef ∧
    (∀ k : Fin m, rationalInner (t.consA k) t.slater = ((t.rhs k : ℚ) : GaussianRational)) ∧
    (gaussianRationalMatrix (tableDualCombo t t.dualExact - t.objective)).PosSemidef ∧
    (gaussianRationalMatrix (tableDualCombo t t.traceCert - gaussianOne n)).PosSemidef ∧
    (gaussianRationalMatrix (tableDualCombo t t.dual - t.objective
      + (t.epsD : GaussianRational) • gaussianOne n)).PosSemidef ∧
    (∀ j : Fin m, ∀ k : Fin m,
      rationalInner (t.consA j) (t.corrBasis k) = if j = k then 1 else 0) ∧
    0 < t.margin ∧ 0 ≤ t.epsP ∧ 0 ≤ t.epsD ∧
    (∀ k : Fin m, |tableResidual t k| ≤ t.epsP) ∧
    c = ⟨fun k => tableResidual t k, tableNormBound t, tableGapCoeff t,
      tableTraceBound t, t.epsP, t.epsD⟩ := by
  unfold programRoundedCertificate at h
  by_cases hb : programRoundedCheckBool t = true
  · rw [if_pos hb] at h
    injection h with h
    subst h
    simp only [programRoundedCheckBool, Bool.and_eq_true, decide_eq_true_eq, psdCheckTable,
      gaussianRationalPsdCheck_correct, gaussianRationalTableMatrix_table] at hb
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hb
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, rfl⟩
  · rw [if_neg hb] at h
    exact absurd h (by simp)

/-- The encoded program's dual score on a cast rational vector is the real cast of its rational
pairing with the table's right-hand side. -/
theorem dualScore_tableDualVec (t : ProgramRoundedTable n m) (y : Fin m → ℚ) :
    (toProgram t).dualScore (tableDualVec y) = ((∑ k, t.rhs k * y k : ℚ) : ℝ) := by
  simp only [Program.dualScore, toProgram, tableDualVec, PiLp.inner_apply,
    RCLike.inner_apply, starRingEnd_apply]
  simp
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The real inner product of the identity with a Hermitian matrix equals its trace. -/
theorem hermMat_inner_one {I : Type*} [Fintype I] [DecidableEq I]
    (X : HermitianMat I ℂ) : ⟪(1 : HermitianMat I ℂ), X⟫_ℝ = X.trace := by
  rw [inner_eq_real_trace]
  simp [HermitianMat.trace]

/-- For Hermitian table constraints, the matrix of the encoded constraint adjoint on a rational
dual vector is the embedded rational dual combination. -/
theorem adjoint_mat_dualCombo (t : ProgramRoundedTable n m) (y : Fin m → ℚ)
    (hA : ∀ k, (t.consA k).IsHermitian) :
    ((toProgram t).constraint.adjoint (tableDualVec y)).mat
      = gaussianRationalMatrix (tableDualCombo t y) := by
  rw [toProgram_adjoint, tableDualVec, WithLp.ofLp_toLp, dualCombo_mat t _ hA]

/-- A successful rounded certificate gives a positive semidefinite primal candidate with
certified coordinate residual and norm bounds, and a common primal and dual optimal value
attained on the dual side. It also bounds the candidate's primal overshoot and the supplied
dual vector's undershoot by the certificate's error products. -/
theorem frontier1 {n m : ℕ} (t : ProgramRoundedTable n m)
    {c : ProgramRoundedCertificate m}
    (h : programRoundedCertificate t = some c) :
    0 ≤ hermMatC t.primal ∧
    (∀ k : Fin m, |((toProgram t).constraint (hermMatC t.primal)).ofLp k
      - (t.rhs k : ℝ)| ≤ c.epsP) ∧
    ‖hermMatC t.primal‖ ≤ c.normBound ∧
    ∃ α : ℝ, IsLUB (toProgram t).primalValues α ∧ IsGLB (toProgram t).dualValues α ∧
      ∃ y, (toProgram t).DualFeasible y ∧ (toProgram t).dualScore y = α ∧
      (toProgram t).primalScore (hermMatC t.primal) - α ≤ c.epsP * c.gapCoeff ∧
      α - (toProgram t).dualScore (tableDualVec t.dual) ≤ c.epsD * c.traceBound := by
  obtain ⟨hA, hC, hPsP, hPsC, hPsS, hSF, hPsZ, hPsT, hPsY, hDB, hmP, heP, heD, hRB, hce⟩ :=
    checks_of_certificate h
  subst hce
  have hP' : t.primal.IsHermitian := (gaussianRationalMatrix_hermitian_iff _).mp hPsP.1
  have hC' : t.objective.IsHermitian := hC
  have hS' : t.slater.IsHermitian := isHermitian_of_margin
    ((gaussianRationalMatrix_hermitian_iff _).mp hPsS.1)
  have hCorr' : (tableCorrectedPrimal t).IsHermitian :=
    (gaussianRationalMatrix_hermitian_iff _).mp hPsC.1

  have hXpsd : 0 ≤ hermMatC t.primal := by
    rw [HermitianMat.zero_le_iff, hermMatC_mat hP']
    exact hPsP
  have hresbound : ∀ k : Fin m, |((toProgram t).constraint (hermMatC t.primal)).ofLp k
      - (t.rhs k : ℝ)| ≤ t.epsP := by
    intro k
    have h1 : ((toProgram t).constraint (hermMatC t.primal)).ofLp k
        = ((rationalInner (t.consA k) t.primal).re : ℝ) :=
      toProgram_constraint_apply t (hermMatC t.primal) k |>.trans
        (rationalInner_real' (hA k) hP')
    rw [h1]
    have h2 : (((rationalInner (t.consA k) t.primal).re : ℝ) - (t.rhs k : ℝ))
        = ((tableResidual t k : ℚ) : ℝ) := by
      simp only [tableResidual, Rat.cast_sub]
    rw [h2]
    push_cast
    exact_mod_cast hRB k
  have hnorm : ‖hermMatC t.primal‖ ≤ tableNormBound t := by
    rw [hermMatC_eq hP']
    exact hermMat_norm_le t.primal hP'

  have hSpsd : (gaussianRationalMatrix t.slater).PosDef :=
    posDef_of_margin_psd hS' hPsS hmP
  have hSlater : (toProgram t).PrimalSlater := by
    refine ⟨hermMatC t.slater, ?_, ?_⟩
    · rw [hermMatC_mat hS']; exact hSpsd
    · apply eq_toLp_of_forall
      intro k
      have h1 : ((toProgram t).constraint (hermMatC t.slater)).ofLp k
          = ((rationalInner (t.consA k) t.slater).re : ℝ) :=
        toProgram_constraint_apply t (hermMatC t.slater) k |>.trans
          (rationalInner_real' (hA k) hS')
      rw [h1, hSF k]
      rfl
  have hZ : (toProgram t).DualFeasible (tableDualVec t.dualExact) := by
    have hzmat : ((toProgram t).constraint.adjoint (tableDualVec t.dualExact)
        - (toProgram t).objective).mat
        = gaussianRationalMatrix (tableDualCombo t t.dualExact - t.objective) := by
      rw [toProgram_adjoint, tableDualVec, WithLp.ofLp_toLp, HermitianMat.mat_sub,
        dualCombo_mat t _ hA]
      show gaussianRationalMatrix (tableDualCombo t t.dualExact)
        - (hermMatC t.objective).mat = _
      rw [hermMatC_mat hC', gaussianRationalMatrix_sub]
    rw [Program.DualFeasible, HermitianMat.zero_le_iff, hzmat]
    exact hPsZ

  obtain ⟨α, hLUB, hGLB, hyAtt, hyScore⟩ :=
    Qatlib.Concepts.SdpDuality.StrongDuality.Program.primalSlater_strong_duality (toProgram t) hSlater hZ

  have hXhatFeas : (toProgram t).PrimalFeasible (hermMatC (tableCorrectedPrimal t)) := by
    refine ⟨by rw [HermitianMat.zero_le_iff, hermMatC_mat hCorr']; exact hPsC, ?_⟩
    apply eq_toLp_of_forall
    intro k
    have h1 : ((toProgram t).constraint (hermMatC (tableCorrectedPrimal t))).ofLp k
        = ((rationalInner (t.consA k) (tableCorrectedPrimal t)).re : ℝ) :=
      toProgram_constraint_apply t (hermMatC (tableCorrectedPrimal t)) k |>.trans
        (rationalInner_real' (hA k) hCorr')
    have h2 : (rationalInner (t.consA k) (tableCorrectedPrimal t)).re
        = (rationalInner (t.consA k) t.primal).re - (tableResidual t k : ℚ) := by
      rw [tableCorrectedPrimal, rationalInner_sub_right, QuadraticAlgebra.re_sub,
        tableCorrection, rationalInner_sum_re]
      have h3 : ∀ j : Fin m, (rationalInner (t.consA k)
          ((tableResidual t j : GaussianRational) • t.corrBasis j)).re
          = tableResidual t j * (if k = j then 1 else 0) := by
        intro j
        rw [rationalInner_smul_re (tableResidual t j), hDB k j]
        by_cases hkj : k = j
        · subst hkj; simp [QuadraticAlgebra.re_one]
        · simp [hkj]
      rw [Finset.sum_congr rfl (fun j _ => h3 j)]
      simp only [mul_ite, mul_zero, mul_one]
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_univ, if_true]
    rw [h1, h2]
    simp only [tableResidual]
    push_cast
    ring

  have heD' : (0 : ℝ) ≤ (t.epsD : ℝ) := by exact_mod_cast heD
  have hSm : ((toProgram t).constraint.adjoint (tableDualVec t.dual)
      - (toProgram t).objective
      + ((t.epsD : ℝ) • (1 : HermitianMat (Fin n) ℂ))).mat
      = gaussianRationalMatrix (tableDualCombo t t.dual - t.objective
        + (t.epsD : GaussianRational) • gaussianOne n) := by
    rw [HermitianMat.mat_add, HermitianMat.mat_sub, adjoint_mat_dualCombo t _ hA,
      HermitianMat.mat_smul, HermitianMat.mat_one]
    show gaussianRationalMatrix (tableDualCombo t t.dual)
        - (hermMatC t.objective).mat
        + (((t.epsD : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) = _
    rw [hermMatC_mat hC', gaussianRationalMatrix_add, gaussianRationalMatrix_sub,
      gaussianRationalMatrix_smul, gaussianRationalEmbed_ratCast, gaussianOne_matrix]
  have hTm : ((toProgram t).constraint.adjoint (tableDualVec t.traceCert)
      - (1 : HermitianMat (Fin n) ℂ)).mat
      = gaussianRationalMatrix (tableDualCombo t t.traceCert - gaussianOne n) := by
    rw [HermitianMat.mat_sub, adjoint_mat_dualCombo t _ hA, HermitianMat.mat_one,
      ← gaussianOne_matrix, gaussianRationalMatrix_sub]
  have hSpsd : 0 ≤ (toProgram t).constraint.adjoint (tableDualVec t.dual)
      - (toProgram t).objective
      + ((t.epsD : ℝ) • (1 : HermitianMat (Fin n) ℂ)) := by
    rw [HermitianMat.zero_le_iff, hSm]
    exact hPsY
  have hTpsd : 0 ≤ (toProgram t).constraint.adjoint (tableDualVec t.traceCert)
      - (1 : HermitianMat (Fin n) ℂ) := by
    rw [HermitianMat.zero_le_iff, hTm]
    exact hPsT

  have htraceBound : ∀ X : HermitianMat (Fin n) ℂ, (toProgram t).PrimalFeasible X →
      X.trace ≤ (tableTraceBound t : ℝ) := by
    intro X hX
    obtain ⟨hX0, hXb⟩ := hX
    have hkey : ⟪(toProgram t).constraint.adjoint (tableDualVec t.traceCert), X⟫_ℝ
        = ⟪tableDualVec t.traceCert, (toProgram t).rhs⟫_ℝ := by
      rw [ContinuousLinearMap.adjoint_inner_left]
      exact congrArg (inner ℝ (tableDualVec t.traceCert)) hXb
    have h1 := (HermitianMat.nonneg_iff_inner_nonneg _).mp hTpsd X hX0
    rw [inner_sub_left, hkey, hermMat_inner_one] at h1
    have hcomm : ⟪tableDualVec t.traceCert, (toProgram t).rhs⟫_ℝ
        = (toProgram t).dualScore (tableDualVec t.traceCert) :=
      (real_inner_comm _ _).trans rfl
    have hTB : ((∑ k, t.rhs k * t.traceCert k : ℚ) : ℝ)
        = (tableTraceBound t : ℝ) := rfl
    rw [hcomm, dualScore_tableDualVec, hTB] at h1
    exact sub_nonneg.mp h1

  have hgapUpper : α ≤ (toProgram t).dualScore (tableDualVec t.dual)
      + (t.epsD : ℝ) * (tableTraceBound t : ℝ) := by
    apply (isLUB_le_iff hLUB).mpr
    rw [mem_upperBounds]
    rintro r ⟨X, hX, rfl⟩
    obtain ⟨hX0, hXb⟩ := hX
    have hkey : ⟪(toProgram t).constraint.adjoint (tableDualVec t.dual), X⟫_ℝ
        = ⟪tableDualVec t.dual, (toProgram t).rhs⟫_ℝ := by
      rw [ContinuousLinearMap.adjoint_inner_left]
      exact congrArg (inner ℝ (tableDualVec t.dual)) hXb
    have h1 := (HermitianMat.nonneg_iff_inner_nonneg _).mp hSpsd X hX0
    rw [inner_add_left, inner_sub_left, real_inner_smul_left, hkey,
      hermMat_inner_one] at h1
    have hcomm : ⟪tableDualVec t.dual, (toProgram t).rhs⟫_ℝ
        = (toProgram t).dualScore (tableDualVec t.dual) :=
      (real_inner_comm _ _).trans rfl
    have hscore : ⟪(toProgram t).objective, X⟫_ℝ
        = (toProgram t).primalScore X := rfl
    rw [hcomm, hscore] at h1
    calc (toProgram t).primalScore X
        ≤ (toProgram t).dualScore (tableDualVec t.dual)
          + (t.epsD : ℝ) * X.trace := by linarith
      _ ≤ (toProgram t).dualScore (tableDualVec t.dual)
          + (t.epsD : ℝ) * (tableTraceBound t : ℝ) :=
        add_le_add_right (mul_le_mul_of_nonneg_left
          (htraceBound X ⟨hX0, hXb⟩) heD') _

  have hVmat : (hermMatC t.primal - hermMatC (tableCorrectedPrimal t)).mat
      = gaussianRationalMatrix (tableCorrection t) := by
    rw [hermMatC_sub_mat hP' hCorr', tableCorrectedPrimal, sub_sub_self]
  have hVinner' : inner ℝ (hermMatC t.objective)
      (hermMatC t.primal - hermMatC (tableCorrectedPrimal t))
      = ((rationalInner t.objective (tableCorrection t)).re : ℝ) := by
    rw [inner_eq_real_trace, hermMatC_mat hC', hVmat, ← gaussianRationalMatrix_mul,
      gaussianRationalMatrix_trace, gaussianRationalEmbed_re]
    rfl
  have hVinner2 : ((rationalInner t.objective (tableCorrection t)).re : ℝ)
      = ∑ k, ((tableResidual t k : ℚ)
        * (rationalInner t.objective (t.corrBasis k)).re : ℝ) := by
    have h1 : (rationalInner t.objective (tableCorrection t)).re
        = ∑ k, (rationalInner t.objective
          ((tableResidual t k : GaussianRational) • t.corrBasis k)).re := by
      rw [tableCorrection, rationalInner_sum_re]
    rw [h1, Rat.cast_sum]
    exact Finset.sum_congr rfl fun k _ => by
      exact_mod_cast rationalInner_smul_re (tableResidual t k) _ _
  have hCVbound : |inner ℝ (toProgram t).objective
      (hermMatC t.primal - hermMatC (tableCorrectedPrimal t))|
      ≤ (t.epsP : ℝ) * (tableGapCoeff t : ℝ) := by
    show |inner ℝ (hermMatC t.objective)
      (hermMatC t.primal - hermMatC (tableCorrectedPrimal t))| ≤ _
    rw [hVinner', hVinner2]
    have hstep : ∀ k : Fin m, |((tableResidual t k : ℚ)
        * (rationalInner t.objective (t.corrBasis k)).re : ℝ)|
        ≤ (t.epsP : ℝ) * |((rationalInner t.objective (t.corrBasis k)).re : ℝ)| := by
      intro k
      have hle : |((tableResidual t k : ℚ) : ℝ)| ≤ (t.epsP : ℝ) := by
        exact_mod_cast hRB k
      calc |((tableResidual t k : ℚ)
            * (rationalInner t.objective (t.corrBasis k)).re : ℝ)|
          = |((tableResidual t k : ℚ) : ℝ)|
            * |((rationalInner t.objective (t.corrBasis k)).re : ℝ)| :=
            abs_mul _ _
        _ ≤ (t.epsP : ℝ) * |((rationalInner t.objective (t.corrBasis k)).re : ℝ)| :=
            mul_le_mul_of_nonneg_right hle (abs_nonneg _)
    calc |∑ k, ((tableResidual t k : ℚ)
          * (rationalInner t.objective (t.corrBasis k)).re : ℝ)|
        ≤ ∑ k, |((tableResidual t k : ℚ)
          * (rationalInner t.objective (t.corrBasis k)).re : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, ((t.epsP : ℝ)
          * |((rationalInner t.objective (t.corrBasis k)).re : ℝ)|) :=
          Finset.sum_le_sum fun k _ => hstep k
      _ = (t.epsP : ℝ) * (tableGapCoeff t : ℝ) := by
          rw [← Finset.mul_sum, tableGapCoeff]
          simp only [Rat.cast_sum, Rat.cast_abs]
  have hgapLower : (toProgram t).primalScore (hermMatC t.primal) - α
      ≤ (t.epsP : ℝ) * (tableGapCoeff t : ℝ) := by
    have hXh : (toProgram t).primalScore (hermMatC (tableCorrectedPrimal t)) ≤ α :=
      (mem_upperBounds.mp hLUB.1) _
        ⟨hermMatC (tableCorrectedPrimal t), hXhatFeas, rfl⟩
    have hsplit : (toProgram t).primalScore (hermMatC t.primal)
        = (toProgram t).primalScore (hermMatC (tableCorrectedPrimal t))
          + inner ℝ (toProgram t).objective
            (hermMatC t.primal - hermMatC (tableCorrectedPrimal t)) := by
      show ⟪(toProgram t).objective, hermMatC t.primal⟫_ℝ
          = ⟪(toProgram t).objective, hermMatC (tableCorrectedPrimal t)⟫_ℝ
            + ⟪(toProgram t).objective,
              hermMatC t.primal - hermMatC (tableCorrectedPrimal t)⟫_ℝ
      conv_lhs =>
        rw [show hermMatC t.primal = hermMatC (tableCorrectedPrimal t)
            + (hermMatC t.primal - hermMatC (tableCorrectedPrimal t)) from by abel]
      rw [inner_add_right]
    rw [hsplit]
    have hCVle : inner ℝ (toProgram t).objective
        (hermMatC t.primal - hermMatC (tableCorrectedPrimal t))
        ≤ |inner ℝ (toProgram t).objective
          (hermMatC t.primal - hermMatC (tableCorrectedPrimal t))| :=
      le_abs_self _
    linarith
  refine ⟨hXpsd, hresbound, hnorm,
    ⟨α, hLUB, hGLB, hyAtt, hyScore.1, hyScore.2, hgapLower, ?_⟩⟩
  have hfinal : α - (toProgram t).dualScore (tableDualVec t.dual)
      ≤ (t.epsD : ℝ) * (tableTraceBound t : ℝ) := by linarith
  exact hfinal

end Main

end Qatlib.Concepts.MpsAdaptation.MpsTransfer.ProgramRoundedWitness
