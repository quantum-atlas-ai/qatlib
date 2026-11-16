/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCornerFastChart
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelBernsteinBridge

@[expose] public section


/-!
# Actual coordinate mass for the scalar-corner certificate

The frozen nonorthonormal metric is a two-coordinate diagonal mask plus
the Gram of the actual fast input columns. Its quadratic pullback is
exactly the existing coordinateMass on every actual complex fast input.
No matrix inequality or normalization identity is assumed.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds
open Matrix
open scoped BigOperators ComplexOrder

open Qatlib.Concepts.GibbsSource.SourceForms

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCoordinateMetric

open ThreeLevelCluster ThreeLevelInvariant ThreeLevelWordDual
open ThreeLevelGramCertificate ThreeLevelGramCertificateCorner ThreeLevelCornerFastChart
open ThreeLevelBernstein

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
noncomputable section

/-- Quadratic add for the stated finite source data. -/
theorem quadratic_add {n : Type*} [Fintype n]
    (M N : Matrix n n ℂ) (z : n → ℂ) :
    quadratic (M+N) z = quadratic M z + quadratic N z := by
  simp [quadratic, Matrix.add_mulVec, dotProduct_add]

/-- Quadratic gram eq sum norm Sq for the stated finite source data. -/
theorem quadratic_gram_eq_sum_normSq {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) (z : n → ℂ) :
    quadratic (Aᴴ*A) z = ∑ k, Complex.normSq ((A *ᵥ z) k) := by
  unfold quadratic
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_conjTranspose, star_star]
  simp only [dotProduct, Complex.re_sum, Pi.star_apply, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

/-- Hs Square eq sum norm Sq for the stated finite source data. -/
theorem hsSquare_eq_sum_normSq (X : Operator 4) :
    hsSquare X = ∑ i, ∑ j, Complex.normSq (X i j) := by
  simp only [hsSquare, hsInner_eq_sum, Complex.re_sum, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

/-- Literal Combination add for the stated finite source data. -/
theorem literalCombination_add (z u : Fin 15 → ℂ) :
    literalCombination (z+u) = literalCombination z + literalCombination u := by
  simp only [literalCombination, Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- Literal Combination single for the stated finite source data. -/
theorem literalCombination_single (i : Fin 15) (c : ℂ) :
    literalCombination (Pi.single i c) = c • literalInput i := by
  simp [literalCombination, Pi.single_apply, ite_smul]

def fullCoordinates (c d : ℂ) (Y : Operator 4) : Fin 15 → ℂ :=
  Pi.single 0 c + Pi.single 1 d + fastCoordinates Y

/-- Full Coordinates zero for the stated finite source data. -/
theorem fullCoordinates_zero (c d : ℂ) (Y : Operator 4) :
    fullCoordinates c d Y 0 = c := by
  simp [fullCoordinates, fastCoordinates_first_zero]

/-- Full Coordinates one for the stated finite source data. -/
theorem fullCoordinates_one (c d : ℂ) (Y : Operator 4) :
    fullCoordinates c d Y 1 = d := by
  simp [fullCoordinates, fastCoordinates_second_zero]

/-- Literal Combination full Coordinates for the stated finite source data. -/
theorem literalCombination_fullCoordinates (σ : Perm) (c d : ℂ)
    (Y : Operator 4) (hY : IsFast σ Y) :
    literalCombination (fullCoordinates c d Y) =
      c • (pOne+pTwo) + d • pTwo + Y := by
  rw [fullCoordinates, literalCombination_add, literalCombination_add,
    literalCombination_single, literalCombination_single,
    literalInput_zero, literalInput_one, literalCombination_of_IsFast σ Y hY]

def flatInput : Matrix (Fin 16) (Fin 15) ℂ :=
  fromParts inputReal inputImag

def fastInput : Matrix (Fin 16) (Fin 15) ℂ :=
  fun i j => if j.val < 2 then 0 else flatInput i j

def populationMask : Fin 15 → ℂ := fun i => if i.val < 2 then 1 else 0

/-- Corner Metric eq masked Gram for the stated finite source data. -/
theorem cornerMetric_eq_maskedGram :
    cornerMetric = Matrix.diagonal populationMask + fastInputᴴ*fastInput := by
  ext i j : 2
  have hr := metric_parts_match_fast_basis.1 i j
  have hi := metric_parts_match_fast_basis.2 i j
  by_cases hsmalli : i.val < 2 <;> by_cases hsmallj : j.val < 2
  · by_cases hij : i = j
    · subst j
      have hle : i.val ≤ 1 := by omega
      apply Complex.ext <;>
        simp [cornerMetric, fromParts, hr, hi, hsmalli, hle, Matrix.diagonal,
          populationMask, Matrix.mul_apply, Matrix.conjTranspose_apply, fastInput]
    · apply Complex.ext <;>
        simp [cornerMetric, fromParts, hr, hi, hsmalli, hsmallj, hij, Matrix.diagonal,
          populationMask, Matrix.mul_apply, Matrix.conjTranspose_apply, fastInput]
  · have hij : i ≠ j := by intro h; subst j; contradiction
    apply Complex.ext <;>
      simp [cornerMetric, fromParts, hr, hi, hsmalli, hsmallj, hij, Matrix.diagonal,
        populationMask, Matrix.mul_apply, Matrix.conjTranspose_apply, fastInput]
  · have hij : i ≠ j := by intro h; subst j; contradiction
    apply Complex.ext <;>
      simp [cornerMetric, fromParts, hr, hi, hsmalli, hsmallj, hij, Matrix.diagonal,
        populationMask, Matrix.mul_apply, Matrix.conjTranspose_apply, fastInput]
  · have hle : ¬ i.val ≤ 1 := by omega
    apply Complex.ext <;>
      simp [cornerMetric, fromParts, hr, hi, hsmalli, hsmallj, hle, Matrix.diagonal,
        populationMask, Matrix.mul_apply, Matrix.conjTranspose_apply, fastInput,
        flatInput, Complex.mul_re, Complex.mul_im,
        Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring

/-- Fast Input mul Vec single zero for the stated finite source data. -/
theorem fastInput_mulVec_single_zero (c : ℂ) :
    fastInput *ᵥ Pi.single 0 c = 0 := by
  ext i
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, fastInput]

/-- Fast Input mul Vec single one for the stated finite source data. -/
theorem fastInput_mulVec_single_one (d : ℂ) :
    fastInput *ᵥ Pi.single 1 d = 0 := by
  ext i
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, fastInput]

/-- Fast Input mul Vec fast Coordinates for the stated finite source data. -/
theorem fastInput_mulVec_fastCoordinates (Y : Operator 4) :
    fastInput *ᵥ fastCoordinates Y = flatInput *ᵥ fastCoordinates Y := by
  ext i
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < 2
  · have hzero : fastCoordinates Y j = 0 := by
      have h : j = 0 ∨ j = 1 := by omega
      rcases h with rfl | rfl
      · exact fastCoordinates_first_zero Y
      · exact fastCoordinates_second_zero Y
    simp only [fastInput, ite_eq_left hj, hzero, mul_zero]
  · simp only [fastInput, ite_eq_right hj]

/-- Fast Input mul Vec full Coordinates for the stated finite source data. -/
theorem fastInput_mulVec_fullCoordinates (c d : ℂ) (Y : Operator 4) :
    fastInput *ᵥ fullCoordinates c d Y = flatInput *ᵥ fastCoordinates Y := by
  rw [fullCoordinates, Matrix.mulVec_add, Matrix.mulVec_add,
    fastInput_mulVec_single_zero, fastInput_mulVec_single_one, zero_add,
    zero_add, fastInput_mulVec_fastCoordinates]

/-- Flat Input mul Vec apply for the stated finite source data. -/
theorem flatInput_mulVec_apply (z : Fin 15 → ℂ) (i j : Fin 4) :
    (flatInput *ᵥ z) (flatIndex i j) = literalCombination z i j := by
  simp only [Matrix.mulVec, dotProduct, flatInput, fromParts, literalCombination,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, literalInput,
    inputMatrixReal, inputMatrixImag]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Sum flat Index for the stated finite source data. -/
theorem sum_flatIndex {α : Type*} [AddCommMonoid α] (f : Fin 16 → α) :
    (∑ k, f k) = ∑ i : Fin 4, ∑ j : Fin 4, f (flatIndex i j) := by
  have he (i j : Fin 4) :
      (finProdFinEquiv (i,j) : Fin 16) = flatIndex i j := by
    apply Fin.ext
    simp [finProdFinEquiv, flatIndex, Nat.add_comm]
  simpa only [Fintype.sum_prod_type, he] using
    (Equiv.sum_comp (finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16) f).symm

/-- Fast Input full Coordinates norm Sq for the stated finite source data. -/
theorem fastInput_fullCoordinates_normSq (σ : Perm) (c d : ℂ)
    (Y : Operator 4) (hY : IsFast σ Y) :
    (∑ k, Complex.normSq ((fastInput *ᵥ fullCoordinates c d Y) k)) =
      hsSquare Y := by
  rw [fastInput_mulVec_fullCoordinates, sum_flatIndex]
  simp only [flatInput_mulVec_apply, literalCombination_of_IsFast σ Y hY]
  exact (hsSquare_eq_sum_normSq Y).symm

/-- Population Mask quadratic for the stated finite source data. -/
theorem populationMask_quadratic (z : Fin 15 → ℂ) :
    quadratic (Matrix.diagonal populationMask) z =
      Complex.normSq (z 0) + Complex.normSq (z 1) := by
  simp [quadratic, Matrix.mulVec_diagonal, dotProduct, populationMask,
    Fin.sum_univ_succ, ← Complex.normSq_eq_conj_mul_self]

/-- Corner Metric full Coordinates quadratic for the stated finite source data. -/
theorem cornerMetric_fullCoordinates_quadratic (σ : Perm) (c d : ℂ)
    (Y : Operator 4) (hY : IsFast σ Y) :
    quadratic cornerMetric (fullCoordinates c d Y) = coordinateMass c d Y := by
  rw [cornerMetric_eq_maskedGram, quadratic_add, populationMask_quadratic,
    quadratic_gram_eq_sum_normSq, fastInput_fullCoordinates_normSq σ c d Y hY,
    fullCoordinates_zero, fullCoordinates_one]
  rfl


end
end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCoordinateMetric
