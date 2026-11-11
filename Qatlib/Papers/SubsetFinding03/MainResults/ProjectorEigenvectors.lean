/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

/-!
# Two-level eigenvectors for subset finding

This module analyzes the explicit two-dimensional matrix `twoLevelUP` associated with the
overlap scale `twoLevelOverlap` in [ChildsEisenberg2003]. It gives exact eigenvectors and
eigenvalues, expresses the eigenvalues through `twoLevelPhase`, and bounds the residuals of the
paper's comparison vectors.

The estimates are quantitative for `0 ≤ c ≤ 1 / 2`: the phase differs from `2c` by at most
`2c³`, and each comparison-vector residual coordinate has norm at most `4c²`.

## Main statements

* `twoLevelUP_eigenvector_plus` and `twoLevelUP_eigenvector_minus`: exact eigenvector
  identities.
* `twoLevelPhase_approx`: the cubic phase-error bound.
* `paper_vector_residual_plus` and `paper_vector_residual_minus`: coordinatewise residual
  bounds.
* `lemma3_two_level`: collects the two-level identities and estimates.

## References

* [Childs and Eisenberg, 2003][ChildsEisenberg2003]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SubsetFinding03.MainResults.ProjectorEigenvectors

open Complex
open scoped Matrix

/-- The real overlap scale `(M / N) ^ (L / 2)`. -/
def twoLevelOverlap (M N L : ℕ) : ℝ := ((M : ℝ) / (N : ℝ)) ^ ((L : ℝ) / 2)

/-- The quantity `√(1 - c ^ 2)` used in the two-level rotation. -/
def twoLevelSin (c : ℝ) : ℝ := Real.sqrt (1 - c ^ 2)

/-- The diagonal coefficient `1 - 2 * c ^ 2` of the two-level matrix. -/
def twoLevelDiag (c : ℝ) : ℝ := 1 - 2 * c ^ 2

/-- The off-diagonal magnitude `2 * c * √(1 - c ^ 2)` of the two-level matrix. -/
def twoLevelOffDiag (c : ℝ) : ℝ := 2 * c * twoLevelSin c

/-- The phase `2 * arcsin c` associated with the two-level matrix. -/
def twoLevelPhase (c : ℝ) : ℝ := 2 * Real.arcsin c

/-- The complex two-by-two matrix with diagonal `twoLevelDiag c` and signed off-diagonal entries
`twoLevelOffDiag c`. -/
def twoLevelUP (c : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(twoLevelDiag c : ℂ), -(twoLevelOffDiag c : ℂ);
     (twoLevelOffDiag c : ℂ), (twoLevelDiag c : ℂ)]

/-- The candidate eigenvalue `twoLevelDiag c + i * twoLevelOffDiag c`. -/
def twoLevelEigPlus (c : ℝ) : ℂ :=
  (twoLevelDiag c : ℂ) + (twoLevelOffDiag c : ℂ) * Complex.I

/-- The candidate eigenvalue `twoLevelDiag c - i * twoLevelOffDiag c`. -/
def twoLevelEigMinus (c : ℝ) : ℂ :=
  (twoLevelDiag c : ℂ) - (twoLevelOffDiag c : ℂ) * Complex.I

/-- The normalized vector `(i, 1) / √2`. -/
def twoLevelKetPlus : Fin 2 → ℂ :=
  ![Complex.I / (Real.sqrt 2 : ℂ), 1 / (Real.sqrt 2 : ℂ)]

/-- The normalized vector `(-i, 1) / √2`. -/
def twoLevelKetMinus : Fin 2 → ℂ :=
  ![-Complex.I / (Real.sqrt 2 : ℂ), 1 / (Real.sqrt 2 : ℂ)]

/-- The unscaled comparison vector `(c + i, √(1 - c ^ 2))`. -/
def paperThetaPlusRaw (c : ℝ) : Fin 2 → ℂ :=
  ![((c : ℂ) + Complex.I), (twoLevelSin c : ℂ)]

/-- The unscaled comparison vector `(c - i, √(1 - c ^ 2))`. -/
def paperThetaMinusRaw (c : ℝ) : Fin 2 → ℂ :=
  ![((c : ℂ) - Complex.I), (twoLevelSin c : ℂ)]

/-- The vector `paperThetaPlusRaw c` scaled by `1 / √2`. -/
def paperThetaPlus (c : ℝ) : Fin 2 → ℂ :=
  (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • paperThetaPlusRaw c

/-- The vector `paperThetaMinusRaw c` scaled by `1 / √2`. -/
def paperThetaMinus (c : ℝ) : Fin 2 → ℂ :=
  (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • paperThetaMinusRaw c

/-- The square-root coefficient `twoLevelSin c` is nonnegative. -/
lemma twoLevelSin_nonneg (c : ℝ) : 0 ≤ twoLevelSin c := Real.sqrt_nonneg _

/-- When `c ^ 2 ≤ 1`, the square of `twoLevelSin c` equals `1 - c ^ 2`. -/
lemma twoLevelSin_sq (c : ℝ) (hc : c ^ 2 ≤ 1) : twoLevelSin c ^ 2 = 1 - c ^ 2 := by
  unfold twoLevelSin
  rw [Real.sq_sqrt]
  linarith

/-- The square-root coefficient `twoLevelSin c` is at most one. -/
lemma twoLevelSin_le_one (c : ℝ) : twoLevelSin c ≤ 1 := by
  unfold twoLevelSin
  rw [Real.sqrt_le_one]
  nlinarith [sq_nonneg c]

/-- For `0 ≤ c ≤ 1`, the deficit `1 - twoLevelSin c` is at most `c ^ 2`. -/
lemma one_sub_twoLevelSin_le_sq (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    1 - twoLevelSin c ≤ c ^ 2 := by
  have hs2 : twoLevelSin c ^ 2 = 1 - c ^ 2 := twoLevelSin_sq c (by nlinarith)
  have hs0 : 0 ≤ twoLevelSin c := twoLevelSin_nonneg c
  have hs1 : twoLevelSin c ≤ 1 := twoLevelSin_le_one c
  have heq : (1 - twoLevelSin c) * (1 + twoLevelSin c) = c ^ 2 := by
    nlinarith [hs2]
  have hmul : (1 - twoLevelSin c) * 1 ≤ (1 - twoLevelSin c) * (1 + twoLevelSin c) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith

/-- The off-diagonal coefficient is nonnegative when `c` is nonnegative. -/
lemma twoLevelOffDiag_nonneg (c : ℝ) (hc0 : 0 ≤ c) : 0 ≤ twoLevelOffDiag c := by
  unfold twoLevelOffDiag
  exact mul_nonneg (mul_nonneg (by norm_num) hc0) (twoLevelSin_nonneg c)

/-- For nonnegative `c`, the off-diagonal coefficient is at most `2 * c`. -/
lemma twoLevelOffDiag_le_two_mul (c : ℝ) (hc0 : 0 ≤ c) :
    twoLevelOffDiag c ≤ 2 * c := by
  unfold twoLevelOffDiag
  have hs : twoLevelSin c ≤ 1 := twoLevelSin_le_one c
  have h := mul_le_mul_of_nonneg_left hs (by linarith : (0 : ℝ) ≤ 2 * c)
  simpa using h

/-- For `0 ≤ c ≤ 1`, the cosine of `twoLevelPhase c` equals `twoLevelDiag c`. -/
lemma twoLevelPhase_cos (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    Real.cos (twoLevelPhase c) = twoLevelDiag c := by
  unfold twoLevelPhase twoLevelDiag
  have hcos : Real.cos (Real.arcsin c) = Real.sqrt (1 - c ^ 2) := Real.cos_arcsin c
  have h1c : 0 ≤ 1 - c ^ 2 := by nlinarith
  have hsq : Real.sqrt (1 - c ^ 2) ^ 2 = 1 - c ^ 2 := Real.sq_sqrt h1c
  calc Real.cos (2 * Real.arcsin c)
      = 2 * Real.cos (Real.arcsin c) ^ 2 - 1 := Real.cos_two_mul _
    _ = 2 * Real.sqrt (1 - c ^ 2) ^ 2 - 1 := by rw [hcos]
    _ = 2 * (1 - c ^ 2) - 1 := by rw [hsq]
    _ = 1 - 2 * c ^ 2 := by ring

/-- For `0 ≤ c ≤ 1`, the sine of `twoLevelPhase c` equals `twoLevelOffDiag c`. -/
lemma twoLevelPhase_sin (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    Real.sin (twoLevelPhase c) = twoLevelOffDiag c := by
  unfold twoLevelPhase twoLevelOffDiag twoLevelSin
  have hsin : Real.sin (Real.arcsin c) = c := Real.sin_arcsin (by linarith) hc1
  have hcos : Real.cos (Real.arcsin c) = Real.sqrt (1 - c ^ 2) := Real.cos_arcsin c
  calc Real.sin (2 * Real.arcsin c)
      = 2 * Real.sin (Real.arcsin c) * Real.cos (Real.arcsin c) := Real.sin_two_mul _
    _ = 2 * c * Real.sqrt (1 - c ^ 2) := by rw [hsin, hcos]

/-- For `0 ≤ c ≤ 1`, the plus eigenvalue equals `exp (i * twoLevelPhase c)`. -/
lemma twoLevelEigPlus_eq_exp (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    twoLevelEigPlus c = Complex.exp ((twoLevelPhase c : ℂ) * Complex.I) := by
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re]
    simp [twoLevelEigPlus, Complex.add_re, Complex.mul_re]
    rw [twoLevelPhase_cos c hc0 hc1]
  · rw [Complex.exp_ofReal_mul_I_im]
    simp [twoLevelEigPlus, Complex.add_im, Complex.mul_im]
    rw [twoLevelPhase_sin c hc0 hc1]

/-- For `0 ≤ c ≤ 1`, the minus eigenvalue equals `exp (-i * twoLevelPhase c)`. -/
lemma twoLevelEigMinus_eq_exp (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    twoLevelEigMinus c = Complex.exp (-((twoLevelPhase c : ℂ)) * Complex.I) := by
  have h : -((twoLevelPhase c : ℂ)) * Complex.I =
      ((-twoLevelPhase c : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h]
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re]
    simp [twoLevelEigMinus, Complex.sub_re, Complex.mul_re, Real.cos_neg]
    rw [twoLevelPhase_cos c hc0 hc1]
  · rw [Complex.exp_ofReal_mul_I_im]
    simp [twoLevelEigMinus, Complex.sub_im, Complex.mul_im, Real.sin_neg]
    rw [twoLevelPhase_sin c hc0 hc1]

/-- The vector `(i, 1)` is an eigenvector of the matrix with rows `(d, -b)` and `(b, d)`, with
eigenvalue `d + bi`. -/
lemma twoByTwo_mulVec_ketPlus (d b : ℝ) :
    (!![(d : ℂ), -(b : ℂ); (b : ℂ), (d : ℂ)]) *ᵥ (![Complex.I, 1] : Fin 2 → ℂ) =
      ((d : ℂ) + (b : ℂ) * Complex.I) • (![Complex.I, 1] : Fin 2 → ℂ) := by
  funext i
  fin_cases i
  · simp [Matrix.mulVec, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(b : ℂ)) * Complex.I_sq
  · simp [Matrix.mulVec, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
    ring

/-- The vector `(-i, 1)` is an eigenvector of the matrix with rows `(d, -b)` and `(b, d)`, with
eigenvalue `d - bi`. -/
lemma twoByTwo_mulVec_ketMinus (d b : ℝ) :
    (!![(d : ℂ), -(b : ℂ); (b : ℂ), (d : ℂ)]) *ᵥ (![-Complex.I, 1] : Fin 2 → ℂ) =
      ((d : ℂ) - (b : ℂ) * Complex.I) • (![-Complex.I, 1] : Fin 2 → ℂ) := by
  funext i
  fin_cases i
  · simp [Matrix.mulVec, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(b : ℂ)) * Complex.I_sq
  · simp [Matrix.mulVec, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
    ring

/-- Expresses `twoLevelKetPlus` as `(i, 1)` scaled by `1 / √2`. -/
lemma twoLevelKetPlus_eq_smul :
    twoLevelKetPlus = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • (![Complex.I, 1] : Fin 2 → ℂ) := by
  funext i
  fin_cases i <;>
    (simp [twoLevelKetPlus, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv] <;> ring)

/-- Expresses `twoLevelKetMinus` as `(-i, 1)` scaled by `1 / √2`. -/
lemma twoLevelKetMinus_eq_smul :
    twoLevelKetMinus = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • (![-Complex.I, 1] : Fin 2 → ℂ) := by
  funext i
  fin_cases i <;>
    (simp [twoLevelKetMinus, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv] <;> ring)

/-- The unscaled vector `(i, 1)` satisfies the plus eigenvector equation for `twoLevelUP c`. -/
lemma twoLevelUP_mulVec_ketPlus (c : ℝ) :
    twoLevelUP c *ᵥ (![Complex.I, 1] : Fin 2 → ℂ) =
      twoLevelEigPlus c • (![Complex.I, 1] : Fin 2 → ℂ) := by
  simpa [twoLevelUP, twoLevelEigPlus] using
    twoByTwo_mulVec_ketPlus (twoLevelDiag c) (twoLevelOffDiag c)

/-- The unscaled vector `(-i, 1)` satisfies the minus eigenvector equation for `twoLevelUP c`. -/
lemma twoLevelUP_mulVec_ketMinus (c : ℝ) :
    twoLevelUP c *ᵥ (![-Complex.I, 1] : Fin 2 → ℂ) =
      twoLevelEigMinus c • (![-Complex.I, 1] : Fin 2 → ℂ) := by
  simpa [twoLevelUP, twoLevelEigMinus] using
    twoByTwo_mulVec_ketMinus (twoLevelDiag c) (twoLevelOffDiag c)

/-- The normalized vector `twoLevelKetPlus` satisfies the eigenvector equation with eigenvalue
`twoLevelEigPlus c`. -/
lemma twoLevelUP_eigenvector_plus (c : ℝ) :
    twoLevelUP c *ᵥ twoLevelKetPlus = twoLevelEigPlus c • twoLevelKetPlus := by
  rw [twoLevelKetPlus_eq_smul, Matrix.mulVec_smul, twoLevelUP_mulVec_ketPlus]
  rw [smul_smul, smul_smul]
  congr 1
  ring

/-- The normalized vector `twoLevelKetMinus` satisfies the eigenvector equation with eigenvalue
`twoLevelEigMinus c`. -/
lemma twoLevelUP_eigenvector_minus (c : ℝ) :
    twoLevelUP c *ᵥ twoLevelKetMinus = twoLevelEigMinus c • twoLevelKetMinus := by
  rw [twoLevelKetMinus_eq_smul, Matrix.mulVec_smul, twoLevelUP_mulVec_ketMinus]
  rw [smul_smul, smul_smul]
  congr 1
  ring

/-- Computes the first coordinate of the plus unscaled residual as `b * (1 - s) - b * c * i`,
where `b = twoLevelOffDiag c` and `s = twoLevelSin c`. -/
lemma residual_raw_plus_zero (c : ℝ) :
    (twoLevelUP c *ᵥ paperThetaPlusRaw c - twoLevelEigPlus c • paperThetaPlusRaw c) 0 =
      ((twoLevelOffDiag c * (1 - twoLevelSin c) : ℝ) : ℂ)
        - ((twoLevelOffDiag c * c : ℝ) : ℂ) * Complex.I := by
  simp [twoLevelUP, twoLevelEigPlus, paperThetaPlusRaw, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  linear_combination (-(twoLevelOffDiag c : ℂ)) * Complex.I_sq

/-- Computes the second coordinate of the plus unscaled residual as `b * c + b * (1 - s) * i`,
where `b = twoLevelOffDiag c` and `s = twoLevelSin c`. -/
lemma residual_raw_plus_one (c : ℝ) :
    (twoLevelUP c *ᵥ paperThetaPlusRaw c - twoLevelEigPlus c • paperThetaPlusRaw c) 1 =
      ((twoLevelOffDiag c * c : ℝ) : ℂ)
        + ((twoLevelOffDiag c * (1 - twoLevelSin c) : ℝ) : ℂ) * Complex.I := by
  simp [twoLevelUP, twoLevelEigPlus, paperThetaPlusRaw, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

/-- Computes the first coordinate of the minus unscaled residual as `b * (1 - s) + b * c * i`,
where `b = twoLevelOffDiag c` and `s = twoLevelSin c`. -/
lemma residual_raw_minus_zero (c : ℝ) :
    (twoLevelUP c *ᵥ paperThetaMinusRaw c - twoLevelEigMinus c • paperThetaMinusRaw c) 0 =
      ((twoLevelOffDiag c * (1 - twoLevelSin c) : ℝ) : ℂ)
        + ((twoLevelOffDiag c * c : ℝ) : ℂ) * Complex.I := by
  simp [twoLevelUP, twoLevelEigMinus, paperThetaMinusRaw, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  linear_combination (-(twoLevelOffDiag c : ℂ)) * Complex.I_sq

/-- Computes the second coordinate of the minus unscaled residual as `b * c - b * (1 - s) * i`,
where `b = twoLevelOffDiag c` and `s = twoLevelSin c`. -/
lemma residual_raw_minus_one (c : ℝ) :
    (twoLevelUP c *ᵥ paperThetaMinusRaw c - twoLevelEigMinus c • paperThetaMinusRaw c) 1 =
      ((twoLevelOffDiag c * c : ℝ) : ℂ)
        - ((twoLevelOffDiag c * (1 - twoLevelSin c) : ℝ) : ℂ) * Complex.I := by
  simp [twoLevelUP, twoLevelEigMinus, paperThetaMinusRaw, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

/-- Scaling a vector by `1 / √2` scales its residual for `twoLevelEigPlus c` by the same factor. -/
lemma residual_smul_inv_plus (c : ℝ) (v : Fin 2 → ℂ) :
    twoLevelUP c *ᵥ ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • v) -
        twoLevelEigPlus c • ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • v)
      = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ •
          (twoLevelUP c *ᵥ v - twoLevelEigPlus c • v) := by
  rw [Matrix.mulVec_smul, smul_sub, smul_smul, smul_smul]
  congr 1
  ring

/-- Scaling a vector by `1 / √2` scales its residual for `twoLevelEigMinus c` by the same
factor. -/
lemma residual_smul_inv_minus (c : ℝ) (v : Fin 2 → ℂ) :
    twoLevelUP c *ᵥ ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • v) -
        twoLevelEigMinus c • ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • v)
      = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ •
          (twoLevelUP c *ᵥ v - twoLevelEigMinus c • v) := by
  rw [Matrix.mulVec_smul, smul_sub, smul_smul, smul_smul]
  congr 1
  ring

/-- The first coordinate of the plus comparison-vector residual equals `1 / √2` times `b * (1 -
s) - b * c * i`, where `b = twoLevelOffDiag c` and `s = twoLevelSin c`. -/
lemma residual_plus_zero (c : ℝ) :
    (twoLevelUP c *ᵥ paperThetaPlus c - twoLevelEigPlus c • paperThetaPlus c) 0 =
      (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ *
        (((twoLevelOffDiag c * (1 - twoLevelSin c) : ℝ) : ℂ)
          - ((twoLevelOffDiag c * c : ℝ) : ℂ) * Complex.I) := by
  unfold paperThetaPlus
  rw [residual_smul_inv_plus]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [residual_raw_plus_zero c]

/-- The second coordinate of the plus comparison-vector residual equals `1 / √2` times `b * c +
b * (1 - s) * i`, where `b = twoLevelOffDiag c` and `s = twoLevelSin c`. -/
lemma residual_plus_one (c : ℝ) :
    (twoLevelUP c *ᵥ paperThetaPlus c - twoLevelEigPlus c • paperThetaPlus c) 1 =
      (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ *
        (((twoLevelOffDiag c * c : ℝ) : ℂ)
          + ((twoLevelOffDiag c * (1 - twoLevelSin c) : ℝ) : ℂ) * Complex.I) := by
  unfold paperThetaPlus
  rw [residual_smul_inv_plus]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [residual_raw_plus_one c]

/-- The first coordinate of the minus comparison-vector residual equals `1 / √2` times `b * (1 -
s) + b * c * i`, where `b = twoLevelOffDiag c` and `s = twoLevelSin c`. -/
lemma residual_minus_zero (c : ℝ) :
    (twoLevelUP c *ᵥ paperThetaMinus c - twoLevelEigMinus c • paperThetaMinus c) 0 =
      (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ *
        (((twoLevelOffDiag c * (1 - twoLevelSin c) : ℝ) : ℂ)
          + ((twoLevelOffDiag c * c : ℝ) : ℂ) * Complex.I) := by
  unfold paperThetaMinus
  rw [residual_smul_inv_minus]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [residual_raw_minus_zero c]

/-- The second coordinate of the minus comparison-vector residual equals `1 / √2` times `b * c -
b * (1 - s) * i`, where `b = twoLevelOffDiag c` and `s = twoLevelSin c`. -/
lemma residual_minus_one (c : ℝ) :
    (twoLevelUP c *ᵥ paperThetaMinus c - twoLevelEigMinus c • paperThetaMinus c) 1 =
      (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ *
        (((twoLevelOffDiag c * c : ℝ) : ℂ)
          - ((twoLevelOffDiag c * (1 - twoLevelSin c) : ℝ) : ℂ) * Complex.I) := by
  unfold paperThetaMinus
  rw [residual_smul_inv_minus]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [residual_raw_minus_one c]

/-- For nonnegative `x` and `y`, the norm of `x + yi` is at most `x + y`. -/
lemma norm_ofReal_add_mul_I_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ‖((x : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I‖ ≤ x + y := by
  calc ‖((x : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I‖
      ≤ ‖((x : ℝ) : ℂ)‖ + ‖((y : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = x + y := by
        rw [Complex.norm_of_nonneg hx, Complex.norm_mul, Complex.norm_I, mul_one,
          Complex.norm_of_nonneg hy]

/-- For nonnegative `x` and `y`, the norm of `x - yi` is at most `x + y`. -/
lemma norm_ofReal_sub_mul_I_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ‖((x : ℝ) : ℂ) - ((y : ℝ) : ℂ) * Complex.I‖ ≤ x + y := by
  calc ‖((x : ℝ) : ℂ) - ((y : ℝ) : ℂ) * Complex.I‖
      ≤ ‖((x : ℝ) : ℂ)‖ + ‖((y : ℝ) : ℂ) * Complex.I‖ := norm_sub_le _ _
    _ = x + y := by
        rw [Complex.norm_of_nonneg hx, Complex.norm_mul, Complex.norm_I, mul_one,
          Complex.norm_of_nonneg hy]

/-- The complex norm of `1 / √2` is at most one. -/
lemma norm_inv_sqrt_two_le_one :
    ‖(((Real.sqrt 2 : ℝ) : ℂ))⁻¹‖ ≤ 1 := by
  rw [norm_inv, Complex.norm_of_nonneg (Real.sqrt_nonneg 2)]
  have h2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.one_le_sqrt]
    norm_num
  exact inv_le_one_of_one_le₀ h2

/-- Multiplication by `1 / √2` preserves an upper bound `B ≥ 0` on a complex norm. -/
lemma norm_smul_inv_sqrt_two_le {z : ℂ} {B : ℝ} (hz : ‖z‖ ≤ B) (hB0 : 0 ≤ B) :
    ‖(((Real.sqrt 2 : ℝ) : ℂ))⁻¹ * z‖ ≤ B := by
  rw [norm_mul]
  calc ‖(((Real.sqrt 2 : ℝ) : ℂ))⁻¹‖ * ‖z‖ ≤ 1 * B :=
        mul_le_mul norm_inv_sqrt_two_le_one hz (norm_nonneg _) (by norm_num)
    _ = B := by ring

/-- For `0 ≤ c ≤ 1 / 2`, the sum `twoLevelOffDiag c * (1 - twoLevelSin c) + twoLevelOffDiag c *
c` is at most `4 * c ^ 2`. -/
lemma offDiag_terms_le (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1 / 2) :
    twoLevelOffDiag c * (1 - twoLevelSin c) + twoLevelOffDiag c * c ≤ 4 * c ^ 2 := by
  have hb := twoLevelOffDiag_le_two_mul c hc0
  have hb0 := twoLevelOffDiag_nonneg c hc0
  have h1s0 : 0 ≤ 1 - twoLevelSin c := by
    have h := twoLevelSin_le_one c
    linarith
  have h1s : 1 - twoLevelSin c ≤ c ^ 2 :=
    one_sub_twoLevelSin_le_sq c hc0 (by linarith)
  have hc2 : c ^ 2 ≤ c := by nlinarith [hc0, hc1]
  have hc3 : c ^ 3 ≤ c ^ 2 := by nlinarith [hc2, hc0]
  have hp1 : twoLevelOffDiag c * (1 - twoLevelSin c) ≤ (2 * c) * c ^ 2 :=
    mul_le_mul hb h1s h1s0 (by linarith : (0 : ℝ) ≤ 2 * c)
  have hp2 : twoLevelOffDiag c * c ≤ (2 * c) * c :=
    mul_le_mul hb le_rfl hc0 (by linarith : (0 : ℝ) ≤ 2 * c)
  nlinarith [hp1, hp2, hc3, hc0]

/-- For `0 ≤ c ≤ 1 / 2`, every coordinate of the plus comparison-vector residual has norm at
most `4 * c ^ 2`. -/
lemma paper_vector_residual_plus (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1 / 2) :
    ∀ i : Fin 2,
      ‖(twoLevelUP c *ᵥ paperThetaPlus c - twoLevelEigPlus c • paperThetaPlus c) i‖
        ≤ 4 * c ^ 2 := by
  have hterms := offDiag_terms_le c hc0 hc1
  have hb0 := twoLevelOffDiag_nonneg c hc0
  have h1s0 : 0 ≤ 1 - twoLevelSin c := by
    have h := twoLevelSin_le_one c
    linarith
  intro i
  fin_cases i
  · change ‖(twoLevelUP c *ᵥ paperThetaPlus c - twoLevelEigPlus c • paperThetaPlus c) 0‖
      ≤ 4 * c ^ 2
    rw [residual_plus_zero c]
    have hz : ‖((twoLevelOffDiag c * (1 - twoLevelSin c) : ℝ) : ℂ)
        - ((twoLevelOffDiag c * c : ℝ) : ℂ) * Complex.I‖
        ≤ twoLevelOffDiag c * (1 - twoLevelSin c) + twoLevelOffDiag c * c :=
      norm_ofReal_sub_mul_I_le _ _ (mul_nonneg hb0 h1s0) (mul_nonneg hb0 hc0)
    exact le_trans (norm_smul_inv_sqrt_two_le hz (by positivity)) hterms
  · change ‖(twoLevelUP c *ᵥ paperThetaPlus c - twoLevelEigPlus c • paperThetaPlus c) 1‖
      ≤ 4 * c ^ 2
    rw [residual_plus_one c]
    have hz : ‖((twoLevelOffDiag c * c : ℝ) : ℂ)
        + ((twoLevelOffDiag c * (1 - twoLevelSin c) : ℝ) : ℂ) * Complex.I‖
        ≤ twoLevelOffDiag c * c + twoLevelOffDiag c * (1 - twoLevelSin c) :=
      norm_ofReal_add_mul_I_le _ _ (mul_nonneg hb0 hc0) (mul_nonneg hb0 h1s0)
    have hterms' : twoLevelOffDiag c * c + twoLevelOffDiag c * (1 - twoLevelSin c)
        ≤ 4 * c ^ 2 := by linarith
    exact le_trans (norm_smul_inv_sqrt_two_le hz (by positivity)) hterms'

/-- For `0 ≤ c ≤ 1 / 2`, every coordinate of the minus comparison-vector residual has norm at
most `4 * c ^ 2`. -/
lemma paper_vector_residual_minus (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1 / 2) :
    ∀ i : Fin 2,
      ‖(twoLevelUP c *ᵥ paperThetaMinus c - twoLevelEigMinus c • paperThetaMinus c) i‖
        ≤ 4 * c ^ 2 := by
  have hterms := offDiag_terms_le c hc0 hc1
  have hb0 := twoLevelOffDiag_nonneg c hc0
  have h1s0 : 0 ≤ 1 - twoLevelSin c := by
    have h := twoLevelSin_le_one c
    linarith
  intro i
  fin_cases i
  · change ‖(twoLevelUP c *ᵥ paperThetaMinus c - twoLevelEigMinus c • paperThetaMinus c) 0‖
      ≤ 4 * c ^ 2
    rw [residual_minus_zero c]
    have hz : ‖((twoLevelOffDiag c * (1 - twoLevelSin c) : ℝ) : ℂ)
        + ((twoLevelOffDiag c * c : ℝ) : ℂ) * Complex.I‖
        ≤ twoLevelOffDiag c * (1 - twoLevelSin c) + twoLevelOffDiag c * c :=
      norm_ofReal_add_mul_I_le _ _ (mul_nonneg hb0 h1s0) (mul_nonneg hb0 hc0)
    exact le_trans (norm_smul_inv_sqrt_two_le hz (by positivity)) hterms
  · change ‖(twoLevelUP c *ᵥ paperThetaMinus c - twoLevelEigMinus c • paperThetaMinus c) 1‖
      ≤ 4 * c ^ 2
    rw [residual_minus_one c]
    have hz : ‖((twoLevelOffDiag c * c : ℝ) : ℂ)
        - ((twoLevelOffDiag c * (1 - twoLevelSin c) : ℝ) : ℂ) * Complex.I‖
        ≤ twoLevelOffDiag c * c + twoLevelOffDiag c * (1 - twoLevelSin c) :=
      norm_ofReal_sub_mul_I_le _ _ (mul_nonneg hb0 hc0) (mul_nonneg hb0 h1s0)
    have hterms' : twoLevelOffDiag c * c + twoLevelOffDiag c * (1 - twoLevelSin c)
        ≤ 4 * c ^ 2 := by linarith
    exact le_trans (norm_smul_inv_sqrt_two_le hz (by positivity)) hterms'

/-- For `0 ≤ x ≤ 1 / 2`, the difference between `arcsin x` and `x` has absolute value at most `x
^ 3`. -/
lemma abs_arcsin_sub_self_le_cube {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    |Real.arcsin x - x| ≤ x ^ 3 := by
  have hx1 : x ≤ 1 := by linarith
  have hlow : x ≤ Real.arcsin x := by
    have h1 : Real.arcsin (Real.sin x) ≤ Real.arcsin x :=
      Real.arcsin_le_arcsin (Real.sin_le hx0)
    have h2 : Real.arcsin (Real.sin x) = x := by
      apply Real.arcsin_sin
      · linarith [Real.neg_one_le_sin x, Real.two_le_pi]
      · linarith [Real.sin_le_one x, Real.two_le_pi]
    linarith
  have hupper : Real.arcsin x ≤ x + x ^ 3 := by
    rcases eq_or_lt_of_le hx0 with hzero | hpos
    · rw [← hzero]
      simp
    · have hy0 : 0 < x + x ^ 3 := by positivity
      have hx3le : x ^ 3 ≤ 1 / 8 := by
        have h := pow_le_pow_left₀ hx0 hx 3
        norm_num at h
        exact h
      have hy1 : x + x ^ 3 ≤ 1 := by linarith
      have hsin : (x + x ^ 3) - (x + x ^ 3) ^ 3 / 4 < Real.sin (x + x ^ 3) := by
        linarith [Real.sin_gt_sub_cube hy0, pow_nonneg hy0.le 3]
      have hcube : (1 + x ^ 2) ^ 3 ≤ 4 := by
        have h1s : 1 + x ^ 2 ≤ 5 / 4 := by
          nlinarith [pow_le_pow_left₀ hx0 hx 2]
        have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + x ^ 2) h1s 3
        norm_num at h
        linarith
      have hrew : (x + x ^ 3) ^ 3 = x ^ 3 * (1 + x ^ 2) ^ 3 := by ring
      have hx3n : 0 ≤ x ^ 3 := by positivity
      have hmul : x ^ 3 * (1 + x ^ 2) ^ 3 ≤ 4 * x ^ 3 := by
        have := mul_le_mul_of_nonneg_left hcube hx3n
        linarith
      have hlower : x ≤ (x + x ^ 3) - (x + x ^ 3) ^ 3 / 4 := by
        rw [hrew]
        nlinarith [hmul]
      have hy2 : x + x ^ 3 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor <;> nlinarith [Real.two_le_pi]
      exact (Real.arcsin_le_iff_le_sin ⟨by linarith, hx1⟩ hy2).mpr (by linarith)
  rw [abs_le]
  constructor <;> linarith

/-- For `0 ≤ c ≤ 1 / 2`, the phase `twoLevelPhase c` differs from `2 * c` by at most `2 * c ^ 3`
[ChildsEisenberg2003]. -/
lemma twoLevelPhase_approx (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1 / 2) :
    |twoLevelPhase c - 2 * c| ≤ 2 * c ^ 3 := by
  unfold twoLevelPhase
  rw [show 2 * Real.arcsin c - 2 * c = 2 * (Real.arcsin c - c) by ring, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left (abs_arcsin_sub_self_le_cube hc0 hc1) (by norm_num)

/-- For `0 ≤ c ≤ 1 / 2`, collects the exact eigenvector and eigenvalue identities, the cubic
phase estimate, and the quadratic coordinatewise residual bounds for the two-level model
[ChildsEisenberg2003]. -/
theorem lemma3_two_level (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1 / 2) :
    (twoLevelUP c *ᵥ twoLevelKetPlus = twoLevelEigPlus c • twoLevelKetPlus) ∧
    (twoLevelUP c *ᵥ twoLevelKetMinus = twoLevelEigMinus c • twoLevelKetMinus) ∧
    (twoLevelEigPlus c = Complex.exp ((twoLevelPhase c : ℂ) * Complex.I)) ∧
    (twoLevelEigMinus c = Complex.exp (-((twoLevelPhase c : ℂ)) * Complex.I)) ∧
    (|twoLevelPhase c - 2 * c| ≤ 2 * c ^ 3) ∧
    (∀ i : Fin 2, ‖(twoLevelUP c *ᵥ paperThetaPlus c -
        twoLevelEigPlus c • paperThetaPlus c) i‖ ≤ 4 * c ^ 2) ∧
    (∀ i : Fin 2, ‖(twoLevelUP c *ᵥ paperThetaMinus c -
        twoLevelEigMinus c • paperThetaMinus c) i‖ ≤ 4 * c ^ 2) :=
  ⟨twoLevelUP_eigenvector_plus c,
   twoLevelUP_eigenvector_minus c,
   twoLevelEigPlus_eq_exp c hc0 (by linarith),
   twoLevelEigMinus_eq_exp c hc0 (by linarith),
   twoLevelPhase_approx c hc0 hc1,
   paper_vector_residual_plus c hc0 hc1,
   paper_vector_residual_minus c hc0 hc1⟩

/-- The real overlap scale is nonnegative under the stated nonnegativity assumptions on `M` and
`N`. -/
lemma twoLevelOverlap_nonneg (M N L : ℕ) (hM : 0 ≤ (M : ℝ)) (hN : 0 ≤ (N : ℝ)) :
    0 ≤ twoLevelOverlap M N L :=
  Real.rpow_nonneg (div_nonneg hM hN) _

end Qatlib.Papers.SubsetFinding03.MainResults.ProjectorEigenvectors
