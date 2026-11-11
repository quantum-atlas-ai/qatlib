/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic

/-!
# AdaptHHL reciprocal rotations and norm scaling

The module defines the clock coefficient `hhlCoefficient`, represented eigenvalues
`scaledEigenvalue`, and controlled rotation angles `rotationAngle`. On a nonzero integer grid
label the rotation ratio is the reciprocal label, independent of the number of clock qubits.

`solutionNormSq` and `ancillaSuccessProb` describe finite sums of squared spectral amplitudes.
Their scaling identity yields the solution norm reconstruction formula used by AdaptHHL. See
[BaskaranEtAl2023].

## Main statements

* `rotationAngle_eq_inv`: For nonzero `i`, the grid rotation angle equals `2 * arcsin (i⁻¹)`.
* `hhlCoefficient_maximal`: Any coefficient whose ratio to every positive grid eigenvalue is at
  most one is at most `hhlCoefficient nr`.
* `adaptHHL_solutionNorm_eq`: For positive `d`, the AdaptHHL solution norm at scale
  `hhlCoefficient nr / d` is the square root of the corresponding ancilla success expression
  divided by `d`.

## References

* [Baskaran et al., 2023][BaskaranEtAl2023]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.HHLManyBody22.AdaptHhl

/-- The reciprocal clock grid size `1 / 2^nr`. -/
def hhlCoefficient (nr : ℕ) : ℝ := ((2 : ℝ) ^ nr)⁻¹

/-- The represented eigenvalue `i / 2^nr`. -/
def scaledEigenvalue (nr : ℕ) (i : ℕ) : ℝ := (i : ℝ) / (2 : ℝ) ^ nr

/-- The angle `2 * arcsin (c / lam)`. -/
def rotationAngle (c lam : ℝ) : ℝ := 2 * Real.arcsin (c / lam)

/-- For nonzero `i`, the ratio of `hhlCoefficient nr` to `scaledEigenvalue nr i` is `i⁻¹`. -/
theorem hhlCoefficient_div_scaledEigenvalue (nr i : ℕ) (hi : i ≠ 0) :
    hhlCoefficient nr / scaledEigenvalue nr i = (i : ℝ)⁻¹ := by
  unfold hhlCoefficient scaledEigenvalue
  have h2 : ((2 : ℝ) ^ nr) ≠ 0 := by positivity
  have hi' : (i : ℝ) ≠ 0 := by exact_mod_cast hi
  field_simp

/-- For positive integer `i`, the grid rotation ratio lies in the interval `[0,1]`. -/
theorem hhlCoefficient_ratio_mem_unit_interval (nr i : ℕ) (hi : 0 < i) :
    0 ≤ hhlCoefficient nr / scaledEigenvalue nr i ∧
      hhlCoefficient nr / scaledEigenvalue nr i ≤ 1 := by
  rw [hhlCoefficient_div_scaledEigenvalue nr i hi.ne']
  have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
  constructor
  · exact inv_nonneg.mpr (by positivity)
  · exact inv_le_one_of_one_le₀ hi'

/-- Any coefficient whose ratio to every positive grid eigenvalue is at most one is at most
`hhlCoefficient nr`. -/
theorem hhlCoefficient_maximal (nr : ℕ) (c' : ℝ)
    (h : ∀ i : ℕ, 1 ≤ i → c' / scaledEigenvalue nr i ≤ 1) :
    c' ≤ hhlCoefficient nr := by
  have h1 := h 1 le_rfl
  simp only [scaledEigenvalue, Nat.cast_one] at h1
  have h2 : (0 : ℝ) < (2 : ℝ) ^ nr := by positivity
  have hratio : c' / ((1 : ℝ) / (2 : ℝ) ^ nr) = c' * (2 : ℝ) ^ nr := by
    field_simp
  rw [hratio] at h1
  rw [hhlCoefficient]
  rw [show ((2 : ℝ) ^ nr)⁻¹ = 1 / (2 : ℝ) ^ nr from (one_div _).symm]
  exact (le_div_iff₀ h2).mpr (by simpa using h1)

/-- For nonzero `i`, the grid rotation angle equals `2 * arcsin (i⁻¹)`. See [BaskaranEtAl2023]. -/
theorem rotationAngle_eq_inv (nr i : ℕ) (hi : i ≠ 0) :
    rotationAngle (hhlCoefficient nr) (scaledEigenvalue nr i) =
      2 * Real.arcsin ((i : ℝ)⁻¹) := by
  rw [rotationAngle, hhlCoefficient_div_scaledEigenvalue nr i hi]

/-- The angle `rotationAngle c 0` is zero. -/
theorem rotationAngle_zero (c : ℝ) : rotationAngle c 0 = 0 := by
  simp [rotationAngle]

variable {ι : Type*} [Fintype ι]

/-- The spectral solution amplitude `b i * s / lam i`. -/
def xAmplitude (s : ℝ) (lam : ι → ℝ) (b : ι → ℂ) (i : ι) : ℂ :=
  b i * (s : ℂ) / ((lam i : ℝ) : ℂ)

/-- The sum of squared norms of the spectral solution amplitudes. -/
def solutionNormSq (s : ℝ) (lam : ι → ℝ) (b : ι → ℂ) : ℝ :=
  ∑ i, ‖xAmplitude s lam b i‖ ^ 2

/-- The sum of squared norms of the success amplitudes `c * b i / lam i`. -/
def ancillaSuccessProb (c : ℝ) (lam : ι → ℝ) (b : ι → ℂ) : ℝ :=
  ∑ i, ‖(c : ℂ) * b i / ((lam i : ℝ) : ℂ)‖ ^ 2

/-- The squared solution norm is nonnegative. -/
theorem solutionNormSq_nonneg (s : ℝ) (lam : ι → ℝ) (b : ι → ℂ) :
    0 ≤ solutionNormSq s lam b := by
  unfold solutionNormSq
  apply Finset.sum_nonneg
  intro i _
  positivity

/-- The ancilla success expression is nonnegative. -/
theorem ancillaSuccessProb_nonneg (c : ℝ) (lam : ι → ℝ) (b : ι → ℂ) :
    0 ≤ ancillaSuccessProb c lam b := by
  unfold ancillaSuccessProb
  apply Finset.sum_nonneg
  intro i _
  positivity

/-- The squared solution norm at scale `c/d` equals the ancilla success expression at
coefficient `c` divided by `d^2`. -/
theorem solutionNormSq_eq_successProb_div
    (c d : ℝ) (lam : ι → ℝ) (b : ι → ℂ) :
    solutionNormSq (c / d) lam b = ancillaSuccessProb c lam b / d ^ 2 := by
  unfold solutionNormSq ancillaSuccessProb
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  have hz : xAmplitude (c / d) lam b i = ((c : ℂ) * b i / ((lam i : ℝ) : ℂ)) / (d : ℂ) := by
    unfold xAmplitude
    push_cast
    ring
  rw [hz, norm_div, div_pow]
  congr 1
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- For positive `d`, the solution norm at scale `c/d` is the square root of the ancilla success
expression divided by `d`. -/
theorem solutionNorm_eq_sqrt_successProb_div
    (c d : ℝ) (hd : 0 < d) (lam : ι → ℝ) (b : ι → ℂ) :
    Real.sqrt (solutionNormSq (c / d) lam b) =
      Real.sqrt (ancillaSuccessProb c lam b) / d := by
  rw [solutionNormSq_eq_successProb_div c d lam b]
  rw [Real.sqrt_div (ancillaSuccessProb_nonneg c lam b)]
  rw [Real.sqrt_sq hd.le]

/-- For positive `d`, the AdaptHHL solution norm at scale `hhlCoefficient nr / d` is the square
root of the corresponding ancilla success expression divided by `d`. -/
theorem adaptHHL_solutionNorm_eq (nr : ℕ) (d : ℝ) (hd : 0 < d) (lam : ι → ℝ)
    (b : ι → ℂ) :
    Real.sqrt (solutionNormSq (hhlCoefficient nr / d) lam b) =
      Real.sqrt (ancillaSuccessProb (hhlCoefficient nr) lam b) / d :=
  solutionNorm_eq_sqrt_successProb_div _ _ hd lam b

end Qatlib.Papers.HHLManyBody22.AdaptHhl
