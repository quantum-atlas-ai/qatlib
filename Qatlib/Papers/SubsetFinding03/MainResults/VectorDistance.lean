/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SubsetFinding03.MainResults.ProjectorEigenvectors

@[expose] public section

/-!
# Coordinate error of the two-level comparison vector

Equations (54)--(55) of arXiv:quant-ph/0311038v2 give approximations to
two eigenvector overlaps. Compare the pinned ideal two-level plus vector
with its limiting vector, using the square-root deficit for the second coordinate.
-/

set_option autoImplicit false

open Qatlib.Papers.SubsetFinding03.MainResults.ProjectorEigenvectors

namespace Qatlib.Papers.SubsetFinding03.MainResults

/-- Each coordinate of the ideal plus vector differs from its limit by at most `2c`
for `0 ≤ c ≤ 1/2`. -/
theorem paperThetaPlus_distance (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1 / 2) :
    ∀ i : Fin 2, ‖(paperThetaPlus c - twoLevelKetPlus) i‖ ≤ 2 * c := by
  have hroot : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  have hinv : ‖((Real.sqrt 2 : ℝ) : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_eq_one_div]
    exact (div_le_iff₀ (by positivity)).mpr (by simp [hroot])
  have hs : 0 ≤ 1 - twoLevelSin c := sub_nonneg.mpr (twoLevelSin_le_one c)
  have hdef : 1 - twoLevelSin c ≤ c :=
    (one_sub_twoLevelSin_le_sq c hc0 (by linarith)).trans (by nlinarith)
  intro i
  fin_cases i
  · change ‖(paperThetaPlus c - twoLevelKetPlus) 0‖ ≤ _
    have hx : (paperThetaPlus c - twoLevelKetPlus) 0 =
        (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) * (c : ℂ) := by
      simp [paperThetaPlus, paperThetaPlusRaw, twoLevelKetPlus, div_eq_mul_inv]
      ring
    rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0]
    exact (mul_le_of_le_one_left hc0 hinv).trans (by linarith)
  · change ‖(paperThetaPlus c - twoLevelKetPlus) 1‖ ≤ _
    have hx : (paperThetaPlus c - twoLevelKetPlus) 1 =
        (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) * ((twoLevelSin c - 1 : ℝ) : ℂ) := by
      simp [paperThetaPlus, paperThetaPlusRaw, twoLevelKetPlus, div_eq_mul_inv]
      ring
    rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    calc
      _ ≤ -(twoLevelSin c - 1) := mul_le_of_le_one_left (by linarith) hinv
      _ ≤ 2 * c := by linarith

end Qatlib.Papers.SubsetFinding03.MainResults
