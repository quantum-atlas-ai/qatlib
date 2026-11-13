/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.IsingPartit08.MainResults.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Normalized gate parameters and explicit rotation angles

This module defines the normalized coefficients `cosHalf` and `sinHalf` and the angle `rotAngle`
used in the gate parameterization of [Geraci2008]. It proves their unit-circle identity and
evaluates the coefficients and angles at the rational parameters `4 / 3` and `3 / 4`.

## Main statements

* `cosHalf_sq_add_sinHalf_sq`: proves normalization of the two gate coefficients.
* `rotAngle_fourThirds`: evaluates the angle at `4 / 3`.
* `rotAngle_threeQuarters`: evaluates the angle at `3 / 4` using an arcsine expression.

## References

* [Geraci, 2008][Geraci2008]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical

attribute [local instance] Classical.propDecidable

namespace Qatlib.Papers.IsingPartit08.MainResults

/-- The normalized coefficient `lam / sqrt (lam ^ 2 + 1)`. -/
def cosHalf (lam : ℝ) : ℝ := lam / Real.sqrt (lam ^ 2 + 1)

/-- The normalized coefficient `1 / sqrt (lam ^ 2 + 1)`. -/
def sinHalf (lam : ℝ) : ℝ := 1 / Real.sqrt (lam ^ 2 + 1)

/-- The rotation parameter `2 * arccos (cosHalf lam)`. -/
def rotAngle (lam : ℝ) : ℝ := 2 * Real.arccos (cosHalf lam)

/-- The normalized coefficients satisfy `cosHalf lam ^ 2 + sinHalf lam ^ 2 = 1`. See
[Geraci2008]. -/
theorem cosHalf_sq_add_sinHalf_sq (lam : ℝ) :
    cosHalf lam ^ 2 + sinHalf lam ^ 2 = 1 := by
  have hpos : 0 < lam ^ 2 + 1 := by nlinarith [sq_nonneg lam]
  have hne : Real.sqrt (lam ^ 2 + 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  unfold cosHalf sinHalf
  field_simp
  rw [Real.sq_sqrt (le_of_lt hpos)]

/-- The normalized cosine coefficient at `lam = 4 / 3` equals `4 / 5`. -/
theorem cosHalf_fourThirds : cosHalf (4 / 3 : ℝ) = 4 / 5 := by
  have h : (4 / 3 : ℝ) ^ 2 + 1 = (5 / 3) ^ 2 := by norm_num
  unfold cosHalf
  rw [h, Real.sqrt_sq (by norm_num)]
  norm_num

/-- The normalized sine coefficient at `lam = 4 / 3` equals `3 / 5`. -/
theorem sinHalf_fourThirds : sinHalf (4 / 3 : ℝ) = 3 / 5 := by
  have h : (4 / 3 : ℝ) ^ 2 + 1 = (5 / 3) ^ 2 := by norm_num
  unfold sinHalf
  rw [h, Real.sqrt_sq (by norm_num)]
  norm_num

/-- The normalized cosine coefficient at `lam = 3 / 4` equals `3 / 5`. -/
theorem cosHalf_threeQuarters : cosHalf (3 / 4 : ℝ) = 3 / 5 := by
  have h : (3 / 4 : ℝ) ^ 2 + 1 = (5 / 4) ^ 2 := by norm_num
  unfold cosHalf
  rw [h, Real.sqrt_sq (by norm_num)]
  norm_num

/-- The normalized sine coefficient at `lam = 3 / 4` equals `4 / 5`. -/
theorem sinHalf_threeQuarters : sinHalf (3 / 4 : ℝ) = 4 / 5 := by
  have h : (3 / 4 : ℝ) ^ 2 + 1 = (5 / 4) ^ 2 := by norm_num
  unfold sinHalf
  rw [h, Real.sqrt_sq (by norm_num)]
  norm_num

/-- The principal inverse trigonometric values satisfy `arccos (3 / 5) = arcsin (4 / 5)`. -/
theorem arccos_threeFifths : Real.arccos (3 / 5 : ℝ) = Real.arcsin (4 / 5) := by
  rw [Real.arccos_eq_arcsin (by norm_num : (0 : ℝ) ≤ 3 / 5)]
  congr 1
  rw [show (1 : ℝ) - (3 / 5) ^ 2 = (4 / 5) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

/-- The rotation parameter at `4 / 3` equals `2 * arccos (4 / 5)`. See [Geraci2008]. -/
theorem rotAngle_fourThirds : rotAngle (4 / 3 : ℝ) = 2 * Real.arccos (4 / 5) := by
  unfold rotAngle
  rw [cosHalf_fourThirds]

/-- The rotation parameter at `3 / 4` equals `2 * arcsin (4 / 5)`. See [Geraci2008]. -/
theorem rotAngle_threeQuarters : rotAngle (3 / 4 : ℝ) = 2 * Real.arcsin (4 / 5) := by
  unfold rotAngle
  rw [cosHalf_threeQuarters, arccos_threeFifths]

end Qatlib.Papers.IsingPartit08.MainResults
