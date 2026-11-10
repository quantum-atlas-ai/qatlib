/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.IsingPartit08.MainResults.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Classical

attribute [local instance] Classical.propDecidable

namespace Qatlib.Papers.IsingPartit08.MainResults

def cosHalf (lam : ℝ) : ℝ := lam / Real.sqrt (lam ^ 2 + 1)

def sinHalf (lam : ℝ) : ℝ := 1 / Real.sqrt (lam ^ 2 + 1)

def rotAngle (lam : ℝ) : ℝ := 2 * Real.arccos (cosHalf lam)

theorem cosHalf_sq_add_sinHalf_sq (lam : ℝ) :
    cosHalf lam ^ 2 + sinHalf lam ^ 2 = 1 := by
  have hpos : 0 < lam ^ 2 + 1 := by nlinarith [sq_nonneg lam]
  have hne : Real.sqrt (lam ^ 2 + 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  unfold cosHalf sinHalf
  field_simp
  rw [Real.sq_sqrt (le_of_lt hpos)]

theorem cosHalf_fourThirds : cosHalf (4 / 3 : ℝ) = 4 / 5 := by
  have h : (4 / 3 : ℝ) ^ 2 + 1 = (5 / 3) ^ 2 := by norm_num
  unfold cosHalf
  rw [h, Real.sqrt_sq (by norm_num)]
  norm_num

theorem sinHalf_fourThirds : sinHalf (4 / 3 : ℝ) = 3 / 5 := by
  have h : (4 / 3 : ℝ) ^ 2 + 1 = (5 / 3) ^ 2 := by norm_num
  unfold sinHalf
  rw [h, Real.sqrt_sq (by norm_num)]
  norm_num

theorem cosHalf_threeQuarters : cosHalf (3 / 4 : ℝ) = 3 / 5 := by
  have h : (3 / 4 : ℝ) ^ 2 + 1 = (5 / 4) ^ 2 := by norm_num
  unfold cosHalf
  rw [h, Real.sqrt_sq (by norm_num)]
  norm_num

theorem sinHalf_threeQuarters : sinHalf (3 / 4 : ℝ) = 4 / 5 := by
  have h : (3 / 4 : ℝ) ^ 2 + 1 = (5 / 4) ^ 2 := by norm_num
  unfold sinHalf
  rw [h, Real.sqrt_sq (by norm_num)]
  norm_num

theorem arccos_threeFifths : Real.arccos (3 / 5 : ℝ) = Real.arcsin (4 / 5) := by
  rw [Real.arccos_eq_arcsin (by norm_num : (0 : ℝ) ≤ 3 / 5)]
  congr 1
  rw [show (1 : ℝ) - (3 / 5) ^ 2 = (4 / 5) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

theorem rotAngle_fourThirds : rotAngle (4 / 3 : ℝ) = 2 * Real.arccos (4 / 5) := by
  unfold rotAngle
  rw [cosHalf_fourThirds]

theorem rotAngle_threeQuarters : rotAngle (3 / 4 : ℝ) = 2 * Real.arcsin (4 / 5) := by
  unfold rotAngle
  rw [cosHalf_threeQuarters, arccos_threeFifths]

end Qatlib.Papers.IsingPartit08.MainResults
