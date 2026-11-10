/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Field.Basic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FastGradEst04.PeakNumerics

def cubeSecondMoment : ℝ := 1 / 12

def sigmaSq1D (α N : ℝ) : ℝ := (2 * α * N) ^ 2 * cubeSecondMoment

theorem sigmaSq1D_eq (α N : ℝ) : sigmaSq1D α N = α ^ 2 * N ^ 2 / 3 := by
  unfold sigmaSq1D cubeSecondMoment
  ring

theorem sigmaSq1D_scale_N (α N c : ℝ) :
    sigmaSq1D α (c * N) = c ^ 2 * sigmaSq1D α N := by
  rw [sigmaSq1D_eq, sigmaSq1D_eq]
  ring

theorem sigmaSq1D_scale_alpha (α N c : ℝ) :
    sigmaSq1D (c * α) N = c ^ 2 * sigmaSq1D α N := by
  rw [sigmaSq1D_eq, sigmaSq1D_eq]
  ring

theorem sigmaSq1D_figure2_value : sigmaSq1D (1 / 50) 80 = 64 / 75 := by
  rw [sigmaSq1D_eq]
  norm_num

def sideVecA (l : ℝ) : ℝ × ℝ := (l / 10, l / 10)

def sideVecB (l : ℝ) : ℝ × ℝ := (l / 10, -(l / 10))

theorem rotated_square_sides (l : ℝ) :
    (sideVecA l).1 ^ 2 + (sideVecA l).2 ^ 2 = (Real.sqrt 2 * l / 10) ^ 2
      ∧ (sideVecB l).1 ^ 2 + (sideVecB l).2 ^ 2 = (Real.sqrt 2 * l / 10) ^ 2 := by
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have key : (l / 10) ^ 2 + (l / 10) ^ 2 = (Real.sqrt 2 * l / 10) ^ 2 := by
    rw [show (Real.sqrt 2 * l / 10) ^ 2 = (Real.sqrt 2) ^ 2 * (l / 10) ^ 2 by ring]
    rw [h2]
    ring
  constructor <;> · simp only [sideVecA, sideVecB, neg_sq]; exact key

theorem rotated_square_orthogonal (l : ℝ) :
    (sideVecA l).1 * (sideVecB l).1 + (sideVecA l).2 * (sideVecB l).2 = 0 := by
  unfold sideVecA sideVecB
  ring

theorem rotated_square_side_pos (l : ℝ) (hl : 0 < l) :
    0 < (sideVecA l).1 ^ 2 + (sideVecA l).2 ^ 2 := by
  unfold sideVecA
  positivity

end Qatlib.Papers.FastGradEst04.PeakNumerics
