/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Field.Basic

/-!
# Peak variance and rotated-square geometry

`sigmaSq1D` uses the cube second-moment constant `cubeSecondMoment` to describe a
one-dimensional variance expression. The module proves its quadratic scaling laws and a
numerical value, and checks lengths and orthogonality of two rotated-square side vectors. The
construction follows [Jordan2005Gradient].

## Main statements

* `sigmaSq1D_eq`: simplifies the variance to `α^2 * N^2 / 3`.
* `sigmaSq1D_figure2_value`: evaluates the chosen numerical parameters.
* `rotated_square_orthogonal`: proves the side vectors are perpendicular.

## References

* [Jordan, 2005][Jordan2005Gradient]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FastGradEst04.PeakNumerics

/-- The unit-interval second-moment constant `1 / 12` used in the variance expression. -/
def cubeSecondMoment : ℝ := 1 / 12

/-- The one-dimensional variance expression `(2 * α * N)^2 * cubeSecondMoment`. -/
def sigmaSq1D (α N : ℝ) : ℝ := (2 * α * N) ^ 2 * cubeSecondMoment

/-- The variance expression simplifies to `α^2 * N^2 / 3`. -/
theorem sigmaSq1D_eq (α N : ℝ) : sigmaSq1D α N = α ^ 2 * N ^ 2 / 3 := by
  unfold sigmaSq1D cubeSecondMoment
  ring

/-- Scaling `N` by `c` multiplies the variance expression by `c^2`. -/
theorem sigmaSq1D_scale_N (α N c : ℝ) :
    sigmaSq1D α (c * N) = c ^ 2 * sigmaSq1D α N := by
  rw [sigmaSq1D_eq, sigmaSq1D_eq]
  ring

/-- Scaling `α` by `c` multiplies the variance expression by `c^2`. -/
theorem sigmaSq1D_scale_alpha (α N c : ℝ) :
    sigmaSq1D (c * α) N = c ^ 2 * sigmaSq1D α N := by
  rw [sigmaSq1D_eq, sigmaSq1D_eq]
  ring

/-- For `α = 1 / 50` and `N = 80`, the variance expression equals `64 / 75`. -/
theorem sigmaSq1D_figure2_value : sigmaSq1D (1 / 50) 80 = 64 / 75 := by
  rw [sigmaSq1D_eq]
  norm_num

/-- The side vector `(l / 10, l / 10)`. -/
def sideVecA (l : ℝ) : ℝ × ℝ := (l / 10, l / 10)

/-- The side vector `(l / 10, -(l / 10))`. -/
def sideVecB (l : ℝ) : ℝ × ℝ := (l / 10, -(l / 10))

/-- Both side vectors have squared length `(Real.sqrt 2 * l / 10)^2`. -/
theorem rotated_square_sides (l : ℝ) :
    (sideVecA l).1 ^ 2 + (sideVecA l).2 ^ 2 = (Real.sqrt 2 * l / 10) ^ 2
      ∧ (sideVecB l).1 ^ 2 + (sideVecB l).2 ^ 2 = (Real.sqrt 2 * l / 10) ^ 2 := by
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have key : (l / 10) ^ 2 + (l / 10) ^ 2 = (Real.sqrt 2 * l / 10) ^ 2 := by
    rw [show (Real.sqrt 2 * l / 10) ^ 2 = (Real.sqrt 2) ^ 2 * (l / 10) ^ 2 by ring]
    rw [h2]
    ring
  constructor <;> · simp only [sideVecA, sideVecB, neg_sq]; exact key

/-- The two side vectors have zero dot product. -/
theorem rotated_square_orthogonal (l : ℝ) :
    (sideVecA l).1 * (sideVecB l).1 + (sideVecA l).2 * (sideVecB l).2 = 0 := by
  unfold sideVecA sideVecB
  ring

/-- The squared length of `sideVecA l` is positive when `l` is positive. -/
theorem rotated_square_side_pos (l : ℝ) (hl : 0 < l) :
    0 < (sideVecA l).1 ^ 2 + (sideVecA l).2 ^ 2 := by
  unfold sideVecA
  positivity

end Qatlib.Papers.FastGradEst04.PeakNumerics
