/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Phase insensitive distance between vectors

`rankOneDistance` is the square root of the sum of squared norms minus twice the modulus of the
inner product. The module proves that its radicand is nonnegative and that this distance is
bounded by the ordinary vector error. For an inner product that is real and nonnegative, the two
quantities coincide.

The mathematical setting follows [BerryCosta2024].

## Main statements

* `rankOneDistance_le_vector_error`: the phase insensitive distance is bounded by vector error.
* `rankOneDistance_eq_vector_error`: equality for aligned inner products.

## References

* [Berry and Costa, 2024][BerryCosta2024]
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.DysonSeries22.PureDistance
open scoped ComplexInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The phase insensitive distance `sqrt (‖x‖² + ‖y‖² - 2 * ‖inner ℂ x y‖)` between two vectors. -/
def rankOneDistance (x y : E) : ℝ :=
  Real.sqrt (‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * ‖inner ℂ x y‖)

/-- The expression under the square root in `rankOneDistance` is nonnegative. -/
theorem radicand_nonneg (x y : E) :
    0 ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * ‖inner ℂ x y‖ := by
  have h := norm_inner_le_norm (𝕜 := ℂ) x y
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-- The rank one distance between two vectors is at most their ordinary norm distance. See
[Berry and Costa, 2024, Eqs. (78)–(79)][BerryCosta2024]. -/
theorem rankOneDistance_le_vector_error (x y : E) :
    rankOneDistance x y ≤ ‖x - y‖ := by
  unfold rankOneDistance
  apply (Real.sqrt_le_iff).2
  refine ⟨norm_nonneg _, ?_⟩
  have hn := norm_sub_sq (𝕜 := ℂ) x y
  change ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * (inner ℂ x y).re + ‖y‖ ^ 2 at hn
  have hr := Complex.re_le_norm (inner ℂ x y)
  nlinarith

/-- If the inner product of `x` and `y` is real and nonnegative, their rank one distance equals
`‖x - y‖`. See [Berry and Costa, 2024, Eqs. (78)–(79)][BerryCosta2024]. -/
theorem rankOneDistance_eq_vector_error (x y : E)
    (halign : inner ℂ x y = ((inner ℂ x y).re : ℂ))
    (hpos : 0 ≤ (inner ℂ x y).re) :
    rankOneDistance x y = ‖x - y‖ := by
  have ha : ‖inner ℂ x y‖ = (inner ℂ x y).re := by
    conv_lhs => rw [halign]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos]
  have hn := norm_sub_sq (𝕜 := ℂ) x y
  change ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * (inner ℂ x y).re + ‖y‖ ^ 2 at hn
  unfold rankOneDistance
  rw [ha, show ‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * (inner ℂ x y).re = ‖x - y‖ ^ 2 by
    linarith [hn]]
  exact Real.sqrt_sq (norm_nonneg _)

/-- A vector and its negative have rank one distance zero. -/
theorem rankOneDistance_neg (x : E) : rankOneDistance x (-x) = 0 := by
  unfold rankOneDistance
  simp only [inner_neg_right, norm_neg, inner_self_eq_norm_sq_to_K, norm_pow]
  simp only [RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg x)]
  rw [show ‖x‖ ^ 2 + ‖x‖ ^ 2 - 2 * ‖x‖ ^ 2 = 0 by ring, Real.sqrt_zero]

/-- An upper bound on vector error also bounds the rank one distance. -/
theorem rankOneDistance_of_error (x y : E) (ε : ℝ) (h : ‖x - y‖ ≤ ε) :
    rankOneDistance x y ≤ ε := (rankOneDistance_le_vector_error x y).trans h
end Qatlib.Papers.DysonSeries22.PureDistance
