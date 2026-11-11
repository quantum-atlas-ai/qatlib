/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Numerical bounds for relative-error composition

Elementary exponential, power, and cosine estimates support the partition-function error
analysis. In particular, `pow_one_add_le_exp` and `one_sub_mul_le_pow` bound products of
relative-error factors, while `abs_cos_sub_cos_le'` controls phase-to-ratio conversion. These
estimates form part of the partition-function scheme in [WocjanEtAl2009a].

## Main statements

* `pow_one_add_le_exp`: For nonnegative real `x`, the power `(1 + x) ^ n` is at most `exp (n *
  x)`.
* `abs_cos_sub_cos_le'`: The absolute difference of two cosine values is at most the absolute
  difference of their arguments.

## References

* [Wocjan et al., 2009][WocjanEtAl2009a]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PartitionFunc08.MainResults

/-- For nonnegative real `x`, the power `(1 + x) ^ n` is at most `exp (n * x)`. -/
theorem pow_one_add_le_exp {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (1 + x) ^ n ≤ Real.exp (↑n * x) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by linarith) (by simpa [add_comm] using Real.add_one_le_exp x) n

/-- For `0 ≤ x ≤ 1`, the exponential `exp x` is at most `1 + 2 * x`. -/
theorem exp_le_one_add_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ 1 + 2 * x := by
  have h := Real.exp_bound' hx0 hx1 (n := 1) (by norm_num)
  have h' : Real.exp x ≤ 1 + x * (1 + 1) := by simpa using h
  linarith

/-- For real `x ≤ 1`, the power `(1 - x) ^ n` is at least `1 - n * x`. -/
theorem one_sub_mul_le_pow {x : ℝ} (hx : x ≤ 1) (n : ℕ) :
    1 - ↑n * x ≤ (1 - x) ^ n := by
  have h := one_add_mul_le_pow (a := -x) (by linarith) n
  simpa [sub_eq_add_neg, mul_neg, neg_mul] using h

/-- The absolute difference of two cosine values is at most the absolute difference of their
arguments. -/
theorem abs_cos_sub_cos_le' (θ θ' : ℝ) :
    |Real.cos θ - Real.cos θ'| ≤ |θ - θ'| :=
  Real.abs_cos_sub_cos_le θ θ'

end Qatlib.Papers.PartitionFunc08.MainResults
