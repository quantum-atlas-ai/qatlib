/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.Taylor

/-!
# Quadratic local error of a curve Euler step

The theorem `curve_euler_error` bounds the remainder after the first-order Euler approximation
of a twice continuously differentiable curve on a compact interval. A single real constant
controls the error by the square of the distance from the initial time.

This estimate supplies local discretization control for the variational imaginary-time setting
of [McArdleTew2020].

## Main statements

* `curve_euler_error`: a uniform quadratic remainder bound on a compact time interval.

## References

* [McArdle and Tew, 2020][McArdleTew2020]
-/

set_option autoImplicit false
noncomputable section
open Set

namespace Qatlib.Concepts.ImaginaryFlow.LeastSquares

/-- A twice continuously differentiable curve on `[a,b]` with `a < b` and derivative `v` at `a`
differs from its Euler approximation by at most `C*(x-a)^2` throughout the interval for some
real constant `C`. -/
theorem curve_euler_error {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Θ : ℝ → E) (a b : ℝ) (hab : a < b)
    (hΘ : ContDiffOn ℝ 2 Θ (Icc a b)) (v : E) (hv : HasDerivAt Θ v a) :
    ∃ C : ℝ, ∀ x ∈ Icc a b, ‖Θ x - (Θ a + (x-a) • v)‖ ≤ C * (x-a)^2 := by
  obtain ⟨C, hC⟩ := exists_taylor_mean_remainder_bound (n := 1) hab.le hΘ
  have hd : derivWithin Θ (Icc a b) a = v :=
    hv.hasDerivWithinAt.derivWithin ((uniqueDiffOn_Icc hab) a (left_mem_Icc.mpr hab.le))
  refine ⟨C, fun x hx => ?_⟩
  have h := hC x hx
  simpa only [taylorWithinEval_succ, taylor_within_zero_eval, Nat.factorial_zero,
    Nat.cast_zero, zero_add, Nat.cast_one, mul_one, inv_one, one_mul, pow_one, iteratedDerivWithin_one, hd] using h

end Qatlib.Concepts.ImaginaryFlow.LeastSquares
