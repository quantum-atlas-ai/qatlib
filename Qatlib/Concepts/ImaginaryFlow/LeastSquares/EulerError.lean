/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.Taylor

set_option autoImplicit false
noncomputable section
open Set

namespace Qatlib.Concepts.ImaginaryFlow.LeastSquares

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
