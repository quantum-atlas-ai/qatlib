/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.DysonSeries22.TimeSteps

@[expose] public section

/-!
# Factorial majorant for the local time-step defect

The defect already combines the homogeneous propagation error with the source
error. Substituting both factorial bounds controls their sum at the same grid step.
-/

set_option autoImplicit false

open Set
open scoped Matrix.Norms.L2Operator
open Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Papers.DysonSeries22.TimeSteps Qatlib.Papers.DysonSeries22.Truncation

namespace Qatlib.Papers.DysonSeries22.TimeSteps

/-- The two factorial tails bound the existing local defect on a single grid interval. -/
theorem localDefect_le_factorial {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I) (hA : Continuous A) (hb : Continuous b)
    (t : ℕ → ℝ) (K : ℕ) (y : ℕ → EuclideanSpace ℂ I) (n : ℕ)
    (M C : ℝ) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hBA : ∀ u ∈ uIcc (t n) (t (n + 1)), ‖A u‖ ≤ M)
    (hBb : ∀ u ∈ uIcc (t n) (t (n + 1)), ‖toEuclidean_fromVec (b u)‖ ≤ C) :
    localDefect A b t K y n ≤
      (M * |t (n + 1) - t n|) ^ (K + 1) / ((K + 1).factorial : ℝ) *
          Real.exp (M * |t (n + 1) - t n|) * ‖y n‖ +
        C * |t (n + 1) - t n| *
          ((M * |t (n + 1) - t n|) ^ K / ((K + 1).factorial : ℝ) *
            Real.exp (M * |t (n + 1) - t n|)) := by
  unfold localDefect exactDriving
  exact add_le_add (mul_le_mul_of_nonneg_right
    (evolution_error_factorial A hA _ _ M hM hBA K) (norm_nonneg _))
    (source_error_factorial A b hA hb _ _ M C hM hC hBA hBb K)

end Qatlib.Papers.DysonSeries22.TimeSteps
