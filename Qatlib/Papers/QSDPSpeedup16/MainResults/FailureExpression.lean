/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section


/-! The scalar expression in the source SDP failure estimate.

The expression does not constrain a run or a probability distribution and
does not establish the source failure estimate.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QSDPSpeedup16.MainResults.FailureExpr

/-- The source polynomial-logarithmic-exponential failure-bound expression. -/
def theorem4FailureRHS (R δ : ℝ) (n m : ℕ) (ξ : ℝ) : ℝ :=
  (R / δ) ^ 18 * ((n : ℝ) * (m : ℝ)) ^ 10 *
    Real.exp (-(Real.log ((n : ℝ) * (m : ℝ))) ^ ξ)

end Qatlib.Papers.QSDPSpeedup16.MainResults.FailureExpr
