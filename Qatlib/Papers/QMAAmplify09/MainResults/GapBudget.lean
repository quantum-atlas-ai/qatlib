/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QMAAmplify09.MainResults.FastAmplification

@[expose] public section

/-!
# Uniform inverse-gap amplification budget

The square-root numerator in Eq. (25) is at most two over the full domain
of the completeness and soundness probabilities.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QMAAmplify09.MainResults

open Qatlib.Papers.QMAAmplify09.MainResults.Defs
open Qatlib.Papers.QMAAmplify09.MainResults.FastAmplification

/-- The scalar amplification budget is bounded by `20 π r / (a - b)` uniformly in the promise. -/
theorem amp_cost_le (P : PromiseBounds) (r : ℕ) :
    amplificationCost P r ≤ 20 * Real.pi * (r : ℝ) / (P.a - P.b) := by
  have ha : Real.sqrt P.a ≤ 1 := by simpa using Real.sqrt_le_sqrt P.a_le_one
  have hb : Real.sqrt P.b ≤ 1 := by simpa using Real.sqrt_le_sqrt P.b_le_one
  have hsum : Real.sqrt P.a + Real.sqrt P.b ≤ 2 := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 10 * Real.pi by positivity)
  have hr : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  apply (amplificationCost_le P r).trans
  apply div_le_div_of_nonneg_right _ P.gap_pos.le
  exact mul_le_mul_of_nonneg_right (by linarith) hr

end Qatlib.Papers.QMAAmplify09.MainResults
