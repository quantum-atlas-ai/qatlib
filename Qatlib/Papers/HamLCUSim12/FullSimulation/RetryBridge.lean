/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HamLCUSim12.LCUDeferred.SubtractionRetryTailHami
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section


set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.HamLCUSim12.FullSimulation
open Qatlib.Papers.HamLCUSim12.LCUDeferred

/-- Fixed arXiv:1202.5822v1, Lemma 11 Eq. (65), restricted form (frozen
`SubtractionRetryTail`): `3r` independent attempts each failing with probability at
most `1/2` fail more than `2r` times with Born probability at most `e^{−r/14}`.
The printed constant `13` is not derivable from the displayed Chernoff exponent
(≈ `0.0754 r` vs `r/13 ≈ 0.0769 r`); the frozen corrected constant `14` is used. -/
theorem lemma11_retry_tail : SubtractionRetryTail := subtractionRetryTail

/-- Fixed arXiv:1202.5822v1, Lemma 11 Eq. (64) (probability conclusion): if the retry
count satisfies `r ≥ 13 log(2/β)`, then the retry failure probability `e^{−r/13}` is at
most `β/2`.  This is the arithmetic used in Lemma 12 to split the failure budget. -/
theorem lemma11_failure_prob_of_retry (β : ℝ) (hβ : 0 < β) (r : ℕ)
    (hr : 13 * Real.log (2 / β) ≤ (r : ℝ)) :
    Real.exp (-(r : ℝ) / 13) ≤ β / 2 := by
  have hpos : 0 < 2 / β := by positivity
  have hle : Real.log (2 / β) ≤ (r : ℝ) / 13 := by linarith
  have hexp : -(r : ℝ) / 13 ≤ -Real.log (2 / β) := by linarith
  calc Real.exp (-(r : ℝ) / 13) ≤ Real.exp (-Real.log (2 / β)) := Real.exp_le_exp.mpr hexp
    _ = β / 2 := by
        rw [Real.exp_neg, Real.exp_log hpos]
        field_simp


end Qatlib.Papers.HamLCUSim12.FullSimulation
