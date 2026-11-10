/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.EnergySpec09.MainResults.SuccessProbability
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath

open scoped BigOperators Classical

namespace Qatlib.Papers.EnergySpec09.MainResults

theorem success_prob_gt_nine_tenths_iff (o : ℂ) :
    (9 / 10 : ℝ) < ‖o‖ ^ 2 ↔ Real.sqrt (9 / 10 : ℝ) < ‖o‖ := by
  have h9 : (0 : ℝ) ≤ (9 / 10 : ℝ) := by norm_num
  rw [← Real.sqrt_lt_sqrt_iff h9]
  rw [Real.sqrt_sq (norm_nonneg o)]

theorem water_pes_success_prob_gt_nine_tenths {I : Type*} [Fintype I] [DecidableEq I]
    (target trial : ℝ → QState I)
    (hdata : ∀ a : ℝ, 0.5 ≤ a → a ≤ 10 →
      Real.sqrt (9 / 10 : ℝ) < ‖Inner (target a) (trial a)‖) :
    ∀ a : ℝ, 0.5 ≤ a → a ≤ 10 → (9 / 10 : ℝ) < ‖Inner (target a) (trial a)‖ ^ 2 := by
  intro a ha hb
  exact (success_prob_gt_nine_tenths_iff (Inner (target a) (trial a))).2 (hdata a ha hb)

end Qatlib.Papers.EnergySpec09.MainResults
