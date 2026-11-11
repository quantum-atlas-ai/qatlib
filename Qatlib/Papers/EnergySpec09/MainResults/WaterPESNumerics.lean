/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.EnergySpec09.MainResults.SuccessProbability

/-!
# Overlap thresholds along a water potential curve

This module translates the overlap threshold used in the water potential-energy-curve discussion
of [WangEtAl2008] into a squared-overlap threshold. The scalar equivalence
`success_prob_gt_nine_tenths_iff` uses the nonnegativity of a complex norm to relate a square to
its positive square-root threshold.

The theorem `water_pes_success_prob_gt_nine_tenths` applies this equivalence pointwise on the
interval `[0.5, 10]`. The overlap lower bound on this interval is an explicit hypothesis.

## Main statements

* `success_prob_gt_nine_tenths_iff`: `9 / 10 < ‖o‖ ^ 2` holds exactly when `sqrt (9 / 10) <
  ‖o‖`.
* `water_pes_success_prob_gt_nine_tenths`: supplied overlap bounds on the stated interval imply
  squared overlaps above `9 / 10`.

## References

* [Wang et al., 2008][WangEtAl2008]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath

open scoped BigOperators Classical

namespace Qatlib.Papers.EnergySpec09.MainResults

/-- A complex overlap has squared norm above `9 / 10` exactly when its norm is above `sqrt (9 /
10)`. This converts the threshold used in the water potential-curve discussion of
[WangEtAl2008]. -/
theorem success_prob_gt_nine_tenths_iff (o : ℂ) :
    (9 / 10 : ℝ) < ‖o‖ ^ 2 ↔ Real.sqrt (9 / 10 : ℝ) < ‖o‖ := by
  have h9 : (0 : ℝ) ≤ (9 / 10 : ℝ) := by norm_num
  rw [← Real.sqrt_lt_sqrt_iff h9]
  rw [Real.sqrt_sq (norm_nonneg o)]

/-- On the interval from `0.5` to `10`, supplied overlap norms above `sqrt (9 / 10)` imply
squared overlaps above `9 / 10`. The overlap data are hypotheses, expressing the threshold
reported for the water potential curve in [WangEtAl2008]. -/
theorem water_pes_success_prob_gt_nine_tenths {I : Type*} [Fintype I] [DecidableEq I]
    (target trial : ℝ → QState I)
    (hdata : ∀ a : ℝ, 0.5 ≤ a → a ≤ 10 →
      Real.sqrt (9 / 10 : ℝ) < ‖Inner (target a) (trial a)‖) :
    ∀ a : ℝ, 0.5 ≤ a → a ≤ 10 → (9 / 10 : ℝ) < ‖Inner (target a) (trial a)‖ ^ 2 := by
  intro a ha hb
  exact (success_prob_gt_nine_tenths_iff (Inner (target a) (trial a))).2 (hdata a ha hb)

end Qatlib.Papers.EnergySpec09.MainResults
