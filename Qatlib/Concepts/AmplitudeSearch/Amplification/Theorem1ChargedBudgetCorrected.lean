/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.Theorem1ChargedBudgetCorrected

/-!
# Corrected charged-budget minimum-finding theorem

This module proves `theorem1ChargedBudgetCorrected`, packaging the corrected charged-budget
version of the minimum-finding guarantee associated with [DurrHoyer1996]. The statement combines
success probability at least one half, normalized budgeted evaluation, dependence only on
payoffs within the budget, and an explicit square-root bound on the charged budget.

## Main statements

* `theorem1ChargedBudgetCorrected`: establishes `Theorem1ChargedBudgetCorrected`, including the
  asymptotic square-root budget bound.

## References

* [Dürr and Høyer, 1996][DurrHoyer1996]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.AmplitudeSearch.InterruptMin.PlannedRetry

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment
open Qatlib.Concepts.AmplitudeSearch.InterruptMin

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

/-- Establishes the corrected charged-budget minimum-finding guarantee: success at least one
half, normalized evaluation with the stated payoff congruence, and explicit and asymptotic
square-root budget bounds. This is the charged-budget formulation associated with Theorem 1
of [DurrHoyer1996]. -/
theorem theorem1ChargedBudgetCorrected : Theorem1ChargedBudgetCorrected := by
  refine ⟨?_, chargedBudget_isBigO_sqrt⟩
  intro N hN α inst T
  exact ⟨charged_initial_success_half T hN,
    (chargedInitialSuccess_bounds T hN _).2,
    fun current => minimumBudgetEvalWithInit_one T (initCharge N) hN _ current,
    fun current f g hfg => minimumBudgetEvalWithInit_congr T (initCharge N) _ current f g hfg,
    chargedBudget_le_sqrt N hN⟩

end Qatlib.Concepts.AmplitudeSearch.Amplification
