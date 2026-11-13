/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.Theorem1QueryBudgetCorrected

/-!
# Corrected query-budget minimum-finding theorem

This module proves `theorem1QueryBudgetCorrected`, packaging the corrected query-budget
minimum-finding guarantee in the setting of [DurrHoyer1996]. For nonempty tables, the statement
combines success probability at least one half, normalized budgeted evaluation, dependence only
on payoffs within the budget, and a query budget bounded by `59 * Real.sqrt N` and
asymptotically by `O(√N)`.

## Main statements

* `theorem1QueryBudgetCorrected`: establishes the bundled proposition
  `Theorem1QueryBudgetCorrected`.

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

/-- Establishes the corrected query-budget minimum-finding guarantee: success at least one half,
normalized evaluation with the stated payoff congruence, and a budget at most `59 *
Real.sqrt N` growing as `O(√N)`. This is a query-budget formulation of the minimum-finding
guarantee in [DurrHoyer1996]. -/
theorem theorem1QueryBudgetCorrected : Theorem1QueryBudgetCorrected := by
  refine ⟨?_, minimumQueryBudget_isBigO_sqrt⟩
  intro N hN α inst T
  exact ⟨minimum_initial_success_half T hN,
    (minimumInitialSuccess_bounds T hN _).2,
    fun current => minimumBudgetEval_one T hN _ current,
    fun current f g hfg => minimumBudgetEval_congr T _ current f g hfg,
    minimumQueryBudget_le N hN⟩

end Qatlib.Concepts.AmplitudeSearch.Amplification
