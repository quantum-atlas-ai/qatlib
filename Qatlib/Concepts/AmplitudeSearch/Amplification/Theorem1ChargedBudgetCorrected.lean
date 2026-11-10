/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.Theorem1ChargedBudgetCorrected
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.AmplitudeSearch.InterruptMin.PlannedRetry

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment
open Qatlib.Concepts.AmplitudeSearch.InterruptMin

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

theorem theorem1ChargedBudgetCorrected : Theorem1ChargedBudgetCorrected := by
  refine ⟨?_, chargedBudget_isBigO_sqrt⟩
  intro N hN α inst T
  exact ⟨charged_initial_success_half T hN,
    (chargedInitialSuccess_bounds T hN _).2,
    fun current => minimumBudgetEvalWithInit_one T (initCharge N) hN _ current,
    fun current f g hfg => minimumBudgetEvalWithInit_congr T (initCharge N) _ current f g hfg,
    chargedBudget_le_sqrt N hN⟩

end Qatlib.Concepts.AmplitudeSearch.Amplification
