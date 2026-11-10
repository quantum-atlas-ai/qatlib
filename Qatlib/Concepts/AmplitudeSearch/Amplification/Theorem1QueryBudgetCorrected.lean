/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.Theorem1QueryBudgetCorrected
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.AmplitudeSearch.InterruptMin.PlannedRetry

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment
open Qatlib.Concepts.AmplitudeSearch.InterruptMin

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

theorem theorem1QueryBudgetCorrected : Theorem1QueryBudgetCorrected := by
  refine ⟨?_, minimumQueryBudget_isBigO_sqrt⟩
  intro N hN α inst T
  exact ⟨minimum_initial_success_half T hN,
    (minimumInitialSuccess_bounds T hN _).2,
    fun current => minimumBudgetEval_one T hN _ current,
    fun current f g hfg => minimumBudgetEval_congr T _ current f g hfg,
    minimumQueryBudget_le N hN⟩

end Qatlib.Concepts.AmplitudeSearch.Amplification
