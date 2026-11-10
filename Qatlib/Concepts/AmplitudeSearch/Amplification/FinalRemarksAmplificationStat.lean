/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.Basic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AmplitudeSearch.InterruptMin.PlannedRetry

open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment

open Qatlib.Concepts.LinearLearning.ConcisePipeline

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

open Qatlib
open scoped ENNReal

def FinalRemarksAmplification : Prop :=
  ∀ (N : ℕ) (hN : 0 < N) (α : Type) [LinearOrder α] (T : Fin N → α) (c : ℕ), 0 < c →
    ENNReal.ofReal (1 - (1 / 2 : ℝ) ^ c)
      ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (amplifiedMinimumPMF T hN c) (fun x => ∀ j, T x.1 ≤ T j) ∧
    ((1 - 1 / ((2 * c : ℕ) : ℝ)) : ℝ)
      ≤ chargedInitialSuccess T (c * chargedBudget N)

end Qatlib.Concepts.AmplitudeSearch.Amplification
