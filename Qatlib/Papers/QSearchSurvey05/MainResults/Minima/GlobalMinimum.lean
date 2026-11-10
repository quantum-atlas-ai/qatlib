/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.ClockMinimumExecutor
import Qatlib.Concepts.AmplitudeSearch.Amplification.TiedGroupBounds
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.AmplitudeSearch.InterruptMin
open Qatlib.Concepts.AmplitudeSearch.Amplification

namespace Qatlib.Papers.QSearchSurvey05.MainResults

theorem theorem31_global_minimum {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) :
    (1 / 2 : ℝ) ≤ sourceSuccess T hN (sourceTimeout N) ∧
      sourceTimeout N ≤
        ((45 / 2 : ℝ) + (112 / 5 : ℝ) / (Real.log 2) ^ 2) * Real.sqrt N := by
  exact ⟨(frontier1 T hN).1, sourceTimeout_le_sqrt N hN⟩

end Qatlib.Papers.QSearchSurvey05.MainResults
