/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.ClockMinimumExecutor
import Qatlib.Concepts.AmplitudeSearch.Amplification.TiedGroupBounds

/-!
# Original minimum-search deadline

Exact source-deadline bounds for the finite minimum-search execution.
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib.Concepts.AmplitudeSearch.InterruptMin
namespace Qatlib.Papers.QMinimum99.InterruptMin

/-- Exact printed source deadline, with no mean or successful-search premise. -/
theorem original_deadline_minimum {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) :
    (1 / 2 : ℝ) ≤ sourceSuccess T hN
      ((45 / 2 : ℝ) * Real.sqrt N + (7 / 5 : ℝ) * (binaryLog N)^2) := by
  exact source_timeout_half T hN
/-- The successful event is measured against the same normalized actual finite execution. -/
theorem original_deadline_actual_output {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) :
    (1 / 2 : ℝ) ≤ (expectation (sourceInitialPMF T hN (sourceTimeout N))
      (fun i => if ∀ j, T i ≤ T j then 1 else 0)).toReal := by
  simpa only [sourceSuccess, sourceInitialEval_eq_expectation] using source_timeout_half T hN

end Qatlib.Papers.QMinimum99.InterruptMin
