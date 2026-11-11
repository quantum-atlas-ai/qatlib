/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.ClockMinimumExecutor
import Qatlib.Concepts.AmplitudeSearch.Amplification.TiedGroupBounds

/-!
# Global minimum search

This module records the global minimum guarantee corresponding to Theorem 3.1 of [Ambainis2005].
The theorem `theorem31_global_minimum` shows that the source execution reaches a minimum with
probability at least one half at the stated timeout, whose explicit upper bound is proportional
to √N.

## Main statements

* `theorem31_global_minimum`: Bounds success and timeout for the source minimum search
  execution.

## References

* [Ambainis, 2005][Ambainis2005]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.AmplitudeSearch.InterruptMin
open Qatlib.Concepts.AmplitudeSearch.Amplification

namespace Qatlib.Papers.QSearchSurvey05.MainResults

/-- For a nonempty finite ordered table, source minimum search succeeds with probability at
least one half at `sourceTimeout` N, and this timeout is at most (45/2 + (112/5)/(log
2)²)√N. See [Ambainis2005]. -/
theorem theorem31_global_minimum {N : ℕ} {α : Type*} [LinearOrder α]
    (T : Fin N → α) (hN : 0 < N) :
    (1 / 2 : ℝ) ≤ sourceSuccess T hN (sourceTimeout N) ∧
      sourceTimeout N ≤
        ((45 / 2 : ℝ) + (112 / 5 : ℝ) / (Real.log 2) ^ 2) * Real.sqrt N := by
  exact ⟨(frontier1 T hN).1, sourceTimeout_le_sqrt N hN⟩

end Qatlib.Papers.QSearchSurvey05.MainResults
