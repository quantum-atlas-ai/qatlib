/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.Basic

/-!
# The minimum-finding amplification specification

`FinalRemarksAmplification` states the success guarantees for a nonempty table and positive
repetition count: combining charged runs gives success at least `1 - 2⁻ᶜ`, and extending the
charged budget by `c` gives success at least `1 - 1 / (2 * c)`.

The predicate records the two amplification bounds motivated by the final remarks of
[DurrHoyer1996].

## Main statements

* `FinalRemarksAmplification`: packages repeated-run and extended-budget success bounds.

## References

* [Durr and Hoyer, 1996][DurrHoyer1996]
-/

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

/-- The minimum-finding amplification statement: for positive `c`, repeated charged runs succeed
with probability at least `1 - 2⁻ᶜ`, and a `c`-fold charged budget gives initial success at
least `1 - 1 / (2 * c)`. -/
def FinalRemarksAmplification : Prop :=
  ∀ (N : ℕ) (hN : 0 < N) (α : Type) [LinearOrder α] (T : Fin N → α) (c : ℕ), 0 < c →
    ENNReal.ofReal (1 - (1 / 2 : ℝ) ^ c)
      ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (amplifiedMinimumPMF T hN c) (fun x => ∀ j, T x.1 ≤ T j) ∧
    ((1 - 1 / ((2 * c : ℕ) : ℝ)) : ℝ)
      ≤ chargedInitialSuccess T (c * chargedBudget N)

end Qatlib.Concepts.AmplitudeSearch.Amplification
