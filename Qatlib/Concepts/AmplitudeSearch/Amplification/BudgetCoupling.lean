/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.Query
import Qatlib.Concepts.AmplitudeSearch.Amplification.MinimumBudget
import Qatlib.Concepts.AmplitudeSearch.Amplification.InitializedBudgetCoupling
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment
open Qatlib.Concepts.AmplitudeSearch.Amplification.SortedRankedTable
open Qatlib.Concepts.AmplitudeSearch.InterruptMin

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib
open Qatlib.Concepts.SearchStopping.GroverSuccess
open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib
variable {N : ℕ} {α : Type*} [LinearOrder α]

theorem minimumBudgetSuccess_step (T : Fin N → α) (hN1 : N ≠ 1)
    (budget : ℕ) (current : Fin N) :
    minimumBudgetSuccess T budget current =
      FiniteBudgetEval (strictMarked T current) (ExponentialSizes N) 0 budget
        (fun candidate remaining => if remaining < budget then
          minimumBudgetSuccess T remaining (checkedUpdate T current candidate) else 0)
        (fun _ => if ∀ j, T current ≤ T j then 1 else 0) := by
  rw [minimumBudgetSuccess, minimumBudgetEval_eq, if_neg hN1]
  rfl

theorem queryCompletion_le_actual_success (T : SortedRankedTable N α) (hN : 0 < N)
    (initial : Fin N) (budget : ℕ) :
    queryCompletion T.indexOfRank T.skip (T.skip.next initial) budget ≤
      minimumBudgetSuccess T.value budget (T.indexOfRank initial) := by
  simpa only [initializedBBHTLaw, Nat.zero_add, queryCompletion, queryBBHTLaw,
    minimumBudgetSuccess, minimumBudgetSuccessWithInit, minimumBudgetEval] using
      initializedCompletion_le_actual_success T hN 0 initial budget

end Qatlib.Concepts.AmplitudeSearch.Amplification
