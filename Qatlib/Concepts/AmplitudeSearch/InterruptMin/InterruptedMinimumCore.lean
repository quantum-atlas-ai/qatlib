/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.InterruptedCallBudget
import Qatlib.Concepts.AmplitudeSearch.Amplification.MinimumBudgetProbability

/-!
# Recursive interrupted minimum-search laws

This module defines interrupted minimum-search evaluators and probability laws with an explicit
initialization charge. The recursion checks candidate updates and continues only when the
remaining budget decreases.

The uniformly initialized constructions use `initCharge N` for the charged-budget analysis of
minimum finding [DurrHoyer1996].

## Main statements

* `interruptedMinimumPMFWithInit`: The interrupted minimum-search law on the final index and
  remaining budget with an explicit initialization charge.
* `interruptedChargedInitialSuccess`: The average interrupted minimum-search success over all
  initial indices, using initialization charge `initCharge N`.

## References

* [Dürr and Høyer, 1996][DurrHoyer1996]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib.Concepts.SearchStopping.UnknownCount

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin

open Qatlib.Concepts.SearchStopping.GroverSuccess Qatlib.Concepts.SearchStopping.UnknownCount
open scoped ENNReal BigOperators Classical

variable {N : ℕ} {α : Type*} [LinearOrder α]

/-- The recursive minimum-search payoff evaluator with an explicit initialization charge and
partial observations at interrupted calls. -/
noncomputable def interruptedMinimumEvalWithInit (T : Fin N → α)
    (initialization budget : ℕ) (current : Fin N) (payoff : Fin N → ℕ → ℝ) : ℝ :=
  if N = 1 then payoff current budget else
    if initialization ≤ budget then
      interruptedBudgetEval (strictMarked T current) (ExponentialSizes N) 0
        (budget - initialization)
        (fun candidate remaining => if _hr : remaining < budget then
          interruptedMinimumEvalWithInit T initialization remaining
            (checkedUpdate T current candidate) payoff
        else payoff (checkedUpdate T current candidate) remaining)
    else payoff current budget
termination_by budget

/-- The interrupted minimum-search evaluator applied to the indicator of returning a global
minimum. -/
noncomputable def interruptedMinimumSuccessWithInit (T : Fin N → α)
    (initialization budget : ℕ) (current : Fin N) : ℝ :=
  interruptedMinimumEvalWithInit T initialization budget current
    (fun i _ => if ∀ j, T i ≤ T j then 1 else 0)

/-- The interrupted minimum-search law on the final index and remaining budget with an explicit
initialization charge. -/
noncomputable def interruptedMinimumPMFWithInit (T : Fin N → α) (initialization : ℕ)
    (hN : 0 < N) (budget : ℕ) (current : Fin N) : PMF (Fin N × ℕ) :=
  if N = 1 then PMF.pure (current, budget) else
    if initialization ≤ budget then
      (interruptedBudgetPMF (by simpa using! hN) (strictMarked T current) (ExponentialSizes N)
        (search_exponential_schedule N hN).2.1 0 (budget - initialization)).bind fun x =>
        if _hr : x.2 < budget then
          interruptedMinimumPMFWithInit T initialization hN x.2
            (checkedUpdate T current x.1)
        else PMF.pure (checkedUpdate T current x.1, x.2)
    else PMF.pure (current, budget)
termination_by budget

/-- The average interrupted minimum-search success over all initial indices, using
initialization charge `initCharge N`. -/
noncomputable def interruptedChargedInitialSuccess (T : Fin N → α) (budget : ℕ) : ℝ :=
  (∑ current : Fin N,
    interruptedMinimumSuccessWithInit T (initCharge N) budget current) / (N : ℝ)

/-- The interrupted minimum-search law with a uniformly sampled initial index and initialization
charge `initCharge N`. -/
noncomputable def interruptedChargedInitialPMF (T : Fin N → α) (hN : 0 < N)
    (budget : ℕ) : PMF (Fin N × ℕ) :=
  (iterationPMF N hN).bind (interruptedMinimumPMFWithInit T (initCharge N) hN budget)

end Qatlib.Concepts.AmplitudeSearch.InterruptMin
