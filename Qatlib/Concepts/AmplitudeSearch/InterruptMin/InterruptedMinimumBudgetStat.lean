/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.InterruptedMinimumCore

/-!
# The interrupted minimum-search budget contract

This module defines `InterruptedMinimumBudget`, collecting the positivity, normalization,
support, and expectation laws for interrupted minimum search. The contract also records the
observation interface, comparison with atomic search, and success bounds at the charged budget.

Its one-half success clause formalizes a budgeted minimum-finding guarantee in the setting of
[DurrHoyer1996].

## Main statements

* `InterruptedMinimumBudget`: The contract collecting interrupted minimum-search probability
  laws, remaining-budget and minimum-preservation properties, partial-observation semantics,
  domination of atomic success, and success between one half and one at the charged budget.

## References

* [Dürr and Høyer, 1996][DurrHoyer1996]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AmplitudeSearch.InterruptMin.PlannedRetry

open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.SearchStopping.UnknownCount

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin

open Qatlib.Concepts.SearchStopping.GroverSuccess Qatlib.Concepts.SearchStopping.UnknownCount
open scoped ENNReal BigOperators Classical

/-- The contract collecting interrupted minimum-search probability laws, remaining-budget and
minimum-preservation properties, partial-observation semantics, domination of atomic
success, and success between one half and one at the charged budget. -/
def InterruptedMinimumBudget : Prop :=
  ∀ (N : ℕ) (hN : 0 < N) (α : Type) [LinearOrder α] (T : Fin N → α),

    (∀ (initialization budget : ℕ) (current : Fin N) (payoff : Fin N → ℕ → ℝ),
      (∀ i r, 0 ≤ payoff i r) →
      0 ≤ interruptedMinimumEvalWithInit T initialization budget current payoff) ∧
    (∀ (initialization budget : ℕ) (current : Fin N),
      interruptedMinimumEvalWithInit T initialization budget current (fun _ _ => 1) = 1) ∧

    (∀ (budget : ℕ) (current : Fin N) (x : Fin N × ℕ),
      x ∈ (interruptedMinimumPMFWithInit T (initCharge N) hN budget current).support →
      x.2 ≤ budget) ∧

    (∀ (budget : ℕ) (current : Fin N) (_hmin : ∀ j, T current ≤ T j) (x : Fin N × ℕ),
      x ∈ (interruptedMinimumPMFWithInit T (initCharge N) hN budget current).support →
      x.1 = current) ∧

    (∀ (budget : ℕ) (current : Fin N) (payoff : Fin N → ℕ → ℝ),
      (∀ i r, 0 ≤ payoff i r) →
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
        (interruptedMinimumPMFWithInit T (initCharge N) hN budget current)
        (fun x => ENNReal.ofReal (payoff x.1 x.2)) =
      ENNReal.ofReal
        (interruptedMinimumEvalWithInit T (initCharge N) budget current payoff)) ∧

    (∀ (current : Fin N) (j r : ℕ),
      (∑ i ∈ strictMarked T current, partialObsMass (strictMarked T current) j r i) =
      observedAcceptance
        (BitOracleOn fun x : Fin N => decide (x ∈ strictMarked T current))
        (interruptedSearchPhaseAttempt (strictMarked T current) j r)
        (WithMinus (Uniform (Fin N)))) ∧

    (∀ (budget : ℕ) (current : Fin N),
      minimumBudgetSuccessWithInit T (initCharge N) budget current ≤
      interruptedMinimumSuccessWithInit T (initCharge N) budget current) ∧

    ((1 / 2 : ℝ) ≤ interruptedChargedInitialSuccess T (chargedBudget N)) ∧
    (interruptedChargedInitialSuccess T (chargedBudget N) ≤ 1)

end Qatlib.Concepts.AmplitudeSearch.InterruptMin
