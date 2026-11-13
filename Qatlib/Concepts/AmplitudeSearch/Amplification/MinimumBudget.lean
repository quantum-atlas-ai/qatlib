/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.MinimumBudgetCore

/-!
# Minimum search with a finite budget

This module specializes the recursive minimum-search evaluator to zero initialization charge.
The evaluator `minimumBudgetEval` and its success indicator `minimumBudgetSuccess` describe a
finite-budget version of quantum minimum finding [DurrHoyer1996].

## Main statements

* `minimumBudgetEval_eq`: unfolds the BBHT search and checked-update recursion.
* `minimumBudgetEval_mono`: proves monotonicity in the terminal payoff.
* `minimumBudgetSuccess_of_minimum`: gives success probability one when the initial index is
  already a minimum.

## References

* [Dürr and Høyer, 1996][DurrHoyer1996]
* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment
open Qatlib.Concepts.AmplitudeSearch.InterruptMin

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib
open Qatlib.Concepts.SearchStopping.GroverSuccess
open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib
variable {N : ℕ} {α : Type*} [LinearOrder α]

/-- The finite-budget minimum-search payoff evaluator with zero initialization charge. -/
noncomputable def minimumBudgetEval (T : Fin N → α) (budget : ℕ) (current : Fin N)
    (payoff : Fin N → ℕ → ℝ) : ℝ :=
  minimumBudgetEvalWithInit T 0 budget current payoff

/-- The evaluator returns the terminal payoff for a singleton table; otherwise it performs a
finite-budget BBHT call and recurses on a checked update when the remaining budget is
strictly smaller. -/
theorem minimumBudgetEval_eq (T : Fin N → α) (budget : ℕ) (current : Fin N)
    (payoff : Fin N → ℕ → ℝ) :
    minimumBudgetEval T budget current payoff =
      if N = 1 then payoff current budget else
        FiniteBudgetEval (strictMarked T current) (ExponentialSizes N) 0 budget
          (fun candidate remaining => if remaining < budget then
            minimumBudgetEval T remaining (checkedUpdate T current candidate) payoff else 0)
          (fun remaining => payoff current remaining) := by
  unfold minimumBudgetEval
  rw [minimumBudgetEvalWithInit]
  simp only [Nat.zero_le, if_true, Nat.sub_zero, dite_eq_ite]

/-- A remaining budget strictly below `budget` satisfies `remaining + 1 ≤ budget`. -/
theorem minimum_success_budget_progress (budget remaining : ℕ) (h : remaining < budget) :
    remaining + 1 ≤ budget := h

/-- Nonnegative terminal payoffs give a nonnegative minimum-search evaluation on a nonempty
table. -/
theorem minimumBudgetEval_nonneg (T : Fin N → α) (hN : 0 < N)
    (budget : ℕ) (current : Fin N) (payoff : Fin N → ℕ → ℝ)
    (hp : ∀ i r, 0 ≤ payoff i r) : 0 ≤ minimumBudgetEval T budget current payoff :=
  minimumBudgetEvalWithInit_nonneg T 0 hN budget current payoff hp

/-- Terminal payoffs agreeing at all remaining budgets at most `budget` give the same
minimum-search evaluation. -/
theorem minimumBudgetEval_congr (T : Fin N → α) (budget : ℕ) (current : Fin N)
    (f g : Fin N → ℕ → ℝ) (hfg : ∀ i r, r ≤ budget → f i r = g i r) :
    minimumBudgetEval T budget current f = minimumBudgetEval T budget current g :=
  minimumBudgetEvalWithInit_congr T 0 budget current f g hfg

/-- The constant terminal payoff one evaluates to one on a nonempty table. -/
theorem minimumBudgetEval_one (T : Fin N → α) (hN : 0 < N)
    (budget : ℕ) (current : Fin N) :
    minimumBudgetEval T budget current (fun _ _ => 1) = 1 :=
  minimumBudgetEvalWithInit_one T 0 hN budget current

/-- Pointwise ordered terminal payoffs give ordered minimum-search evaluations on a nonempty
table. -/
theorem minimumBudgetEval_mono (T : Fin N → α) (hN : 0 < N)
    (budget : ℕ) (current : Fin N) (f g : Fin N → ℕ → ℝ)
    (hfg : ∀ i r, f i r ≤ g i r) :
    minimumBudgetEval T budget current f ≤ minimumBudgetEval T budget current g :=
  minimumBudgetEvalWithInit_mono T 0 hN budget current f g hfg

/-- With zero budget, the evaluator returns the payoff of the current index with zero remaining
budget. -/
theorem minimumBudgetEval_zero (T : Fin N → α) (hN : 0 < N)
    (current : Fin N) (payoff : Fin N → ℕ → ℝ) :
    minimumBudgetEval T 0 current payoff = payoff current 0 :=
  minimumBudgetEvalWithInit_zero T 0 hN current payoff

/-- The finite-budget minimum-search evaluation of the indicator that the returned index is a
global minimum. -/
noncomputable def minimumBudgetSuccess (T : Fin N → α) (budget : ℕ) (current : Fin N) : ℝ :=
  minimumBudgetEval T budget current (fun i _ => if ∀ j, T i ≤ T j then 1 else 0)

/-- The finite-budget minimum-search success value lies between zero and one on a nonempty
table. -/
theorem minimumBudgetSuccess_bounds (T : Fin N → α) (hN : 0 < N)
    (budget : ℕ) (current : Fin N) :
    0 ≤ minimumBudgetSuccess T budget current ∧ minimumBudgetSuccess T budget current ≤ 1 :=
  minimumBudgetSuccessWithInit_bounds T 0 hN budget current

/-- Starting from a global minimum gives success value one for every budget. -/
theorem minimumBudgetSuccess_of_minimum (T : Fin N → α) (hN : 0 < N)
    (budget : ℕ) (current : Fin N) (hmin : ∀ j, T current ≤ T j) :
    minimumBudgetSuccess T budget current = 1 :=
  minimumBudgetSuccessWithInit_of_minimum T 0 hN budget current hmin

end Qatlib.Concepts.AmplitudeSearch.Amplification
