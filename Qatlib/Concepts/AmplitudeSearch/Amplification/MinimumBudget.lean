/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.MinimumBudgetCore
set_option warningAsError false
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

noncomputable def minimumBudgetEval (T : Fin N → α) (budget : ℕ) (current : Fin N)
    (payoff : Fin N → ℕ → ℝ) : ℝ :=
  minimumBudgetEvalWithInit T 0 budget current payoff

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

theorem minimum_success_budget_progress (budget remaining : ℕ) (h : remaining < budget) :
    remaining + 1 ≤ budget := h

theorem minimumBudgetEval_nonneg (T : Fin N → α) (hN : 0 < N)
    (budget : ℕ) (current : Fin N) (payoff : Fin N → ℕ → ℝ)
    (hp : ∀ i r, 0 ≤ payoff i r) : 0 ≤ minimumBudgetEval T budget current payoff :=
  minimumBudgetEvalWithInit_nonneg T 0 hN budget current payoff hp

theorem minimumBudgetEval_congr (T : Fin N → α) (budget : ℕ) (current : Fin N)
    (f g : Fin N → ℕ → ℝ) (hfg : ∀ i r, r ≤ budget → f i r = g i r) :
    minimumBudgetEval T budget current f = minimumBudgetEval T budget current g :=
  minimumBudgetEvalWithInit_congr T 0 budget current f g hfg

theorem minimumBudgetEval_one (T : Fin N → α) (hN : 0 < N)
    (budget : ℕ) (current : Fin N) :
    minimumBudgetEval T budget current (fun _ _ => 1) = 1 :=
  minimumBudgetEvalWithInit_one T 0 hN budget current

theorem minimumBudgetEval_mono (T : Fin N → α) (hN : 0 < N)
    (budget : ℕ) (current : Fin N) (f g : Fin N → ℕ → ℝ)
    (hfg : ∀ i r, f i r ≤ g i r) :
    minimumBudgetEval T budget current f ≤ minimumBudgetEval T budget current g :=
  minimumBudgetEvalWithInit_mono T 0 hN budget current f g hfg

theorem minimumBudgetEval_zero (T : Fin N → α) (hN : 0 < N)
    (current : Fin N) (payoff : Fin N → ℕ → ℝ) :
    minimumBudgetEval T 0 current payoff = payoff current 0 :=
  minimumBudgetEvalWithInit_zero T 0 hN current payoff

noncomputable def minimumBudgetSuccess (T : Fin N → α) (budget : ℕ) (current : Fin N) : ℝ :=
  minimumBudgetEval T budget current (fun i _ => if ∀ j, T i ≤ T j then 1 else 0)

theorem minimumBudgetSuccess_bounds (T : Fin N → α) (hN : 0 < N)
    (budget : ℕ) (current : Fin N) :
    0 ≤ minimumBudgetSuccess T budget current ∧ minimumBudgetSuccess T budget current ≤ 1 :=
  minimumBudgetSuccessWithInit_bounds T 0 hN budget current

theorem minimumBudgetSuccess_of_minimum (T : Fin N → α) (hN : 0 < N)
    (budget : ℕ) (current : Fin N) (hmin : ∀ j, T current ≤ T j) :
    minimumBudgetSuccess T budget current = 1 :=
  minimumBudgetSuccessWithInit_of_minimum T 0 hN budget current hmin

end Qatlib.Concepts.AmplitudeSearch.Amplification
