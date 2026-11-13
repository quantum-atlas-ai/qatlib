/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.BBHTCall
import Qatlib.Concepts.AmplitudeSearch.InterruptMin.SearchBudgetProbability

/-!
# Recursive minimum search with initialization costs

This module defines `strictMarked` and the evaluator `minimumBudgetEvalWithInit`, which charges
initialization before each BBHT call and recurses after a strict improvement. These definitions
give finite-budget payoff semantics for the minimum-search procedure of [DurrHoyer1996].

The evaluator preserves nonnegative payoffs, the constant payoff one, and pointwise payoff
inequalities. Its minimum indicator `minimumBudgetSuccessWithInit` lies in the unit interval and
equals one from an initial minimum.

## Main statements

* `minimumBudgetEvalWithInit`: evaluates terminal payoffs with an explicit initialization
  charge.
* `minimumBudgetEvalWithInit_mono`: compares ordered terminal payoffs.
* `minimumBudgetSuccessWithInit_bounds`: bounds the success value between zero and one.

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

/-- The finite set of indices whose table values are strictly smaller than the current value. -/
def strictMarked (T : Fin N → α) (current : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun i => T i < T current)

/-- Recursive payoff semantics for finite-budget minimum search, charging `initialization`
before each BBHT call and continuing after a checked improvement with smaller remaining
budget [DurrHoyer1996]. A singleton table or an unaffordable initialization returns the
current terminal payoff. -/
noncomputable def minimumBudgetEvalWithInit (T : Fin N → α) (initialization budget : ℕ)
    (current : Fin N) (payoff : Fin N → ℕ → ℝ) : ℝ :=
  if N = 1 then payoff current budget else
    if initialization ≤ budget then
      FiniteBudgetEval (strictMarked T current) (ExponentialSizes N) 0 (budget - initialization)
        (fun candidate remaining => if _hr : remaining < budget then
          minimumBudgetEvalWithInit T initialization remaining (checkedUpdate T current candidate) payoff
          else 0)
        (fun remaining => payoff current remaining)
    else payoff current budget
termination_by budget

/-- Nonnegative terminal payoffs give a nonnegative evaluation with initialization charges on a
nonempty table. -/
theorem minimumBudgetEvalWithInit_nonneg (T : Fin N → α) (initialization : ℕ) (hN : 0 < N)
    (budget : ℕ) (current : Fin N) (payoff : Fin N → ℕ → ℝ)
    (hp : ∀ i r, 0 ≤ payoff i r) :
    0 ≤ minimumBudgetEvalWithInit T initialization budget current payoff := by
  induction budget using Nat.strong_induction_on generalizing current with
  | h budget ih =>
    rw [minimumBudgetEvalWithInit]
    split_ifs with hsingle hpaid
    · exact hp _ _
    · apply search_finite_budget_eval_nonneg (by simpa using hN) _ _
        (search_exponential_schedule N hN).2.1
      · intro i r
        split_ifs with hr
        · exact ih r hr _
        · exact le_rfl
      · exact fun r => hp current r
    · exact hp _ _

/-- Payoffs agreeing at all remaining budgets at most the initial budget give equal evaluations
with initialization charges. -/
theorem minimumBudgetEvalWithInit_congr (T : Fin N → α) (initialization budget : ℕ)
    (current : Fin N) (f g : Fin N → ℕ → ℝ)
    (hfg : ∀ i r, r ≤ budget → f i r = g i r) :
    minimumBudgetEvalWithInit T initialization budget current f =
      minimumBudgetEvalWithInit T initialization budget current g := by
  induction budget using Nat.strong_induction_on generalizing current with
  | h budget ih =>
    conv_lhs => rw [minimumBudgetEvalWithInit]
    conv_rhs => rw [minimumBudgetEvalWithInit]
    by_cases hsingle : N = 1
    · simp only [if_pos hsingle]
      exact hfg current budget le_rfl
    · simp only [if_neg hsingle]
      by_cases hpaid : initialization ≤ budget
      · simp only [if_pos hpaid]
        apply search_finite_budget_eval_congr
        · intro i r hr
          have hrB : r < budget := lt_of_lt_of_le hr (Nat.sub_le _ _)
          simp only [dif_pos hrB]
          exact ih r hrB _ (fun j s hs => hfg j s (le_trans hs hrB.le))
        · intro r hr
          exact hfg current r (le_trans hr (Nat.sub_le _ _))
      · simp only [if_neg hpaid]
        exact hfg current budget le_rfl

/-- The evaluator with initialization charges preserves the constant payoff one on a nonempty
table. -/
theorem minimumBudgetEvalWithInit_one (T : Fin N → α) (initialization : ℕ) (hN : 0 < N)
    (budget : ℕ) (current : Fin N) :
    minimumBudgetEvalWithInit T initialization budget current (fun _ _ => 1) = 1 := by
  induction budget using Nat.strong_induction_on generalizing current with
  | h budget ih =>
    rw [minimumBudgetEvalWithInit]
    split_ifs with hsingle hpaid
    · rfl
    · calc
        _ = FiniteBudgetEval (strictMarked T current) (ExponentialSizes N) 0
            (budget - initialization) (fun _ _ => 1) (fun _ => 1) := by
          apply search_finite_budget_eval_congr
          · intro i r hr
            have hrB : r < budget := lt_of_lt_of_le hr (Nat.sub_le _ _)
            simp only [dif_pos hrB]
            exact ih r hrB _
          · intros; rfl
        _ = 1 := search_finite_budget_eval_one (by simpa using hN) _ _
          (search_exponential_schedule N hN).2.1 _ _
    · rfl

/-- The finite-budget BBHT evaluator is monotone in both its successful and stopping
continuation payoffs when the table and all schedule widths are positive. -/
private theorem bbhtEval_mono {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (sizes : ℕ → ℕ) (hsizes : ∀ k, 0 < sizes k)
    (stage budget : ℕ) (f g : I → ℕ → ℝ) (s t : ℕ → ℝ)
    (hfg : ∀ i r, f i r ≤ g i r) (hst : ∀ r, s r ≤ t r) :
    FiniteBudgetEval A sizes stage budget f s ≤ FiniteBudgetEval A sizes stage budget g t :=
  search_finite_budget_eval_mono hN A sizes hsizes stage budget f g s t hfg hst

/-- Pointwise ordered terminal payoffs give ordered evaluations with initialization charges on a
nonempty table. -/
theorem minimumBudgetEvalWithInit_mono (T : Fin N → α) (initialization : ℕ) (hN : 0 < N)
    (budget : ℕ) (current : Fin N) (f g : Fin N → ℕ → ℝ) (hfg : ∀ i r, f i r ≤ g i r) :
    minimumBudgetEvalWithInit T initialization budget current f ≤
      minimumBudgetEvalWithInit T initialization budget current g := by
  induction budget using Nat.strong_induction_on generalizing current with
  | h budget ih =>
    conv_lhs => rw [minimumBudgetEvalWithInit]
    conv_rhs => rw [minimumBudgetEvalWithInit]
    by_cases hsingle : N = 1
    · simp only [if_pos hsingle]
      exact hfg current budget
    · simp only [if_neg hsingle]
      by_cases hpaid : initialization ≤ budget
      · simp only [if_pos hpaid]
        apply bbhtEval_mono (by simpa using hN) _ _ (search_exponential_schedule N hN).2.1
        · intro i r
          by_cases hr : r < budget
          · simp only [dif_pos hr]
            exact ih r hr _
          · simp only [dif_neg hr]
            exact le_rfl
        · intro r; exact hfg current r
      · simp only [if_neg hpaid]
        exact hfg current budget

/-- At zero budget, evaluation with any initialization charge returns the current payoff with
zero remaining budget. -/
theorem minimumBudgetEvalWithInit_zero (T : Fin N → α) (initialization : ℕ) (hN : 0 < N)
    (current : Fin N) (payoff : Fin N → ℕ → ℝ) :
    minimumBudgetEvalWithInit T initialization 0 current payoff = payoff current 0 := by
  rw [minimumBudgetEvalWithInit]
  split_ifs with hsingle hpaid
  · rfl
  · simp only [Nat.zero_sub]
    rw [FiniteBudgetEval]
    have hc (x : Fin (ExponentialSizes N 0) × Option (Fin N)) : ¬ x.1.val + 1 ≤ 0 := by omega
    simp only [hc, dite_false]
    rw [← Finset.sum_mul]
    rw [(search_joint_attempt_law (by simpa using hN) (strictMarked T current)
      (ExponentialSizes N 0) ((search_exponential_schedule N hN).2.1 0)).2.1]
    exact one_mul _
  · rfl

/-- The minimum-search success value obtained by evaluating the global-minimum indicator with an
explicit initialization charge. -/
noncomputable def minimumBudgetSuccessWithInit (T : Fin N → α) (initialization budget : ℕ)
    (current : Fin N) : ℝ :=
  minimumBudgetEvalWithInit T initialization budget current
    (fun i _ => if ∀ j, T i ≤ T j then 1 else 0)

/-- The success value with initialization charges lies in the unit interval for a nonempty
table. -/
theorem minimumBudgetSuccessWithInit_bounds (T : Fin N → α) (initialization : ℕ) (hN : 0 < N)
    (budget : ℕ) (current : Fin N) :
    0 ≤ minimumBudgetSuccessWithInit T initialization budget current ∧
      minimumBudgetSuccessWithInit T initialization budget current ≤ 1 := by
  constructor
  · exact minimumBudgetEvalWithInit_nonneg T initialization hN budget current _
      (fun _ _ => by split_ifs <;> norm_num)
  · unfold minimumBudgetSuccessWithInit
    calc
      _ ≤ minimumBudgetEvalWithInit T initialization budget current (fun _ _ => 1) :=
        minimumBudgetEvalWithInit_mono T initialization hN budget current _ _
          (fun _ _ => by split_ifs <;> norm_num)
      _ = 1 := minimumBudgetEvalWithInit_one T initialization hN budget current

/-- An initial global minimum gives success value one with any budget and initialization charge. -/
theorem minimumBudgetSuccessWithInit_of_minimum (T : Fin N → α) (initialization : ℕ) (hN : 0 < N)
    (budget : ℕ) (current : Fin N) (hmin : ∀ j, T current ≤ T j) :
    minimumBudgetSuccessWithInit T initialization budget current = 1 := by
  induction budget using Nat.strong_induction_on generalizing current with
  | h budget ih =>
    unfold minimumBudgetSuccessWithInit
    rw [minimumBudgetEvalWithInit]
    by_cases hsingle : N = 1
    · rw [if_pos hsingle, if_pos hmin]
    · rw [if_neg hsingle]
      by_cases hpaid : initialization ≤ budget
      · rw [if_pos hpaid]
        calc
          _ = FiniteBudgetEval (strictMarked T current) (ExponentialSizes N) 0
              (budget - initialization) (fun _ _ => 1) (fun _ => 1) := by
            apply search_finite_budget_eval_congr
            · intro i r hr
              have hrB : r < budget := lt_of_lt_of_le hr (Nat.sub_le _ _)
              simp only [dif_pos hrB, checkedUpdate_preserves_minimum T current i hmin]
              exact ih r hrB current hmin
            · intro r hr
              exact if_pos hmin
          _ = 1 := search_finite_budget_eval_one (by simpa using hN) _ _
            (search_exponential_schedule N hN).2.1 _ _
      · rw [if_neg hpaid, if_pos hmin]

end Qatlib.Concepts.AmplitudeSearch.Amplification
