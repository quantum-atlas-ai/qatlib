/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.UnknownCount.SearchBudget

/-!
# Terminal trace bounds for finite search budgets

This module connects stagewise terminal search masses with the atomic finite-budget recursion.
It decomposes histories by their first attempt and bounds completed-prefix masses and full
fitting terminal masses by `FiniteBudgetMass`.

The accounting charges each attempt its iterations plus one checking query in the randomized
search framework [BoyerEtAl1998].

## Main statements

* `search_budget_terminal_row`: The stagewise terminal mass of traces fitting the Boolean-query
  budget and outputting `i` equals `BudgetCompletedRow`.
* `search_finite_budget_dominates_terminal`: The total terminal mass of traces fitting the
  Boolean-query budget and outputting `i` is bounded by the finite-budget success mass.
* `search_fitting_trace_finite`: A terminal trace fitting the Boolean-query budget has terminal
  stage strictly below that budget.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.SearchStopping.UnknownCount

namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin
open scoped BigOperators

/-- The attempt-size schedule shifted forward by one stage. -/
abbrev TailSizes (sizes : ℕ → ℕ) : ℕ → ℕ := fun k => sizes (k+1)

/-- Using the tail size schedule at a stage gives the finite-budget mass of the original
schedule at the next stage. -/
theorem search_finite_budget_shift {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (sizes : ℕ → ℕ) (stage budget : ℕ) (out : Option I) :
    FiniteBudgetMass A (TailSizes sizes) stage budget out =
      FiniteBudgetMass A sizes (stage+1) budget out := by
  induction budget using Nat.strong_induction_on generalizing stage with
  | h budget ih =>
    conv_lhs => rw [FiniteBudgetMass]
    conv_rhs => rw [FiniteBudgetMass]
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    by_cases hc : x.1.val+1 ≤ budget
    · simp only [dif_pos hc]
      cases hx : x.2 with
      | none => exact ih _ (search_budget_progress _ _ hc) (stage+1)
      | some i => rfl
    · simp only [dif_neg hc]

/-- Prepending a failed attempt factors the failure-history mass and adds its iteration count to
the history clock. -/
theorem search_history_head {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (sizes : ℕ → ℕ) (n : ℕ) (j : Fin (sizes 0))
    (h : TrialHistory (TailSizes sizes) n) :
    FailureHistoryMass A sizes (n+1) (Fin.cons j h) =
      AttemptMass A (sizes 0) (j,none) * FailureHistoryMass A (TailSizes sizes) n h ∧
    HistoryIterations sizes (n+1) (Fin.cons j h) =
      j.val + HistoryIterations (TailSizes sizes) n h := by
  constructor
  · rw [FailureHistoryMass, Fin.prod_univ_succ]
    simp [FailureHistoryMass, Fin.cons_succ, TailSizes]
  · rw [HistoryIterations, Fin.sum_univ_succ]
    simp [HistoryIterations, Fin.cons_succ, TailSizes]

/-- The mass of stage-`n` completions outputting `i` whose iteration and checking-query cost
fits the budget. -/
noncomputable def BudgetCompletedRow {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (sizes : ℕ → ℕ) (budget n : ℕ) (i : I) : ℝ :=
  ∑ h : TrialHistory sizes n, ∑ j : Fin (sizes n),
    if HistoryIterations sizes n h + j.val + (n+1) ≤ budget then
      FailureHistoryMass A sizes n h * AttemptMass A (sizes n) (j,some i)
    else 0

/-- The stage-zero completed mass is the sum of successful first-attempt masses whose
iteration-plus-check cost fits the budget. -/
theorem search_budget_row_zero {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (sizes : ℕ → ℕ) (budget : ℕ) (i : I) :
    BudgetCompletedRow A sizes budget 0 i =
      ∑ j : Fin (sizes 0), if j.val+1 ≤ budget then AttemptMass A (sizes 0) (j,some i) else 0 := by
  simp [BudgetCompletedRow, FailureHistoryMass, HistoryIterations]

/-- The next-stage completed mass factors through an affordable failed first attempt and the
shifted residual-budget process. -/
theorem search_budget_row_succ {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (sizes : ℕ → ℕ) (budget n : ℕ) (i : I) :
    BudgetCompletedRow A sizes budget (n+1) i =
      ∑ j : Fin (sizes 0), if j.val+1 ≤ budget then
        AttemptMass A (sizes 0) (j,none) *
          BudgetCompletedRow A (TailSizes sizes) (budget-(j.val+1)) n i
      else 0 := by
  let e := Fin.consEquiv (fun k : Fin (n+1) => Fin (sizes k.val))
  unfold BudgetCompletedRow
  rw [← e.sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  change (∑ h : TrialHistory (TailSizes sizes) n, ∑ k : Fin (sizes (n+1)),
    (if HistoryIterations sizes (n+1) (Fin.cons j h) + k.val + (n+1+1) ≤ budget then
      FailureHistoryMass A sizes (n+1) (Fin.cons j h) * AttemptMass A (sizes (n+1)) (k,some i)
    else 0)) = _
  simp_rw [(search_history_head A sizes n j _).1, (search_history_head A sizes n j _).2]
  by_cases hc : j.val+1 ≤ budget
  · rw [if_pos hc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have heq : j.val + HistoryIterations (TailSizes sizes) n h + k.val + (n+1+1) ≤ budget ↔
        HistoryIterations (TailSizes sizes) n h + k.val + (n+1) ≤ budget-(j.val+1) := by omega
    simp only [heq]
    split_ifs <;> ring
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro h _
    apply Finset.sum_eq_zero
    intro k _
    rw [if_neg (by omega)]

/-- The completed mass for output `i` summed over stages below `depth`. -/
noncomputable def BudgetCompletedPrefix {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (sizes : ℕ → ℕ) (budget depth : ℕ) (i : I) : ℝ :=
  ∑ n ∈ Finset.range depth, BudgetCompletedRow A sizes budget n i

/-- The completed-prefix recurrence splits into immediate success and continuation after an
affordable failed first attempt. -/
theorem search_budget_prefix_succ {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (sizes : ℕ → ℕ) (budget depth : ℕ) (i : I) :
    BudgetCompletedPrefix A sizes budget (depth+1) i =
      ∑ j : Fin (sizes 0), if j.val+1 ≤ budget then
        AttemptMass A (sizes 0) (j,some i) + AttemptMass A (sizes 0) (j,none) *
          BudgetCompletedPrefix A (TailSizes sizes) (budget-(j.val+1)) depth i
      else 0 := by
  unfold BudgetCompletedPrefix
  rw [Finset.sum_range_succ', search_budget_row_zero]
  simp_rw [search_budget_row_succ]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hc : j.val+1 ≤ budget
  · simp only [if_pos hc]
    rw [← Finset.mul_sum]
    ring
  · simp [hc]

/-- The finite-budget success mass splits into immediate success and affordable-failure
continuation under the tail schedule. -/
theorem search_finite_budget_success_step {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (sizes : ℕ → ℕ) (budget : ℕ) (i : I) :
    FiniteBudgetMass A sizes 0 budget (some i) =
      ∑ j : Fin (sizes 0), if j.val+1 ≤ budget then
        AttemptMass A (sizes 0) (j,some i) + AttemptMass A (sizes 0) (j,none) *
          FiniteBudgetMass A (TailSizes sizes) 0 (budget-(j.val+1)) (some i)
      else 0 := by
  conv_lhs => rw [FiniteBudgetMass]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  rw [search_finite_budget_shift]
  by_cases hc : j.val+1 ≤ budget
  · simp only [dif_pos hc, if_pos hc]
    rw [Fintype.sum_option]
    simp [mul_ite, add_comm]
  · simp [hc]

/-- Every finite completed-prefix mass is bounded by the finite-budget success mass. -/
theorem search_budget_prefix_le {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (sizes : ℕ → ℕ)
    (hsizes : ∀ k, 0 < sizes k) (budget depth : ℕ) (i : I) :
    BudgetCompletedPrefix A sizes budget depth i ≤ FiniteBudgetMass A sizes 0 budget (some i) := by
  induction depth generalizing sizes budget with
  | zero =>
    simpa only [BudgetCompletedPrefix, Finset.range_zero, Finset.sum_empty] using
      (search_finite_budget_law hN A sizes hsizes 0 budget).1 (some i)
  | succ depth ih =>
    rw [search_budget_prefix_succ, search_finite_budget_success_step]
    apply Finset.sum_le_sum
    intro j _
    by_cases hc : j.val+1 ≤ budget
    · rw [if_pos hc, if_pos hc]
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left
      · exact ih (TailSizes sizes) (fun k => hsizes (k+1)) (budget-(j.val+1))
      · exact (search_joint_attempt_law hN A (sizes 0) (hsizes 0)).1 (j,none)
    · rw [if_neg hc, if_neg hc]

/-- The stagewise terminal mass of traces fitting the Boolean-query budget and outputting `i`
equals `BudgetCompletedRow`. -/
theorem search_budget_terminal_row {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (sizes : ℕ → ℕ) (budget n : ℕ) (i : I) :
    (∑ x : TerminalStage I sizes n,
      if TerminalBooleanQueries sizes ⟨n,x⟩ ≤ budget ∧ TerminalOutput ⟨n,x⟩ = i
      then TerminalMass A sizes ⟨n,x⟩ else 0) = BudgetCompletedRow A sizes budget n i := by
  simp only [TerminalBooleanQueries, TerminalCost, TerminalIterations, TerminalOutput,
    TerminalMass, TerminalStageMass, BudgetCompletedRow, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hc : HistoryIterations sizes n h + j.val + (n+1) ≤ budget
  · simp [hc]
  · simp [hc]

/-- The total terminal mass of traces fitting the Boolean-query budget and outputting `i` is
bounded by the finite-budget success mass. -/
theorem search_finite_budget_dominates_terminal {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (sizes : ℕ → ℕ)
    (hsizes : ∀ k, 0 < sizes k) (budget : ℕ) (i : I) :
    (∑' x : TerminalTrace I sizes,
      if TerminalBooleanQueries sizes x ≤ budget ∧ TerminalOutput x = i
      then TerminalMass A sizes x else 0) ≤ FiniteBudgetMass A sizes 0 budget (some i) := by
  have hn (x : TerminalTrace I sizes) :
      0 ≤ (if TerminalBooleanQueries sizes x ≤ budget ∧ TerminalOutput x = i
        then TerminalMass A sizes x else 0) := by
    split_ifs
    · exact ((search_terminal_stage_law hN A sizes hsizes x.1).1 x.2).1
    · exact le_rfl
  have hrow (n : ℕ) : 0 ≤ BudgetCompletedRow A sizes budget n i := by
    rw [← search_budget_terminal_row]
    exact Finset.sum_nonneg (fun x _ => hn ⟨n,x⟩)
  have hb (depth : ℕ) : (∑ n ∈ Finset.range depth, BudgetCompletedRow A sizes budget n i) ≤
      FiniteBudgetMass A sizes 0 budget (some i) := search_budget_prefix_le hN A sizes hsizes budget depth i
  have hs := summable_of_sum_range_le hrow hb
  have hflat : HasSum (fun x : TerminalTrace I sizes =>
      if TerminalBooleanQueries sizes x ≤ budget ∧ TerminalOutput x = i
      then TerminalMass A sizes x else 0) (∑' n, BudgetCompletedRow A sizes budget n i) := by
    apply search_nonnegative_trace_sum _ hn
    simp_rw [search_budget_terminal_row]
    exact hs.hasSum
  rw [hflat.tsum_eq]
  exact hs.tsum_le_of_sum_range_le hb

/-- A terminal trace fitting the Boolean-query budget has terminal stage strictly below that
budget. -/
theorem search_fitting_trace_finite {I : Type*} (sizes : ℕ → ℕ)
    (budget : ℕ) (x : TerminalTrace I sizes)
    (hx : TerminalBooleanQueries sizes x ≤ budget) : x.1 < budget := by
  unfold TerminalBooleanQueries at hx
  omega

end Qatlib.Concepts.AmplitudeSearch.InterruptMin
