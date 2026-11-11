/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.SearchBudgetBridge
import Qatlib.Concepts.AmplitudeSearch.InterruptMin.SearchTerminal

/-!
# Rewards for search completion before a deadline

This module expresses nonnegative rewards for terminal search traces that finish strictly before
a query budget. `rewardRow` isolates a terminal stage and `rewardPrefix` sums finitely many such
stages.

The recurrence formulas split off the first randomized search attempt in the retry framework of
[BoyerEtAl1998].

## Main statements

* `rewardPrefix_succ`: The reward prefix at successor depth splits into immediate success and
  continuation after a failed first attempt.
* `rewardRow_terminal`: The payoff sum over terminal traces at stage `n` completing strictly
  before the budget equals `rewardRow`.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AmplitudeSearch.InterruptMin

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin
open Qatlib
open scoped Classical BigOperators ENNReal
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The expected payoff contributed by successful stage-`n` histories whose total iteration cost
is strictly below `budget`. -/
def rewardRow (A : Finset I) (sizes : ℕ → ℕ) (budget n : ℕ)
    (payoff : I × Option ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ h : TrialHistory sizes n, ∑ j : Fin (sizes n), ∑ i : I,
    if HistoryIterations sizes n h + j.val < budget then
      ENNReal.ofReal (FailureHistoryMass A sizes n h * AttemptMass A (sizes n) (j,some i)) *
        payoff (i,some (budget-(HistoryIterations sizes n h+j.val)))
    else 0

/-- The stage-zero reward is the sum of successful first-attempt payoffs for iteration counts
strictly below the budget. -/
theorem rewardRow_zero (A : Finset I) (sizes : ℕ → ℕ) (budget : ℕ)
    (payoff : I × Option ℕ → ℝ≥0∞) :
    rewardRow A sizes budget 0 payoff =
      ∑ j : Fin (sizes 0), if j.val < budget then
        ∑ i : I, ENNReal.ofReal (AttemptMass A (sizes 0) (j,some i)) * payoff (i,some (budget-j.val)) else 0 := by
  simp only [rewardRow,HistoryIterations,Fin.sum_univ_zero,FailureHistoryMass,
    Fin.prod_univ_zero,one_mul,zero_add]
  simp

/-- The next-stage reward factors through a failed first attempt, reducing the budget and
shifting the size schedule. -/
theorem rewardRow_succ (hN : 0 < Fintype.card I) (A : Finset I) (sizes : ℕ → ℕ)
    (budget n : ℕ) (payoff : I × Option ℕ → ℝ≥0∞) :
    rewardRow A sizes budget (n+1) payoff =
      ∑ j : Fin (sizes 0), if j.val < budget then
        ENNReal.ofReal (AttemptMass A (sizes 0) (j,none)) *
          rewardRow A (TailSizes sizes) (budget-j.val) n payoff else 0 := by
  let e := Fin.consEquiv (fun k : Fin (n+1) => Fin (sizes k.val))
  unfold rewardRow
  rw [← e.sum_comp,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  change (∑ h : TrialHistory (TailSizes sizes) n, ∑ k : Fin (sizes (n+1)), ∑ i : I,
    (if HistoryIterations sizes (n+1) (Fin.cons j h)+k.val < budget then
      ENNReal.ofReal (FailureHistoryMass A sizes (n+1) (Fin.cons j h) * AttemptMass A (sizes (n+1)) (k,some i)) *
        payoff (i,some (budget-(HistoryIterations sizes (n+1) (Fin.cons j h)+k.val))) else 0)) = _
  simp_rw [(search_history_head A sizes n j _).1,(search_history_head A sizes n j _).2]
  by_cases hc : j.val < budget
  · rw [if_pos hc,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have heq : j.val+HistoryIterations (TailSizes sizes) n h+k.val < budget ↔
        HistoryIterations (TailSizes sizes) n h+k.val < budget-j.val := by omega
    have hr : budget-(j.val+HistoryIterations (TailSizes sizes) n h+k.val) =
        (budget-j.val)-(HistoryIterations (TailSizes sizes) n h+k.val) := by omega
    simp only [heq,hr]
    split_ifs
    · have ha := (search_joint_attempt_law hN A (sizes 0)
        (lt_of_le_of_lt (Nat.zero_le _) j.isLt)).1 (j,none)
      simp only [mul_assoc,ENNReal.ofReal_mul ha]
    · simp
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro h _
    apply Finset.sum_eq_zero
    intro k _
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg (by omega)]

/-- The sum of completion rewards over terminal stages below `depth`. -/
def rewardPrefix (A : Finset I) (sizes : ℕ → ℕ) (budget depth : ℕ)
    (payoff : I × Option ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ n ∈ Finset.range depth, rewardRow A sizes budget n payoff

/-- The reward prefix at successor depth splits into immediate success and continuation after a
failed first attempt. -/
theorem rewardPrefix_succ (hN : 0 < Fintype.card I) (A : Finset I) (sizes : ℕ → ℕ)
    (budget depth : ℕ) (payoff : I × Option ℕ → ℝ≥0∞) :
    rewardPrefix A sizes budget (depth+1) payoff =
      ∑ j : Fin (sizes 0), if j.val < budget then
        (∑ i : I, ENNReal.ofReal (AttemptMass A (sizes 0) (j,some i)) * payoff (i,some (budget-j.val))) +
          ENNReal.ofReal (AttemptMass A (sizes 0) (j,none)) *
            rewardPrefix A (TailSizes sizes) (budget-j.val) depth payoff else 0 := by
  unfold rewardPrefix
  rw [Finset.sum_range_succ',rewardRow_zero]
  simp_rw [rewardRow_succ hN]
  rw [Finset.sum_comm,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hc : j.val < budget
  · simp only [if_pos hc]
    rw [← Finset.mul_sum]
    exact add_comm _ _
  · simp [hc]

/-- The payoff sum over terminal traces at stage `n` completing strictly before the budget
equals `rewardRow`. -/
theorem rewardRow_terminal (A : Finset I) (sizes : ℕ → ℕ) (budget n : ℕ)
    (payoff : I × Option ℕ → ℝ≥0∞) :
    (∑ x : TerminalStage I sizes n,
      if TerminalCost sizes ⟨n,x⟩ < budget then
        ENNReal.ofReal (TerminalMass A sizes ⟨n,x⟩) *
          payoff (TerminalOutput ⟨n,x⟩,some (budget-TerminalCost sizes ⟨n,x⟩)) else 0) =
      rewardRow A sizes budget n payoff := by
  simp only [TerminalCost,TerminalIterations,TerminalOutput,TerminalMass,TerminalStageMass,
    rewardRow,Fintype.sum_prod_type]

end Qatlib.Concepts.AmplitudeSearch.InterruptMin
