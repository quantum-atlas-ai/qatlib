/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.SearchJoint
import Qatlib.Concepts.AmplitudeSearch.InterruptMin.SearchExpected
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.SearchRandomized
import Qatlib.Concepts.SearchStopping.UnknownCount.SearchSchedule
set_option warningAsError false
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.SearchStopping.UnknownCount

namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin

open scoped BigOperators
open Qatlib

noncomputable def LiveIterationCost {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (sizes : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∑ h : TrialHistory sizes n, FailureHistoryMass A sizes n h * (HistoryIterations sizes n h : ℝ)

noncomputable def TerminalIterationCost {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (sizes : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∑ x : TerminalStage I sizes n, TerminalStageMass A sizes n x * (TerminalIterations sizes n x : ℝ)

theorem search_history_append {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (sizes : ℕ → ℕ) (n : ℕ) (h : TrialHistory sizes n) (j : Fin (sizes n)) :
    FailureHistoryMass A sizes (n+1) (Fin.snoc h j) =
      FailureHistoryMass A sizes n h * AttemptMass A (sizes n) (j,none) ∧
    HistoryIterations sizes (n+1) (Fin.snoc h j) = HistoryIterations sizes n h + j.val := by
  constructor
  · rw [FailureHistoryMass, Fin.prod_univ_castSucc]
    simp [Fin.snoc_castSucc, FailureHistoryMass]
  · rw [HistoryIterations, Fin.sum_univ_castSucc]
    simp [Fin.snoc_castSucc, HistoryIterations]

theorem search_history_clock_mono (sizes : ℕ → ℕ) (n : ℕ)
    (h : TrialHistory sizes n) (j : Fin (sizes n)) :
    HistoryIterations sizes n h ≤ HistoryIterations sizes (n+1) (Fin.snoc h j) := by
  simp only [HistoryIterations]
  rw [Fin.sum_univ_castSucc]
  simp

def InterruptIterations (sizes : ℕ → ℕ) (n : ℕ) (h : TrialHistory sizes n)
    (j : Fin (sizes n)) (budget : ℕ) : ℕ :=
  min budget (HistoryIterations sizes n h + j.val)

theorem search_interrupt_clock (sizes : ℕ → ℕ) (n : ℕ) (h : TrialHistory sizes n)
    (j : Fin (sizes n)) (budget : ℕ) :
    InterruptIterations sizes n h j budget ≤ budget ∧
    (HistoryIterations sizes n h + j.val ≤ budget →
      InterruptIterations sizes n h j budget = HistoryIterations sizes n h + j.val) := by
  exact ⟨min_le_left _ _, fun hcost => min_eq_right hcost⟩

theorem search_live_cost_step {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (sizes : ℕ → ℕ) (n : ℕ) :
    LiveIterationCost A sizes (n+1) =
      ∑ h : TrialHistory sizes n, ∑ j : Fin (sizes n),
        FailureHistoryMass A sizes n h * AttemptMass A (sizes n) (j,none) *
          ((HistoryIterations sizes n h : ℝ) + j.val) := by
  let e := Fin.snocEquiv (fun k : Fin (n+1) => Fin (sizes k.val))
  unfold LiveIterationCost
  have heq : (∑ h : TrialHistory sizes (n+1),
      FailureHistoryMass A sizes (n+1) h * (HistoryIterations sizes (n+1) h : ℝ)) =
      ∑ x : Fin (sizes n) × TrialHistory sizes n,
        FailureHistoryMass A sizes (n+1) (e x) * (HistoryIterations sizes (n+1) (e x) : ℝ) := by
    exact (e.sum_comp (fun h => FailureHistoryMass A sizes (n+1) h *
      (HistoryIterations sizes (n+1) h : ℝ))).symm
  rw [heq, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro j _
  change FailureHistoryMass A sizes (n+1) (Fin.snoc h j) *
    (HistoryIterations sizes (n+1) (Fin.snoc h j) : ℝ) = _
  rw [(search_history_append A sizes n h j).1, (search_history_append A sizes n h j).2]
  push_cast
  rfl

theorem search_iteration_cost_flow {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (sizes : ℕ → ℕ)
    (hsizes : ∀ k, 0 < sizes k) (n : ℕ) :
    LiveIterationCost A sizes (n+1) + TerminalIterationCost A sizes n =
      LiveIterationCost A sizes n + RetryReach A sizes n * MeanQueries I (sizes n) := by
  rw [search_live_cost_step]
  have hterminal : TerminalIterationCost A sizes n =
      ∑ h : TrialHistory sizes n, ∑ j : Fin (sizes n), ∑ i : I,
        FailureHistoryMass A sizes n h * AttemptMass A (sizes n) (j,some i) *
          ((HistoryIterations sizes n h : ℝ) + j.val) := by
    unfold TerminalIterationCost
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type, TerminalStageMass, TerminalIterations, Nat.cast_add]
  rw [hterminal, ← Finset.sum_add_distrib]
  have hbranch (h : TrialHistory sizes n) :
      (∑ j : Fin (sizes n), FailureHistoryMass A sizes n h * AttemptMass A (sizes n) (j,none) *
          ((HistoryIterations sizes n h : ℝ) + j.val)) +
      (∑ j : Fin (sizes n), ∑ i : I, FailureHistoryMass A sizes n h * AttemptMass A (sizes n) (j,some i) *
          ((HistoryIterations sizes n h : ℝ) + j.val)) =
      FailureHistoryMass A sizes n h * (HistoryIterations sizes n h : ℝ) +
        FailureHistoryMass A sizes n h * MeanQueries I (sizes n) := by
    rw [← Finset.sum_add_distrib]
    have heq : (∑ j : Fin (sizes n),
        (FailureHistoryMass A sizes n h * AttemptMass A (sizes n) (j,none) *
          ((HistoryIterations sizes n h : ℝ) + j.val) +
        ∑ i : I, FailureHistoryMass A sizes n h * AttemptMass A (sizes n) (j,some i) *
          ((HistoryIterations sizes n h : ℝ) + j.val))) =
        ∑ x : Fin (sizes n) × Option I, FailureHistoryMass A sizes n h * AttemptMass A (sizes n) x *
          ((HistoryIterations sizes n h : ℝ) + x.1.val) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro j _
      rw [Fintype.sum_option]
    rw [heq]
    exact search_joint_attempt_reward hN A (sizes n) (hsizes n) _ _
  simp_rw [hbranch]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, (search_failure_history_law hN A sizes hsizes n).2]
  rfl

theorem search_truncated_iteration_balance {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (sizes : ℕ → ℕ)
    (hsizes : ∀ k, 0 < sizes k) (n : ℕ) :
    (∑ s ∈ Finset.range n, TerminalIterationCost A sizes s) + LiveIterationCost A sizes n =
      RetryPhasePrefixCost A sizes n := by
  induction n with
  | zero => simp [LiveIterationCost, HistoryIterations, RetryPhasePrefixCost]
  | succ n ih =>
    have hf := search_iteration_cost_flow hN A sizes hsizes n
    rw [Finset.sum_range_succ, RetryPhasePrefixCost, Finset.sum_range_succ]
    change _ = RetryPhasePrefixCost A sizes n + _
    linarith

theorem search_terminal_iteration_mean {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (hproper : A.card < Fintype.card I) :
    ∃ q : ℝ, HasSum (TerminalIterationCost A (ExponentialSizes (Fintype.card I))) q ∧
      0 ≤ q ∧ q ≤ (∑' n, RetryReach A (ExponentialSizes (Fintype.card I)) n *
        MeanQueries I (ExponentialSizes (Fintype.card I) n)) ∧
      q ≤ (9/2 : ℝ)*Real.sqrt ((Fintype.card I : ℝ)/A.card) := by
  have hN : 0 < Fintype.card I := lt_trans hA hproper
  let sizes := ExponentialSizes (Fintype.card I)
  have hsizes : ∀ n, 0 < sizes n := (search_exponential_schedule _ hN).2.1
  have hterminal (n : ℕ) : 0 ≤ TerminalIterationCost A sizes n := by
    unfold TerminalIterationCost
    apply Finset.sum_nonneg
    intro x _
    exact mul_nonneg ((search_terminal_stage_law hN A sizes hsizes n).1 x).1 (Nat.cast_nonneg _)
  have hlive (n : ℕ) : 0 ≤ LiveIterationCost A sizes n := by
    unfold LiveIterationCost
    apply Finset.sum_nonneg
    intro h _
    exact mul_nonneg ((search_failure_history_law hN A sizes hsizes n).1 h) (Nat.cast_nonneg _)
  obtain ⟨q0,hq0,hq0nn,hq0bound⟩ := search_expected_grover_iterations A hA hproper
  have hocc (n : ℕ) : 0 ≤ RetryReach A sizes n * MeanQueries I (sizes n) :=
    mul_nonneg (search_retry_prefix hN A sizes hsizes n).1
      (search_phase_mean_bound A hA hproper n).1
  have hprefix (n : ℕ) : (∑ s ∈ Finset.range n, TerminalIterationCost A sizes s) ≤ q0 := by
    have hb := search_truncated_iteration_balance hN A sizes hsizes n
    have ho : RetryPhasePrefixCost A sizes n ≤ q0 := by
      have h := hq0.summable.sum_le_tsum (Finset.range n) (fun k _ => hocc k)
      rw [hq0.tsum_eq] at h
      exact h
    linarith [hlive n]
  have hsum := summable_of_sum_range_le hterminal hprefix
  have hqle := hsum.tsum_le_of_sum_range_le hprefix
  refine ⟨_,hsum.hasSum,tsum_nonneg hterminal,?_,hqle.trans hq0bound⟩
  rw [hq0.tsum_eq]
  exact hqle

end Qatlib.Concepts.AmplitudeSearch.InterruptMin
