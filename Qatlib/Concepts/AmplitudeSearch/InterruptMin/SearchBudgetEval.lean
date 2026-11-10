/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.SearchBudgetBridge
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.SearchStopping.UnknownCount

namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin
open scoped BigOperators

noncomputable def FiniteBudgetEval {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (sizes : ℕ → ℕ) (stage budget : ℕ)
    (onSuccess : I → ℕ → ℝ) (onTimeout : ℕ → ℝ) : ℝ :=
  ∑ x : Fin (sizes stage) × Option I, AttemptMass A (sizes stage) x *
    (if _hc : x.1.val+1 ≤ budget then
      match x.2 with
      | some i => onSuccess i (budget-(x.1.val+1))
      | none => FiniteBudgetEval A sizes (stage+1) (budget-(x.1.val+1)) onSuccess onTimeout
    else onTimeout budget)
termination_by budget

theorem search_finite_budget_eval_nonneg {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (sizes : ℕ → ℕ)
    (hsizes : ∀ k, 0 < sizes k) (stage budget : ℕ)
    (s : I → ℕ → ℝ) (t : ℕ → ℝ) (hs : ∀ i r, 0 ≤ s i r) (ht : ∀ r, 0 ≤ t r) :
    0 ≤ FiniteBudgetEval A sizes stage budget s t := by
  induction budget using Nat.strong_induction_on generalizing stage with
  | h budget ih =>
    rw [FiniteBudgetEval]
    apply Finset.sum_nonneg
    intro x _
    apply mul_nonneg ((search_joint_attempt_law hN A (sizes stage) (hsizes stage)).1 x)
    by_cases hc : x.1.val+1 ≤ budget
    · simp only [dif_pos hc]
      cases hx : x.2 with
      | some i => exact hs i _
      | none => exact ih _ (search_budget_progress _ _ hc) (stage+1)
    · simpa only [dif_neg hc] using ht budget

theorem search_finite_budget_eval_one {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (sizes : ℕ → ℕ)
    (hsizes : ∀ k, 0 < sizes k) (stage budget : ℕ) :
    FiniteBudgetEval A sizes stage budget (fun _ _ => 1) (fun _ => 1) = 1 := by
  induction budget using Nat.strong_induction_on generalizing stage with
  | h budget ih =>
    rw [FiniteBudgetEval]
    calc
      _ = ∑ x : Fin (sizes stage) × Option I, AttemptMass A (sizes stage) x := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hc : x.1.val+1 ≤ budget
        · simp only [dif_pos hc]
          cases hx : x.2 with
          | some i => simp
          | none => rw [ih _ (search_budget_progress _ _ hc) (stage+1)]; simp
        · simp [hc]
      _ = 1 := (search_joint_attempt_law hN A (sizes stage) (hsizes stage)).2.1

theorem search_finite_budget_eval_indicator {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (sizes : ℕ → ℕ) (stage budget : ℕ) (out : Option I) :
    FiniteBudgetEval A sizes stage budget
      (fun i _ => if out = some i then 1 else 0) (fun _ => if out = none then 1 else 0) =
      FiniteBudgetMass A sizes stage budget out := by
  induction budget using Nat.strong_induction_on generalizing stage with
  | h budget ih =>
    conv_lhs => rw [FiniteBudgetEval]
    conv_rhs => rw [FiniteBudgetMass]
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    by_cases hc : x.1.val+1 ≤ budget
    · simp only [dif_pos hc]
      cases hx : x.2 with
      | some i => rfl
      | none => exact ih _ (search_budget_progress _ _ hc) (stage+1)
    · simp [hc]

theorem search_finite_budget_eval_congr {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (sizes : ℕ → ℕ) (stage budget : ℕ)
    (s₁ s₂ : I → ℕ → ℝ) (t₁ t₂ : ℕ → ℝ)
    (hs : ∀ i r, r < budget → s₁ i r = s₂ i r)
    (ht : ∀ r, r ≤ budget → t₁ r = t₂ r) :
    FiniteBudgetEval A sizes stage budget s₁ t₁ = FiniteBudgetEval A sizes stage budget s₂ t₂ := by
  induction budget using Nat.strong_induction_on generalizing stage with
  | h budget ih =>
    conv_lhs => rw [FiniteBudgetEval]
    conv_rhs => rw [FiniteBudgetEval]
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    by_cases hc : x.1.val+1 ≤ budget
    · simp only [dif_pos hc]
      have hb := search_budget_progress _ _ hc
      cases hx : x.2 with
      | some i => exact hs i _ hb
      | none =>
        exact ih _ hb (stage+1)
          (fun i r hr => hs i r (lt_trans hr hb))
          (fun r hr => ht r (le_trans hr hb.le))
    · simp only [dif_neg hc]
      exact ht budget le_rfl

theorem search_finite_budget_eval_success_support {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (sizes : ℕ → ℕ) (stage budget : ℕ)
    (s : I → ℕ → ℝ) (t : ℕ → ℝ) :
    FiniteBudgetEval A sizes stage budget s t =
      FiniteBudgetEval A sizes stage budget (fun i r => if r < budget then s i r else 0) t := by
  apply search_finite_budget_eval_congr
  · intro i r hr
    simp [hr]
  · intros
    rfl

theorem search_finite_budget_eval_shift {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (sizes : ℕ → ℕ) (stage budget : ℕ)
    (s : I → ℕ → ℝ) (t : ℕ → ℝ) :
    FiniteBudgetEval A (TailSizes sizes) stage budget s t =
      FiniteBudgetEval A sizes (stage+1) budget s t := by
  induction budget using Nat.strong_induction_on generalizing stage with
  | h budget ih =>
    conv_lhs => rw [FiniteBudgetEval]
    conv_rhs => rw [FiniteBudgetEval]
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    by_cases hc : x.1.val+1 ≤ budget
    · simp only [dif_pos hc]
      cases hx : x.2 with
      | some i => rfl
      | none => exact ih _ (search_budget_progress _ _ hc) (stage+1)
    · simp [hc]

noncomputable def BudgetRewardRow {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (sizes : ℕ → ℕ) (budget n : ℕ) (s : I → ℕ → ℝ) : ℝ :=
  ∑ h : TrialHistory sizes n, ∑ j : Fin (sizes n), ∑ i : I,
    if HistoryIterations sizes n h + j.val + (n+1) ≤ budget then
      FailureHistoryMass A sizes n h * AttemptMass A (sizes n) (j,some i) *
        s i (budget-(HistoryIterations sizes n h + j.val + (n+1)))
    else 0

theorem search_budget_reward_zero {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (sizes : ℕ → ℕ) (budget : ℕ) (s : I → ℕ → ℝ) :
    BudgetRewardRow A sizes budget 0 s =
      ∑ j : Fin (sizes 0), if j.val+1 ≤ budget then
        ∑ i : I, AttemptMass A (sizes 0) (j,some i) * s i (budget-(j.val+1)) else 0 := by
  simp only [BudgetRewardRow, HistoryIterations, Fin.sum_univ_zero, FailureHistoryMass,
    Fin.prod_univ_zero, one_mul, zero_add]
  simp

theorem search_budget_reward_succ {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (sizes : ℕ → ℕ) (budget n : ℕ) (s : I → ℕ → ℝ) :
    BudgetRewardRow A sizes budget (n+1) s =
      ∑ j : Fin (sizes 0), if j.val+1 ≤ budget then
        AttemptMass A (sizes 0) (j,none) *
          BudgetRewardRow A (TailSizes sizes) (budget-(j.val+1)) n s else 0 := by
  let e := Fin.consEquiv (fun k : Fin (n+1) => Fin (sizes k.val))
  unfold BudgetRewardRow
  rw [← e.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  change (∑ h : TrialHistory (TailSizes sizes) n, ∑ k : Fin (sizes (n+1)), ∑ i : I,
    (if HistoryIterations sizes (n+1) (Fin.cons j h) + k.val + (n+1+1) ≤ budget then
      FailureHistoryMass A sizes (n+1) (Fin.cons j h) * AttemptMass A (sizes (n+1)) (k,some i) *
        s i (budget-(HistoryIterations sizes (n+1) (Fin.cons j h) + k.val + (n+1+1)))
    else 0)) = _
  simp_rw [(search_history_head A sizes n j _).1, (search_history_head A sizes n j _).2]
  by_cases hc : j.val+1 ≤ budget
  · rw [if_pos hc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have heq : j.val + HistoryIterations (TailSizes sizes) n h + k.val + (n+1+1) ≤ budget ↔
        HistoryIterations (TailSizes sizes) n h + k.val + (n+1) ≤ budget-(j.val+1) := by omega
    have hr : budget-(j.val + HistoryIterations (TailSizes sizes) n h + k.val + (n+1+1)) =
        (budget-(j.val+1))-(HistoryIterations (TailSizes sizes) n h + k.val + (n+1)) := by omega
    simp only [heq, hr]
    split_ifs <;> ring
  · rw [if_neg hc]
    apply Finset.sum_eq_zero
    intro h _
    apply Finset.sum_eq_zero
    intro k _
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg (by omega)]

noncomputable def BudgetRewardPrefix {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (sizes : ℕ → ℕ) (budget depth : ℕ) (s : I → ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.range depth, BudgetRewardRow A sizes budget n s

theorem search_budget_reward_prefix_succ {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (sizes : ℕ → ℕ) (budget depth : ℕ) (s : I → ℕ → ℝ) :
    BudgetRewardPrefix A sizes budget (depth+1) s =
      ∑ j : Fin (sizes 0), if j.val+1 ≤ budget then
        (∑ i : I, AttemptMass A (sizes 0) (j,some i) * s i (budget-(j.val+1))) +
        AttemptMass A (sizes 0) (j,none) *
          BudgetRewardPrefix A (TailSizes sizes) (budget-(j.val+1)) depth s else 0 := by
  unfold BudgetRewardPrefix
  rw [Finset.sum_range_succ', search_budget_reward_zero]
  simp_rw [search_budget_reward_succ]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hc : j.val+1 ≤ budget
  · simp only [if_pos hc]
    rw [← Finset.mul_sum]
    ring
  · simp [hc]

theorem search_finite_budget_eval_step {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (sizes : ℕ → ℕ) (budget : ℕ) (s : I → ℕ → ℝ) (t : ℕ → ℝ) :
    FiniteBudgetEval A sizes 0 budget s t =
      ∑ j : Fin (sizes 0), if j.val+1 ≤ budget then
        (∑ i : I, AttemptMass A (sizes 0) (j,some i) * s i (budget-(j.val+1))) +
        AttemptMass A (sizes 0) (j,none) *
          FiniteBudgetEval A (TailSizes sizes) 0 (budget-(j.val+1)) s t
      else (∑ out : Option I, AttemptMass A (sizes 0) (j,out)) * t budget := by
  conv_lhs => rw [FiniteBudgetEval]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  rw [search_finite_budget_eval_shift]
  by_cases hc : j.val+1 ≤ budget
  · simp only [dif_pos hc, if_pos hc]
    rw [Fintype.sum_option]
    simp only
    ring
  · simp only [dif_neg hc, if_neg hc]
    rw [Finset.sum_mul]

theorem search_budget_reward_prefix_le {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (sizes : ℕ → ℕ)
    (hsizes : ∀ k, 0 < sizes k) (budget depth : ℕ)
    (s : I → ℕ → ℝ) (t : ℕ → ℝ) (hs : ∀ i r, 0 ≤ s i r) (ht : ∀ r, 0 ≤ t r) :
    BudgetRewardPrefix A sizes budget depth s ≤ FiniteBudgetEval A sizes 0 budget s t := by
  induction depth generalizing sizes budget with
  | zero =>
    simpa only [BudgetRewardPrefix, Finset.range_zero, Finset.sum_empty] using
      search_finite_budget_eval_nonneg hN A sizes hsizes 0 budget s t hs ht
  | succ depth ih =>
    rw [search_budget_reward_prefix_succ, search_finite_budget_eval_step]
    apply Finset.sum_le_sum
    intro j _
    by_cases hc : j.val+1 ≤ budget
    · rw [if_pos hc, if_pos hc]
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left
      · exact ih (TailSizes sizes) (fun k => hsizes (k+1)) (budget-(j.val+1))
      · exact (search_joint_attempt_law hN A (sizes 0) (hsizes 0)).1 (j,none)
    · rw [if_neg hc, if_neg hc]
      apply mul_nonneg _ (ht budget)
      exact Finset.sum_nonneg (fun out _ =>
        (search_joint_attempt_law hN A (sizes 0) (hsizes 0)).1 (j,out))

theorem search_budget_reward_terminal_row {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (sizes : ℕ → ℕ) (budget n : ℕ) (s : I → ℕ → ℝ) :
    (∑ x : TerminalStage I sizes n,
      if TerminalBooleanQueries sizes ⟨n,x⟩ ≤ budget then
        TerminalMass A sizes ⟨n,x⟩ * s (TerminalOutput ⟨n,x⟩) (budget-TerminalBooleanQueries sizes ⟨n,x⟩)
      else 0) = BudgetRewardRow A sizes budget n s := by
  simp only [TerminalBooleanQueries, TerminalCost, TerminalIterations, TerminalOutput,
    TerminalMass, TerminalStageMass, BudgetRewardRow, Fintype.sum_prod_type]

theorem search_finite_budget_eval_dominates_terminal {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (sizes : ℕ → ℕ)
    (hsizes : ∀ k, 0 < sizes k) (budget : ℕ)
    (s : I → ℕ → ℝ) (t : ℕ → ℝ) (hs : ∀ i r, 0 ≤ s i r) (ht : ∀ r, 0 ≤ t r) :
    (∑' x : TerminalTrace I sizes, if TerminalBooleanQueries sizes x ≤ budget then
      TerminalMass A sizes x * s (TerminalOutput x) (budget-TerminalBooleanQueries sizes x) else 0) ≤
      FiniteBudgetEval A sizes 0 budget s t := by
  have hn (x : TerminalTrace I sizes) :
      0 ≤ (if TerminalBooleanQueries sizes x ≤ budget then
        TerminalMass A sizes x * s (TerminalOutput x) (budget-TerminalBooleanQueries sizes x) else 0) := by
    split_ifs
    · exact mul_nonneg ((search_terminal_stage_law hN A sizes hsizes x.1).1 x.2).1 (hs _ _)
    · exact le_rfl
  have hrow (n : ℕ) : 0 ≤ BudgetRewardRow A sizes budget n s := by
    rw [← search_budget_reward_terminal_row]
    exact Finset.sum_nonneg (fun x _ => hn ⟨n,x⟩)
  have hb (depth : ℕ) : (∑ n ∈ Finset.range depth, BudgetRewardRow A sizes budget n s) ≤
      FiniteBudgetEval A sizes 0 budget s t :=
    search_budget_reward_prefix_le hN A sizes hsizes budget depth s t hs ht
  have hsum := summable_of_sum_range_le hrow hb
  have hflat : HasSum (fun x : TerminalTrace I sizes => if TerminalBooleanQueries sizes x ≤ budget then
      TerminalMass A sizes x * s (TerminalOutput x) (budget-TerminalBooleanQueries sizes x) else 0)
      (∑' n, BudgetRewardRow A sizes budget n s) := by
    apply search_nonnegative_trace_sum _ hn
    simp_rw [search_budget_reward_terminal_row]
    exact hsum.hasSum
  rw [hflat.tsum_eq]
  exact hsum.tsum_le_of_sum_range_le hb

end Qatlib.Concepts.AmplitudeSearch.InterruptMin
