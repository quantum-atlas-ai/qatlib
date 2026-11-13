/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.SearchQueryCost

/-!
# Finite query budgets for unknown-count search

Defines `HistoryBooleanQueries` by charging each trial's Grover iterations plus one verification
query. `FiniteBudgetMass` recursively describes search with a remaining query budget, and the
main laws establish normalization, absence of unmarked outputs, and certain timeout for an empty
marked set. For the quantum-search analysis, see [BoyerEtAl1998].

## Main statements

* `HistoryBooleanQueries`: The Boolean-query cost of a trial history, equal to its total Grover
  iterations plus its number of trials.
* `search_finite_budget_law`: On a nonempty search space with positive schedule sizes, the
  finite-budget output masses are nonnegative and sum to one.
* `search_finite_budget_no_false_positive`: With positive schedule sizes on a nonempty search
  space, finite-budget search assigns zero output mass to every unmarked address.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeSearch.InterruptMin

namespace Qatlib.Concepts.SearchStopping.UnknownCount
open scoped BigOperators

/-- The Boolean-query cost of a trial history, equal to its total Grover iterations plus its
number of trials. -/
def HistoryBooleanQueries (sizes : ℕ → ℕ) (n : ℕ) (h : TrialHistory sizes n) : ℕ :=
  HistoryIterations sizes n h + n

/-- Appending a trial with iteration count `j.val` increases the Boolean-query history cost by
`j.val + 1`. -/
theorem search_advancing_clock (sizes : ℕ → ℕ) (n : ℕ)
    (h : TrialHistory sizes n) (j : Fin (sizes n)) :
    HistoryBooleanQueries sizes (n+1) (Fin.snoc h j) =
      HistoryBooleanQueries sizes n h + (j.val+1) := by
  simp only [HistoryBooleanQueries, HistoryIterations]
  rw [Fin.sum_univ_castSucc]
  simp
  omega

/-- A history whose Boolean-query cost is at most `budget` contains at most `budget` trials. -/
theorem search_budget_bounds_attempts (sizes : ℕ → ℕ) (n budget : ℕ)
    (h : TrialHistory sizes n) (hc : HistoryBooleanQueries sizes n h ≤ budget) : n ≤ budget := by
  unfold HistoryBooleanQueries at hc
  omega

/-- The recursive output mass for staged search with a remaining Boolean-query budget, returning
`none` when the next sampled attempt exceeds that budget. -/
noncomputable def FiniteBudgetMass {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (sizes : ℕ → ℕ) (stage budget : ℕ) (out : Option I) : ℝ :=
  ∑ x : Fin (sizes stage) × Option I, AttemptMass A (sizes stage) x *
    (if hc : x.1.val + 1 ≤ budget then
      match x.2 with
      | some i => if out = some i then 1 else 0
      | none => FiniteBudgetMass A sizes (stage+1) (budget-(x.1.val+1)) out
    else if out = none then 1 else 0)
termination_by budget

/-- An affordable attempt of cost `j + 1` strictly decreases the remaining natural-number
budget. -/
theorem search_budget_progress (budget j : ℕ) (h : j+1 ≤ budget) :
    budget - (j+1) < budget := by omega

/-- On a nonempty search space with positive schedule sizes, the finite-budget output masses are
nonnegative and sum to one. -/
theorem search_finite_budget_law {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (sizes : ℕ → ℕ)
    (hsizes : ∀ k, 0 < sizes k) (stage budget : ℕ) :
    (∀ out, 0 ≤ FiniteBudgetMass A sizes stage budget out) ∧
      (∑ out : Option I, FiniteBudgetMass A sizes stage budget out) = 1 := by
  induction budget using Nat.strong_induction_on generalizing stage with
  | h budget ih =>
    have hbranch (x : Fin (sizes stage) × Option I) :
        (∀ out, 0 ≤ (if hc : x.1.val+1 ≤ budget then
          match x.2 with
          | some i => if out = some i then (1 : ℝ) else 0
          | none => FiniteBudgetMass A sizes (stage+1) (budget-(x.1.val+1)) out
        else if out = none then 1 else 0)) ∧
        (∑ out : Option I, (if hc : x.1.val+1 ≤ budget then
          match x.2 with
          | some i => if out = some i then (1 : ℝ) else 0
          | none => FiniteBudgetMass A sizes (stage+1) (budget-(x.1.val+1)) out
        else if out = none then 1 else 0)) = 1 := by
      by_cases hc : x.1.val+1 ≤ budget
      · simp only [dif_pos hc]
        cases hx : x.2 with
        | none => exact ih _ (search_budget_progress _ _ hc) (stage+1)
        | some i =>
          constructor
          · intro out
            change 0 ≤ (if out = some i then (1 : ℝ) else 0)
            split_ifs <;> norm_num
          · simp
      · simp only [dif_neg hc]
        constructor
        · intro out
          split_ifs <;> norm_num
        · simp
    constructor
    · intro out
      rw [FiniteBudgetMass]
      apply Finset.sum_nonneg
      intro x _
      exact mul_nonneg ((search_joint_attempt_law hN A (sizes stage) (hsizes stage)).1 x)
        ((hbranch x).1 out)
    · conv_lhs =>
        arg 2
        ext out
        rw [FiniteBudgetMass]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
      have heq : (∑ x : Fin (sizes stage) × Option I, AttemptMass A (sizes stage) x *
          (∑ out : Option I, (if hc : x.1.val+1 ≤ budget then
            match x.2 with
            | some i => if out = some i then (1 : ℝ) else 0
            | none => FiniteBudgetMass A sizes (stage+1) (budget-(x.1.val+1)) out
          else if out = none then 1 else 0))) =
          ∑ x : Fin (sizes stage) × Option I, AttemptMass A (sizes stage) x := by
        apply Finset.sum_congr rfl
        intro x _
        rw [(hbranch x).2, mul_one]
      rw [heq]
      exact (search_joint_attempt_law hN A (sizes stage) (hsizes stage)).2.1

/-- With positive schedule sizes on a nonempty search space, finite-budget search assigns zero
output mass to every unmarked address. -/
theorem search_finite_budget_no_false_positive {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (sizes : ℕ → ℕ)
    (hsizes : ∀ k, 0 < sizes k) (stage budget : ℕ) (i : I) (hi : i ∉ A) :
    FiniteBudgetMass A sizes stage budget (some i) = 0 := by
  induction budget using Nat.strong_induction_on generalizing stage with
  | h budget ih =>
    rw [FiniteBudgetMass]
    apply Finset.sum_eq_zero
    rintro ⟨j,o⟩ _
    by_cases hc : j.val+1 ≤ budget
    · simp only [dif_pos hc]
      cases o with
      | none => rw [ih _ (search_budget_progress _ _ hc), mul_zero]
      | some k =>
        by_cases hk : i = k
        · subst k
          rw [(search_joint_attempt_law hN A (sizes stage) (hsizes stage)).2.2 j i hi, zero_mul]
        · simp [hk]
    · simp [hc]

/-- With positive schedule sizes on a nonempty search space, finite-budget search on the empty
marked set returns `none` with probability one. -/
theorem search_empty_budget_timeout {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (sizes : ℕ → ℕ) (hsizes : ∀ k, 0 < sizes k)
    (stage budget : ℕ) : FiniteBudgetMass (∅ : Finset I) sizes stage budget none = 1 := by
  have hlaw := (search_finite_budget_law hN (∅ : Finset I) sizes hsizes stage budget).2
  rw [Fintype.sum_option] at hlaw
  have hz (i : I) : FiniteBudgetMass (∅ : Finset I) sizes stage budget (some i) = 0 :=
    search_finite_budget_no_false_positive hN ∅ sizes hsizes stage budget i (by simp)
  simpa only [hz, Finset.sum_const_zero, add_zero] using hlaw

end Qatlib.Concepts.SearchStopping.UnknownCount
