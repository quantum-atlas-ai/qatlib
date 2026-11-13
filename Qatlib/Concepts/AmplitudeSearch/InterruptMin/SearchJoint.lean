/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.SearchRetry
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.SearchAttempt
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.SearchRandomized

/-!
# Joint laws of search attempts and histories

This module defines `AttemptMass` for a uniformly chosen iteration count and checked optional
output. It proves normalization, support, marginal, and mean-cost identities, then builds failed
histories and terminal-stage masses.

These joint laws retain iteration counts needed for the randomized search cost analysis
[BoyerEtAl1998].

## Main statements

* `search_joint_attempt_law`: For positive attempt size on a nonempty index type, joint attempt
  masses are nonnegative, normalized, and zero on unmarked successful outputs.
* `search_failure_history_law`: Failure-history masses are nonnegative and sum to the retry
  reach mass at stage `n`.
* `search_terminal_stage_law`: Terminal-stage masses are nonnegative, vanish on unmarked
  outputs, and sum to the first-success mass at that stage.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

open Qatlib.Concepts.QueryComplexity.AdaptiveQuery

namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin

open scoped BigOperators
open Qatlib

/-- The joint mass of a uniform iteration count below `m` and the corresponding checked optional
output. -/
noncomputable def AttemptMass {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (m : ℕ) (x : Fin m × Option I) : ℝ :=
  (match x.2 with
    | none => CheckedRejectMass A x.1.val
    | some i => CheckedOutputMass A x.1.val i) / (m : ℝ)

/-- For a fixed iteration count, the joint masses over optional outputs sum to `1 / m`. -/
theorem search_joint_attempt_slice {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (m : ℕ) (j : Fin m) :
    (∑ o : Option I, AttemptMass A m (j,o)) = 1/(m : ℝ) := by
  rw [Fintype.sum_option]
  simp only [AttemptMass]
  rw [← Finset.sum_div, ← add_div]
  have h := (search_checked_attempt hN A j.val).2.2.2.1
  congr 1
  linarith

/-- For positive attempt size on a nonempty index type, joint attempt masses are nonnegative,
normalized, and zero on unmarked successful outputs. -/
theorem search_joint_attempt_law {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (m : ℕ) (hm : 0 < m) :
    (∀ x : Fin m × Option I, 0 ≤ AttemptMass A m x) ∧
    (∑ x : Fin m × Option I, AttemptMass A m x) = 1 ∧
    ∀ j : Fin m, ∀ i : I, i ∉ A → AttemptMass A m (j,some i) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨j,o⟩
    unfold AttemptMass
    apply div_nonneg _ (Nat.cast_nonneg _)
    cases o with
    | none => exact (search_checked_attempt hN A j.val).2.2.2.2.2
    | some i => exact (search_checked_attempt hN A j.val).2.2.2.2.1 i
  · rw [Fintype.sum_prod_type]
    simp_rw [search_joint_attempt_slice hN A m]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
    field_simp
  · intro j i hi
    simp only [AttemptMass, (search_checked_attempt hN A j.val).2.1 i, if_neg hi, zero_div]

/-- The joint attempt marginals recover checked failure, averaged checked output masses, and
checked success. -/
theorem search_joint_attempt_marginals {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (m : ℕ) :
    (∑ j : Fin m, AttemptMass A m (j,none)) = CheckedFailure A m ∧
    (∀ i : I, (∑ j : Fin m, AttemptMass A m (j,some i)) =
      (∑ j ∈ Finset.range m, CheckedOutputMass A j i)/(m : ℝ)) ∧
    (∑ i : I, ∑ j : Fin m, AttemptMass A m (j,some i)) = CheckedSuccess A m := by
  constructor
  · simp only [AttemptMass, CheckedFailure]
    rw [← Finset.sum_div, Fin.sum_univ_eq_sum_range]
  · constructor
    · intro i
      simp only [AttemptMass]
      rw [← Finset.sum_div, Fin.sum_univ_eq_sum_range (fun j => CheckedOutputMass A j i) m]
    · simp only [AttemptMass, CheckedSuccess]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_div]
      rw [Fin.sum_univ_eq_sum_range (fun j => ∑ i, CheckedOutputMass A j i) m]

/-- The joint attempt law's mean iteration count equals `MeanQueries I m`. -/
theorem search_joint_attempt_cost {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (m : ℕ) :
    (∑ x : Fin m × Option I, AttemptMass A m x * (x.1.val : ℝ)) = MeanQueries I m := by
  rw [Fintype.sum_prod_type]
  have hs (j : Fin m) : (∑ o : Option I, AttemptMass A m (j,o) * (j.val : ℝ)) =
      (j.val : ℝ)/(m : ℝ) := by
    rw [← Finset.sum_mul, search_joint_attempt_slice hN A m]
    ring
  simp_rw [hs]
  rw [← Finset.sum_div, Fin.sum_univ_eq_sum_range]
  unfold MeanQueries
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [(search_circuit_laws hN A j).1]

/-- The weighted joint mean of an offset cost is `w * c + w * MeanQueries I m`. -/
theorem search_joint_attempt_reward {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (m : ℕ) (hm : 0 < m) (w c : ℝ) :
    (∑ x : Fin m × Option I, w * AttemptMass A m x * (c + (x.1.val : ℝ))) =
      w*c + w*MeanQueries I m := by
  calc
    _ = (w*c) * (∑ x : Fin m × Option I, AttemptMass A m x) +
        w * (∑ x : Fin m × Option I, AttemptMass A m x * (x.1.val : ℝ)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by rw [(search_joint_attempt_law hN A m hm).2.1,
      search_joint_attempt_cost hN A m]; ring

/-- A choice of an iteration count for each stage below `n`. -/
abbrev TrialHistory (sizes : ℕ → ℕ) (n : ℕ) := ∀ k : Fin n, Fin (sizes k.val)
/-- A failed trial history followed by a terminal iteration count and output index. -/
abbrev TerminalStage (I : Type*) (sizes : ℕ → ℕ) (n : ℕ) :=
  TrialHistory sizes n × (Fin (sizes n) × I)

/-- The product of failed-attempt masses along the specified history. -/
noncomputable def FailureHistoryMass {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (sizes : ℕ → ℕ) (n : ℕ) (history : TrialHistory sizes n) : ℝ :=
  ∏ k : Fin n, AttemptMass A (sizes k.val) (history k,none)

/-- Failure-history masses are nonnegative and sum to the retry reach mass at stage `n`. -/
theorem search_failure_history_law {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (sizes : ℕ → ℕ)
    (hsizes : ∀ k, 0 < sizes k) (n : ℕ) :
    (∀ history : TrialHistory sizes n, 0 ≤ FailureHistoryMass A sizes n history) ∧
    (∑ history : TrialHistory sizes n, FailureHistoryMass A sizes n history) =
      RetryReach A sizes n := by
  constructor
  · intro history
    unfold FailureHistoryMass
    apply Finset.prod_nonneg
    intro k _
    exact (search_joint_attempt_law hN A (sizes k.val) (hsizes k.val)).1 (history k,none)
  · unfold FailureHistoryMass
    rw [← Fintype.prod_sum (fun k : Fin n => fun j : Fin (sizes k.val) =>
      AttemptMass A (sizes k.val) (j,none))]
    simp_rw [(search_joint_attempt_marginals A _).1]
    rw [Fin.prod_univ_eq_prod_range (fun k => CheckedFailure A (sizes k)) n]
    rfl

/-- The mass of a failed history followed by a successful terminal attempt. -/
noncomputable def TerminalStageMass {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (sizes : ℕ → ℕ) (n : ℕ) (x : TerminalStage I sizes n) : ℝ :=
  FailureHistoryMass A sizes n x.1 * AttemptMass A (sizes n) (x.2.1,some x.2.2)

/-- The sum of iteration counts in a trial history. -/
def HistoryIterations (sizes : ℕ → ℕ) (n : ℕ) (h : TrialHistory sizes n) : ℕ :=
  ∑ k : Fin n, (h k).val

/-- An alias for the total history iteration count `HistoryIterations`. -/
abbrev FailureIterations := HistoryIterations

/-- The failed-history iteration count plus the final successful attempt's iteration count. -/
def TerminalIterations {I : Type*} (sizes : ℕ → ℕ) (n : ℕ) (x : TerminalStage I sizes n) : ℕ :=
  HistoryIterations sizes n x.1 + x.2.1.val

/-- Summing terminal-stage masses over failed histories and iteration counts gives the retry
output mass at the specified index. -/
theorem search_terminal_output_marginal {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (sizes : ℕ → ℕ)
    (hsizes : ∀ k, 0 < sizes k) (n : ℕ) (i : I) :
    (∑ h : TrialHistory sizes n, ∑ j : Fin (sizes n), TerminalStageMass A sizes n (h,j,i)) =
      RetryOutputMass A sizes n i := by
  unfold TerminalStageMass
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, (search_failure_history_law hN A sizes hsizes n).2,
    (search_joint_attempt_marginals A (sizes n)).2.1 i]
  rfl

/-- Terminal-stage masses are nonnegative, vanish on unmarked outputs, and sum to the
first-success mass at that stage. -/
theorem search_terminal_stage_law {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (sizes : ℕ → ℕ)
    (hsizes : ∀ k, 0 < sizes k) (n : ℕ) :
    (∀ x : TerminalStage I sizes n, 0 ≤ TerminalStageMass A sizes n x ∧
      (x.2.2 ∉ A → TerminalStageMass A sizes n x = 0)) ∧
    (∑ x : TerminalStage I sizes n, TerminalStageMass A sizes n x) = RetryFirstSuccess A sizes n := by
  constructor
  · rintro ⟨h,j,i⟩
    constructor
    · exact mul_nonneg ((search_failure_history_law hN A sizes hsizes n).1 h)
        ((search_joint_attempt_law hN A (sizes n) (hsizes n)).1 (j,some i))
    · intro hi
      unfold TerminalStageMass
      rw [(search_joint_attempt_law hN A (sizes n) (hsizes n)).2.2 j i hi, mul_zero]
  · rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type, TerminalStageMass, ← Finset.mul_sum]
    have ha : (∑ j : Fin (sizes n), ∑ i : I, AttemptMass A (sizes n) (j,some i)) = CheckedSuccess A (sizes n) := by
      rw [Finset.sum_comm]
      exact (search_joint_attempt_marginals A (sizes n)).2.2
    rw [ha, ← Finset.sum_mul, (search_failure_history_law hN A sizes hsizes n).2]
    rfl

end Qatlib.Concepts.AmplitudeSearch.InterruptMin
