/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.SearchTerminal

/-!
# Boundary cases and nonempty search laws

This module treats empty and fully marked search spaces, then extends termination, terminal-law,
output-uniformity, and expected iteration bounds to every nonempty marked set. In particular,
`search_terminal_output_nonempty` gives uniform output on marked indices.

These statements complete the boundary cases of the randomized search analysis [BoyerEtAl1998].

## Main statements

* `search_terminal_law_nonempty`: For a nonempty marked set, terminal trace masses are
  normalized, nonnegative, and zero on outputs outside the marked set.
* `search_terminal_cost_nonempty`: For a nonempty marked set, the expected terminal iteration
  cost exists, is nonnegative, and is at most `(9 / 2) * √(card I / card A)`.
* `search_terminal_output_nonempty`: For a nonempty marked set, terminal output masses sum to `1
  / card A` at each marked index and to zero at every unmarked index.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.SearchStopping.UnknownCount

namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin

open scoped BigOperators
open Qatlib.Concepts.SearchStopping.KnownCount

/-- The uniform state's Born probability at any index is the reciprocal of the index type's
cardinality. -/
theorem search_uniform_born {I : Type*} [Fintype I] (i : I) :
    BornProb (Uniform I) i = 1 / (Fintype.card I : ℝ) := by
  simp [BornProb, Uniform, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    inv_pow, sq_abs, Real.sq_sqrt (Nat.cast_nonneg (Fintype.card I)), one_div]

/-- Randomized search has zero success probability when the marked set is empty. -/
theorem search_randomized_empty {I : Type*} [Fintype I] [DecidableEq I] (m : ℕ) :
    RandomizedSuccess (∅ : Finset I) m = 0 := by
  simp [RandomizedSuccess, MeasureProb]

/-- For a nonempty index type and positive attempt size, randomized search succeeds with
probability one when every index is marked. -/
theorem search_randomized_univ {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (m : ℕ) (hm : 0 < m) :
    RandomizedSuccess (Finset.univ : Finset I) m = 1 := by
  have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [RandomizedSuccess, (search_circuit_laws hN Finset.univ _).2.2.2]
  simp [hmne]

/-- With an empty marked set, checked success is zero and checked failure is one. -/
theorem search_empty_failure {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (m : ℕ) (hm : 0 < m) :
    CheckedSuccess (∅ : Finset I) m = 0 ∧ CheckedFailure (∅ : Finset I) m = 1 := by
  have h := search_checked_random_attempt hN (∅ : Finset I) m hm
  rw [search_randomized_empty] at h
  exact ⟨h.1, by linarith [h.2.1]⟩

/-- With every index marked, checked success is one and checked failure is zero. -/
theorem search_univ_failure {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (m : ℕ) (hm : 0 < m) :
    CheckedSuccess (Finset.univ : Finset I) m = 1 ∧ CheckedFailure (Finset.univ : Finset I) m = 0 := by
  have h := search_checked_random_attempt hN (Finset.univ : Finset I) m hm
  rw [search_randomized_univ hN m hm] at h
  exact ⟨h.1, by linarith [h.2.1]⟩

/-- With an empty marked set, the retry process remains live with mass one and has zero
first-success mass at every stage. -/
theorem search_empty_live {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (sizes : ℕ → ℕ) (hsizes : ∀ k, 0 < sizes k) (n : ℕ) :
    RetryReach (∅ : Finset I) sizes n = 1 ∧ RetryFirstSuccess (∅ : Finset I) sizes n = 0 := by
  have hr : RetryReach (∅ : Finset I) sizes n = 1 := by
    simp [RetryReach, fun k => (search_empty_failure hN (sizes k) (hsizes k)).2]
  exact ⟨hr, by rw [RetryFirstSuccess, (search_empty_failure hN (sizes n) (hsizes n)).1, mul_zero]⟩

/-- With every index marked, first success occurs at stage zero with mass one and has mass zero
at later stages. -/
theorem search_univ_first_success {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (sizes : ℕ → ℕ) (hsizes : ∀ k, 0 < sizes k) (n : ℕ) :
    RetryFirstSuccess (Finset.univ : Finset I) sizes n = if n = 0 then 1 else 0 := by
  cases n with
  | zero => simp [RetryFirstSuccess, RetryReach, (search_univ_failure hN (sizes 0) (hsizes 0)).1]
  | succ n =>
    simp [RetryFirstSuccess, RetryReach, Finset.prod_range_succ,
      (search_univ_failure hN (sizes n) (hsizes n)).2]

/-- Every terminal trace has mass zero when the marked set is empty. -/
theorem search_empty_terminal {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (sizes : ℕ → ℕ) (hsizes : ∀ k, 0 < sizes k)
    (x : TerminalTrace I sizes) : TerminalMass (∅ : Finset I) sizes x = 0 :=
  (search_terminal_stage_law hN ∅ sizes hsizes x.1).1 x.2 |>.2 (by simp)

/-- At the initial exponential-schedule stage, each marked index has output mass `1 / card I`,
and every unmarked index has zero mass. -/
theorem search_initial_output {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (i : I) :
    RetryOutputMass A (ExponentialSizes (Fintype.card I)) 0 i =
      if i ∈ A then 1 / (Fintype.card I : ℝ) else 0 := by
  simp only [RetryOutputMass, RetryReach, Finset.range_zero, Finset.prod_empty, one_mul]
  have hs : ExponentialSizes (Fintype.card I) 0 = 1 := by
    norm_num [ExponentialSizes, ExponentialWidth]
  rw [hs]
  simp only [Finset.sum_range_one, Nat.cast_one, div_one]
  rw [(search_checked_attempt hN A 0).2.1 i]
  have hz : SearchState A 0 = Uniform I := rfl
  rw [hz, search_uniform_born]

/-- With every index marked, terminal traces at positive stages have zero mass. -/
theorem search_univ_terminal_later {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (sizes : ℕ → ℕ) (hsizes : ∀ k, 0 < sizes k)
    (x : TerminalTrace I sizes) (hx : x.1 ≠ 0) :
    TerminalMass (Finset.univ : Finset I) sizes x = 0 := by
  have h := search_terminal_stage_law hN Finset.univ sizes hsizes x.1
  have hsum := h.2
  rw [search_univ_first_success hN sizes hsizes, if_neg hx] at hsum
  have hle := Finset.single_le_sum (fun y _ => (h.1 y).1) (Finset.mem_univ x.2)
  change TerminalMass (Finset.univ : Finset I) sizes x ≤ _ at hle
  rw [hsum] at hle
  exact le_antisymm hle (h.1 x.2).1

/-- With every index marked, each terminal trace contributes zero mass-weighted iteration cost
under the exponential schedule. -/
theorem search_univ_weighted_cost {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (x : TerminalTrace I (ExponentialSizes (Fintype.card I))) :
    TerminalMass (Finset.univ : Finset I) (ExponentialSizes (Fintype.card I)) x *
      (TerminalCost (ExponentialSizes (Fintype.card I)) x : ℝ) = 0 := by
  by_cases hx : x.1 = 0
  · rcases x with ⟨n,h,j,i⟩
    dsimp at hx
    subst n
    have hj : j.val = 0 := by
      have hjlt := j.isLt
      norm_num [ExponentialSizes, ExponentialWidth] at hjlt
      exact hjlt
    simp [TerminalCost, TerminalIterations, HistoryIterations, hj]
  · rw [search_univ_terminal_later hN _ (search_exponential_schedule _ hN).2.1 x hx, zero_mul]

/-- For any nonempty marked set, the first-success masses under the exponential schedule sum to
one. -/
theorem search_termination_nonempty {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) :
    HasSum (RetryFirstSuccess A (ExponentialSizes (Fintype.card I))) 1 := by
  by_cases hp : A.card < Fintype.card I
  · exact search_all_density_termination A hA hp
  · have hAu : A = Finset.univ := (Finset.card_eq_iff_eq_univ A).mp
      (by have := Finset.card_le_univ A; omega)
    subst A
    have hN : 0 < Fintype.card I := by simpa using hA
    have hsizes := (search_exponential_schedule _ hN).2.1
    change HasSum (fun n => RetryFirstSuccess (Finset.univ : Finset I)
      (ExponentialSizes (Fintype.card I)) n) 1
    simp_rw [search_univ_first_success hN _ hsizes]
    exact hasSum_ite_eq 0 1

/-- For a nonempty marked set, terminal trace masses are normalized, nonnegative, and zero on
outputs outside the marked set. -/
theorem search_terminal_law_nonempty {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) :
    HasSum (TerminalMass A (ExponentialSizes (Fintype.card I))) 1 ∧
    ∀ x : TerminalTrace I (ExponentialSizes (Fintype.card I)),
      0 ≤ TerminalMass A (ExponentialSizes (Fintype.card I)) x ∧
      (TerminalOutput x ∉ A → TerminalMass A (ExponentialSizes (Fintype.card I)) x = 0) := by
  have hN : 0 < Fintype.card I := lt_of_lt_of_le hA (Finset.card_le_univ A)
  have hsizes := (search_exponential_schedule _ hN).2.1
  have hp (x : TerminalTrace I (ExponentialSizes (Fintype.card I))) :
      0 ≤ TerminalMass A (ExponentialSizes (Fintype.card I)) x ∧
      (TerminalOutput x ∉ A → TerminalMass A (ExponentialSizes (Fintype.card I)) x = 0) :=
    (search_terminal_stage_law hN A _ hsizes x.1).1 x.2
  refine ⟨?_,hp⟩
  apply search_nonnegative_trace_sum _ (fun x => (hp x).1) 1
  change HasSum (fun n => ∑ x : TerminalStage I (ExponentialSizes (Fintype.card I)) n,
    TerminalStageMass A (ExponentialSizes (Fintype.card I)) n x) 1
  simp_rw [(search_terminal_stage_law hN A _ hsizes _).2]
  exact search_termination_nonempty A hA

/-- For a nonempty marked set, the expected terminal iteration cost exists, is nonnegative, and
is at most `(9 / 2) * √(card I / card A)`. -/
theorem search_terminal_cost_nonempty {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) :
    ∃ q : ℝ, HasSum (fun x : TerminalTrace I (ExponentialSizes (Fintype.card I)) =>
      TerminalMass A (ExponentialSizes (Fintype.card I)) x *
        (TerminalCost (ExponentialSizes (Fintype.card I)) x : ℝ)) q ∧
      0 ≤ q ∧ q ≤ (9/2 : ℝ)*Real.sqrt ((Fintype.card I : ℝ)/A.card) := by
  by_cases hp : A.card < Fintype.card I
  · obtain ⟨q,hq,hq0,_,hb⟩ := search_terminal_cost A hA hp
    exact ⟨q,hq,hq0,hb⟩
  · have hAu : A = Finset.univ := (Finset.card_eq_iff_eq_univ A).mp
      (by have := Finset.card_le_univ A; omega)
    subst A
    have hN : 0 < Fintype.card I := by simpa using hA
    refine ⟨0,?_,le_rfl,by positivity⟩
    simp_rw [search_univ_weighted_cost hN]
    exact hasSum_zero

/-- With every index marked, the exponential retry output mass at an index is `1 / card I` at
stage zero and zero later. -/
theorem search_univ_retry_output {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (n : ℕ) (i : I) :
    RetryOutputMass (Finset.univ : Finset I) (ExponentialSizes (Fintype.card I)) n i =
      if n = 0 then 1 / (Fintype.card I : ℝ) else 0 := by
  by_cases hn : n = 0
  · subst n
    simpa using search_initial_output hN Finset.univ i
  · have hsizes := (search_exponential_schedule _ hN).2.1
    have hr := search_univ_first_success hN (ExponentialSizes (Fintype.card I)) hsizes n
    rw [RetryFirstSuccess, (search_univ_failure hN _ (hsizes n)).1, mul_one, if_neg hn] at hr
    rw [RetryOutputMass, hr, zero_mul, if_neg hn]

/-- For a nonempty marked set, terminal output masses sum to `1 / card A` at each marked index
and to zero at every unmarked index. -/
theorem search_terminal_output_nonempty {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (i : I) :
    HasSum (fun x : TerminalTrace I (ExponentialSizes (Fintype.card I)) =>
      if TerminalOutput x = i then TerminalMass A (ExponentialSizes (Fintype.card I)) x else 0)
      (if i ∈ A then 1 / (A.card : ℝ) else 0) := by
  by_cases hp : A.card < Fintype.card I
  · exact search_terminal_output A hA hp i
  · have hAu : A = Finset.univ := (Finset.card_eq_iff_eq_univ A).mp
      (by have := Finset.card_le_univ A; omega)
    subst A
    have hN : 0 < Fintype.card I := by simpa using hA
    let sizes := ExponentialSizes (Fintype.card I)
    have hsizes : ∀ k, 0 < sizes k := (search_exponential_schedule _ hN).2.1
    apply search_nonnegative_trace_sum
    · intro x
      split_ifs
      · exact ((search_terminal_law_nonempty Finset.univ hA).2 x).1
      · exact le_rfl
    · have hrow (n : ℕ) : (∑ x : TerminalStage I sizes n,
          if TerminalOutput ⟨n,x⟩ = i then TerminalMass Finset.univ sizes ⟨n,x⟩ else 0) =
          RetryOutputMass Finset.univ sizes n i := by
        simp only [TerminalOutput, TerminalMass]
        rw [Fintype.sum_prod_type]
        simp_rw [Fintype.sum_prod_type]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
        exact search_terminal_output_marginal hN Finset.univ sizes hsizes n i
      change HasSum (fun n => ∑ x : TerminalStage I sizes n,
        if TerminalOutput ⟨n,x⟩ = i then TerminalMass Finset.univ sizes ⟨n,x⟩ else 0) _
      simp_rw [hrow]
      simp only [sizes, search_univ_retry_output hN, Finset.mem_univ, if_true, Finset.card_univ]
      exact hasSum_ite_eq 0 _

end Qatlib.Concepts.AmplitudeSearch.InterruptMin
