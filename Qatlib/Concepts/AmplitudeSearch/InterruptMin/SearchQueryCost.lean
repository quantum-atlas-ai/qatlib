/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.SearchBoundary

/-!
# Boolean-query and source lookup search costs

This module defines terminal Boolean-query cost and source lookup cost separately.
`TerminalBooleanQueries` charges iterations plus one check per attempt, while
`SourceLookupClock` charges twice the iteration cost plus those checks.

Bounds on terminal attempt counts give expected costs of `(29 / 2) * √(card I / card A)` and `19
* √(card I / card A)` respectively, supporting randomized search [BoyerEtAl1998] and minimum
finding [DurrHoyer1996].

## Main statements

* `search_terminal_boolean_cost`: For any nonempty marked set, the expected terminal
  Boolean-query count exists, is nonnegative, and is at most `(29 / 2) * √(card I / card A)`.
* `search_terminal_source_lookup_cost`: For any nonempty marked set, the expected source lookup
  clock exists, is nonnegative, and is at most `19 * √(card I / card A)`.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
* [Dürr and Høyer, 1996][DurrHoyer1996]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.SearchStopping.UnknownCount

namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin

open scoped BigOperators
open Qatlib

/-- The terminal iteration cost plus one checking query for each attempt. -/
def TerminalBooleanQueries {I : Type*} (sizes : ℕ → ℕ) (x : TerminalTrace I sizes) : ℕ :=
  TerminalCost sizes x + (x.1 + 1)

/-- Twice the terminal iteration cost plus one check for each attempt, defining the source
lookup clock used in minimum-search accounting [DurrHoyer1996]. -/
def SourceLookupClock {I : Type*} (sizes : ℕ → ℕ) (x : TerminalTrace I sizes) : ℕ :=
  2 * TerminalCost sizes x + (x.1 + 1)

/-- The terminal Boolean-query count equals the sum of the lifted search-circuit queries and one
checking query over all attempts. -/
theorem search_terminal_query_count {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (sizes : ℕ → ℕ) (x : TerminalTrace I sizes) :
    TerminalBooleanQueries sizes x =
      (∑ k : Fin x.1, (QueryCount (LiftCircuit (SearchCircuit I (x.2.1 k).val)) +
        QueryCount ([Step.query] : Circuit (I × Bool)))) +
      (QueryCount (LiftCircuit (SearchCircuit I x.2.2.1.val)) +
        QueryCount ([Step.query] : Circuit (I × Bool))) := by
  simp_rw [(search_checked_attempt hN A _).1]
  simp [TerminalBooleanQueries, TerminalCost, TerminalIterations, HistoryIterations,
    Finset.sum_add_distrib, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- For `N ≥ 2`, every positive-stage exponential attempt size is at least two. -/
theorem search_later_size_ge_two (N k : ℕ) (hN : 2 ≤ N) (hk : 0 < k) :
    2 ≤ ExponentialSizes N k := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hroot : 1 < Real.sqrt N := by
    nlinarith [Real.sqrt_nonneg (N : ℝ), Real.sq_sqrt (Nat.cast_nonneg N)]
  have hp : 1 < (6/5 : ℝ)^k := one_lt_pow₀ (by norm_num) hk.ne'
  have hw : 1 < ExponentialWidth N k := by
    rw [(search_exponential_schedule N (by omega)).1]
    exact lt_min hp hroot
  have h : 1 < Nat.ceil (ExponentialWidth N k) := Nat.lt_ceil.mpr (by simpa using hw)
  exact h

/-- For a nonempty proper marked set, the prefix sum of retry reach masses is at most one plus
twice the retry phase prefix cost. -/
theorem search_attempt_prefix_bound {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (hp : A.card < Fintype.card I) (n : ℕ) :
    (∑ s ∈ Finset.range n, RetryReach A (ExponentialSizes (Fintype.card I)) s) ≤
      1 + 2 * RetryPhasePrefixCost A (ExponentialSizes (Fintype.card I)) n := by
  have hN : 0 < Fintype.card I := lt_trans hA hp
  let sizes := ExponentialSizes (Fintype.card I)
  have hsizes := (search_exponential_schedule _ hN).2.1
  have hterm (s : ℕ) : RetryReach A sizes s ≤
      (if s = 0 then 1 else 0) + 2 * (RetryReach A sizes s * MeanQueries I (sizes s)) := by
    have hr := (search_retry_prefix hN A sizes hsizes s).1
    have hc := (search_phase_mean_bound A hA hp s).1
    by_cases hs : s = 0
    · subst s
      simp only [RetryReach, Finset.range_zero, Finset.prod_empty, ite_true, one_mul]
      linarith
    · rw [if_neg hs, zero_add]
      have hm : 2 ≤ sizes s := search_later_size_ge_two _ s (by omega) (by omega)
      obtain ⟨_,_,_,_,_,hQ,_⟩ := search_randomized_search_contract A hA hp (sizes s) (hsizes s)
      have hmr : (2 : ℝ) ≤ sizes s := by exact_mod_cast hm
      have hmean : 1 ≤ 2 * MeanQueries I (sizes s) := by rw [hQ]; linarith
      nlinarith [mul_le_mul_of_nonneg_left hmean hr]
  calc
    _ ≤ ∑ s ∈ Finset.range n,
        ((if s = 0 then 1 else 0) + 2 * (RetryReach A sizes s * MeanQueries I (sizes s))) :=
      Finset.sum_le_sum (fun s _ => hterm s)
    _ = (∑ s ∈ Finset.range n, (if s = 0 then (1 : ℝ) else 0)) +
        2 * RetryPhasePrefixCost A sizes n := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      rfl
    _ ≤ _ := by
      simp only [Finset.sum_ite_eq', Finset.mem_range]
      split_ifs <;> linarith

/-- The first-success-weighted attempt count before stage `n`, plus `n` times the surviving
mass, equals the sum of reach masses before `n`. -/
theorem search_attempt_count_balance {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (sizes : ℕ → ℕ)
    (hsizes : ∀ k, 0 < sizes k) (n : ℕ) :
    (∑ s ∈ Finset.range n, RetryFirstSuccess A sizes s * ((s : ℝ)+1)) +
      (n : ℝ) * RetryReach A sizes n = ∑ s ∈ Finset.range n, RetryReach A sizes s := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hr : RetryFirstSuccess A sizes n + RetryReach A sizes (n+1) = RetryReach A sizes n := by
      have hstep : RetryReach A sizes (n+1) = RetryReach A sizes n * CheckedFailure A (sizes n) := by
        simp only [RetryReach, Finset.prod_range_succ]
      rw [hstep, RetryFirstSuccess, (search_checked_random_attempt hN A (sizes n) (hsizes n)).2.1]
      ring
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    push_cast
    linear_combination ih + ((n : ℝ)+1)*hr

/-- For a nonempty proper marked set, the mean terminal attempt count exists, is nonnegative,
and is at most `1 + 9 * √(card I / card A)`. -/
theorem search_terminal_attempts {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (hp : A.card < Fintype.card I) :
    ∃ q : ℝ, HasSum (fun x : TerminalTrace I (ExponentialSizes (Fintype.card I)) =>
      TerminalMass A (ExponentialSizes (Fintype.card I)) x * ((x.1 + 1 : ℕ) : ℝ)) q ∧
      0 ≤ q ∧ q ≤ 1 + 9 * Real.sqrt ((Fintype.card I : ℝ) / A.card) := by
  have hN : 0 < Fintype.card I := lt_trans hA hp
  let sizes := ExponentialSizes (Fintype.card I)
  have hsizes := (search_exponential_schedule _ hN).2.1
  have hnn (n : ℕ) : 0 ≤ RetryFirstSuccess A sizes n * ((n : ℝ)+1) :=
    mul_nonneg (search_retry_prefix hN A sizes hsizes n).2.2.2 (by positivity)
  have hb (n : ℕ) : (∑ s ∈ Finset.range n, RetryFirstSuccess A sizes s * ((s : ℝ)+1)) ≤
      1 + 9 * Real.sqrt ((Fintype.card I : ℝ) / A.card) := by
    have hc := search_attempt_count_balance hN A sizes hsizes n
    have ht := search_attempt_prefix_bound A hA hp n
    have hi := search_phase_prefix_bound A hA hp n
    have hlive : 0 ≤ (n : ℝ) * RetryReach A sizes n :=
      mul_nonneg (Nat.cast_nonneg n) (search_retry_prefix hN A sizes hsizes n).1
    change (∑ s ∈ Finset.range n, RetryReach A sizes s) ≤ _ at ht
    change RetryPhasePrefixCost A sizes n ≤ _ at hi
    linarith
  have hsum := summable_of_sum_range_le hnn hb
  refine ⟨_,?_,tsum_nonneg hnn,hsum.tsum_le_of_sum_range_le hb⟩
  apply search_nonnegative_trace_sum
  · intro x
    exact mul_nonneg ((search_terminal_law A hA hp).2 x).1 (Nat.cast_nonneg _)
  · change HasSum (fun n => ∑ x : TerminalStage I sizes n,
      TerminalStageMass A sizes n x * ((n+1 : ℕ) : ℝ)) _
    simp_rw [← Finset.sum_mul, (search_terminal_stage_law hN A sizes hsizes _).2, Nat.cast_add,
        Nat.cast_one]
    exact hsum.hasSum

/-- For a nonempty proper marked set, the mean of `c` times terminal iteration cost plus attempt
count is nonnegative and at most `(10 + c * (9 / 2)) * √(card I / card A)`. -/
theorem search_terminal_linear_cost {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (hp : A.card < Fintype.card I) (c : ℕ) :
    ∃ q : ℝ, HasSum (fun x : TerminalTrace I (ExponentialSizes (Fintype.card I)) =>
      TerminalMass A (ExponentialSizes (Fintype.card I)) x *
        ((c * TerminalCost (ExponentialSizes (Fintype.card I)) x + (x.1+1) : ℕ) : ℝ)) q ∧
      0 ≤ q ∧ q ≤ (1 + 9 + (c : ℝ) * (9/2)) * Real.sqrt ((Fintype.card I : ℝ) / A.card) := by
  obtain ⟨qi,hi,hi0,_,hib⟩ := search_terminal_cost A hA hp
  obtain ⟨qa,ha,ha0,hab⟩ := search_terminal_attempts A hA hp
  have hAr : (0 : ℝ) < A.card := by exact_mod_cast hA
  have hNr : (A.card : ℝ) ≤ Fintype.card I := by exact_mod_cast (Finset.card_le_univ A)
  have hd : 1 ≤ (Fintype.card I : ℝ) / A.card :=
    (le_div_iff₀ hAr).2 (by simpa only [one_mul] using hNr)
  have hsqrt : 1 ≤ Real.sqrt ((Fintype.card I : ℝ) / A.card) := by
    nlinarith [Real.sqrt_nonneg ((Fintype.card I : ℝ) / A.card),
      Real.sq_sqrt (show 0 ≤ (Fintype.card I : ℝ) / A.card by positivity)]
  refine ⟨(c : ℝ)*qi+qa,?_,by positivity,?_⟩
  · have h := (hi.mul_left (c : ℝ)).add ha
    convert! h using 1
    funext x
    push_cast
    ring
  · have hmul := mul_le_mul_of_nonneg_left hib (Nat.cast_nonneg c)
    nlinarith

/-- For any nonempty marked set, the mean of `c` times terminal iteration cost plus attempt
count is nonnegative and at most `(10 + c * (9 / 2)) * √(card I / card A)`. -/
theorem search_terminal_linear_cost_nonempty {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (c : ℕ) :
    ∃ q : ℝ, HasSum (fun x : TerminalTrace I (ExponentialSizes (Fintype.card I)) =>
      TerminalMass A (ExponentialSizes (Fintype.card I)) x *
        ((c * TerminalCost (ExponentialSizes (Fintype.card I)) x + (x.1+1) : ℕ) : ℝ)) q ∧
      0 ≤ q ∧ q ≤ (1 + 9 + (c : ℝ) * (9/2)) * Real.sqrt ((Fintype.card I : ℝ) / A.card) := by
  by_cases hp : A.card < Fintype.card I
  · exact search_terminal_linear_cost A hA hp c
  · have hAu : A = Finset.univ := (Finset.card_eq_iff_eq_univ A).mp
      (by have := Finset.card_le_univ A; omega)
    subst A
    have hN : 0 < Fintype.card I := by simpa using hA
    have hNr : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    refine ⟨1,?_,by norm_num,?_⟩
    · have heq (x : TerminalTrace I (ExponentialSizes (Fintype.card I))) :
          TerminalMass Finset.univ (ExponentialSizes (Fintype.card I)) x *
            ((c * TerminalCost (ExponentialSizes (Fintype.card I)) x + (x.1+1) : ℕ) : ℝ) =
          TerminalMass Finset.univ (ExponentialSizes (Fintype.card I)) x := by
        by_cases hx : x.1 = 0
        · have hz := search_univ_weighted_cost hN x
          push_cast
          rw [hx]
          push_cast
          nlinarith [hz]
        · rw [search_univ_terminal_later hN _ (search_exponential_schedule _ hN).2.1 x hx]
          ring
      simp_rw [heq]
      exact (search_terminal_law_nonempty Finset.univ hA).1
    · simp only [Finset.card_univ, div_self hNr, Real.sqrt_one, mul_one]
      have hc : 0 ≤ (c : ℝ) := Nat.cast_nonneg c
      linarith

/-- For any nonempty marked set, the expected terminal Boolean-query count exists, is
nonnegative, and is at most `(29 / 2) * √(card I / card A)`. -/
theorem search_terminal_boolean_cost {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) :
    ∃ q : ℝ, HasSum (fun x : TerminalTrace I (ExponentialSizes (Fintype.card I)) =>
      TerminalMass A (ExponentialSizes (Fintype.card I)) x *
        (TerminalBooleanQueries (ExponentialSizes (Fintype.card I)) x : ℝ)) q ∧
      0 ≤ q ∧ q ≤ (29/2 : ℝ) * Real.sqrt ((Fintype.card I : ℝ) / A.card) := by
  have h := search_terminal_linear_cost_nonempty A hA 1
  norm_num only [Nat.cast_one, one_mul, show (1 + 9 + 9/2 : ℝ) = 29/2 by norm_num] at h
  exact h

/-- For any nonempty marked set, the expected source lookup clock exists, is nonnegative, and is
at most `19 * √(card I / card A)`. -/
theorem search_terminal_source_lookup_cost {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) :
    ∃ q : ℝ, HasSum (fun x : TerminalTrace I (ExponentialSizes (Fintype.card I)) =>
      TerminalMass A (ExponentialSizes (Fintype.card I)) x *
        (SourceLookupClock (ExponentialSizes (Fintype.card I)) x : ℝ)) q ∧
      0 ≤ q ∧ q ≤ 19 * Real.sqrt ((Fintype.card I : ℝ) / A.card) := by
  have h := search_terminal_linear_cost_nonempty A hA 2
  norm_num only [Nat.cast_ofNat, show (1 + 9 + 2 * (9/2) : ℝ) = 19 by norm_num] at h
  exact h

end Qatlib.Concepts.AmplitudeSearch.InterruptMin
