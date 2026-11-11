/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.BBHTCall

/-!
# Query clocks for ranked BBHT search

The ranked call law `queryBBHTLaw` charges each search trace its terminal Boolean query count,
and `runQueries` adds these counts over a run. The BBHT call estimate [BoyerEtAl1998] yields an
expected total query clock of at most `29 * Real.sqrt N` for minimum attainment, as used in the
analysis of [DurrHoyer1996].

## Main statements

* `queryBBHTLaw_moment`: bounds the first query-cost moment of a call at a positive threshold.
* `queryEnvelope_initial_bound`: bounds the expected rank-trace cost envelope.
* `bbht_query_attainment_moment`: bounds the initial expected query clock for a sorted table.

## References

* [Dürr and Høyer, 1996][DurrHoyer1996]
* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment

open Qatlib.Concepts.AmplitudeSearch.Amplification.RankedCallLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification.SortedRankedTable
open Qatlib.Concepts.AmplitudeSearch.InterruptMin

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib
open Qatlib.Concepts.SearchStopping.GroverSuccess
open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib
/-- The ranked BBHT call law whose duration is the terminal Boolean query count of the search
trace. -/
noncomputable def queryBBHTLaw {N : ℕ} (e : Fin N ≃ Fin N) :
    RankedCallLaw N (SearchTrace N) :=
  bbhtJointLaw e (fun x => (TerminalBooleanQueries (ExponentialSizes N) x : ℝ))
    (fun _ => Nat.cast_nonneg _)

/-- The sum of the terminal Boolean query counts of all calls in a run. -/
noncomputable def runQueries {N : ℕ} (xs : List (SearchTrace N)) : ℕ :=
  (xs.map (TerminalBooleanQueries (ExponentialSizes N))).sum

/-- The accumulated clock of `queryBBHTLaw` equals the total query count coerced to a real
number. -/
theorem queryBBHTLaw_clock {N : ℕ} (e : Fin N ≃ Fin N) (xs : List (SearchTrace N)) :
    (queryBBHTLaw e).runClock xs = (runQueries xs : ℝ) := by
  induction xs with
  | nil => simp only [RankedCallLaw.runClock, runQueries, List.map_nil, List.sum_nil, Nat.cast_zero]
  | cons x xs ih =>
    simp only [RankedCallLaw.runClock, queryBBHTLaw, bbhtJointLaw, runQueries,
      List.map_cons, List.sum_cons, Nat.cast_add] at *
    rw [ih]

/-- Every search trace has a strictly positive terminal Boolean query count. -/
theorem terminalQueries_pos {N : ℕ} (x : SearchTrace N) :
    0 < TerminalBooleanQueries (ExponentialSizes N) x := by
  unfold TerminalBooleanQueries
  omega

/-- The call-cost bound `(29 / 2) * √N / √t` for a nonzero threshold `t`, with value zero at
threshold zero. -/
noncomputable def queryCallBound (N t : ℕ) : ℝ :=
  if t = 0 then 0 else ((29 / 2 : ℝ) * Real.sqrt N) / Real.sqrt t

/-- The call-cost bound is zero at threshold zero. -/
@[simp] theorem queryCallBound_zero (N : ℕ) : queryCallBound N 0 = 0 := by simp [queryCallBound]

/-- At a positive threshold below `N`, the query-cost first moment exists and is at most
`queryCallBound N t`, using the BBHT search bound [BoyerEtAl1998]. -/
theorem queryBBHTLaw_moment {N : ℕ} (e : Fin N ≃ Fin N) (t : ℕ)
    (ht : 0 < t) (htN : t < N) :
    ∃ q, HasSum (fun x => (queryBBHTLaw e).mass t x * (queryBBHTLaw e).duration x) q ∧
      q ≤ queryCallBound N t := by
  have hc := rankMarked_card e t htN.le
  have h := search_terminal_boolean_cost (rankMarked e t) (by omega)
  generalize hM : Fintype.card (Fin N) = M at h
  have hMN : M = N := hM.symm.trans (Fintype.card_fin N)
  clear hM
  subst M
  rw [hc] at h
  obtain ⟨q, hq, _, hqb⟩ := h
  refine ⟨q, ?_, ?_⟩
  · simpa only [queryBBHTLaw, bbhtJointLaw,
      if_pos (show 0 < t ∧ t < N from ⟨ht, htN⟩)] using hq
  · rw [queryCallBound, if_neg (Nat.ne_of_gt ht)]
    rw [Real.sqrt_div (Nat.cast_nonneg N)] at hqb
    convert hqb using 1
    ring

/-- Multiplying the call bound by `t` gives `(29 / 2) * √N * √t`. -/
theorem queryCallBound_scaled (N t : ℕ) :
    (t : ℝ) * queryCallBound N t = ((29 / 2 : ℝ) * Real.sqrt N) * Real.sqrt t := by
  by_cases ht : t = 0
  · simp [ht, queryCallBound]
  have hs : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero ht)
  have hdiv : (t : ℝ) / Real.sqrt t = Real.sqrt t :=
    (div_eq_iff hs.ne').2 (Real.mul_self_sqrt (Nat.cast_nonneg t)).symm
  rw [queryCallBound, if_neg ht]
  calc
    _ = ((29 / 2 : ℝ) * Real.sqrt N) * ((t : ℝ) / Real.sqrt t) := by ring
    _ = _ := by rw [hdiv]

/-- The product of the threshold and its call-cost bound does not decrease when the threshold
increases by one. -/
theorem queryCallBound_scaled_mono (N : ℕ) :
    ∀ t : ℕ, (t : ℝ) * queryCallBound N t ≤ (t + 1 : ℝ) * queryCallBound N (t + 1) := by
  intro t
  have hcast : (t + 1 : ℝ) = ((t + 1 : ℕ) : ℝ) := by norm_cast
  rw [hcast, queryCallBound_scaled, queryCallBound_scaled]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ t))
    (by positivity)

/-- For `N > 0`, the expected rank-trace cost with call bound at rank minus one is at most `29 *
Real.sqrt N`. -/
theorem queryEnvelope_initial_bound (N : ℕ) (hN : 0 < N) :
    expectedTraceCost (fun r => queryCallBound N (r - 1)) N ≤ 29 * Real.sqrt N := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  rw [expectedTraceCost_sum, Finset.sum_range_succ']
  simp only [Nat.zero_add, Nat.sub_self, queryCallBound_zero, zero_div, add_zero]
  have heach (k : ℕ) :
      queryCallBound (n + 1) (k + 1 + 1 - 1) / ((k + 1 : ℕ) + 1 : ℝ) =
      ((29 / 2 : ℝ) * Real.sqrt (n + 1 : ℕ)) *
        (1 / (((k : ℝ) + 2) * Real.sqrt ((k : ℝ) + 1))) := by
    simp only [Nat.add_sub_cancel, queryCallBound, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, if_false, Nat.cast_add, Nat.cast_one]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  simp_rw [heach]
  rw [← Finset.mul_sum]
  have h := mul_le_mul_of_nonneg_left (sqrtCost_sum n)
    (by positivity : 0 ≤ (29 / 2 : ℝ) * Real.sqrt (n + 1 : ℕ))
  nlinarith

/-- For a nonempty sorted table, the initial ranked BBHT run has a nonnegative query-clock first
moment at most `29 * Real.sqrt N`. -/
theorem bbht_query_attainment_moment {N : ℕ} {α : Type*} [LinearOrder α]
    (T : SortedRankedTable N α) (hN : 0 < N) :
    ∃ q, HasSum (fun x : Fin N × List (SearchTrace N) =>
      (queryBBHTLaw T.indexOfRank).initialMass T.skip x *
        (queryBBHTLaw T.indexOfRank).runClock x.2) q ∧
      0 ≤ q ∧ q ≤ 29 * Real.sqrt N := by
  let D := queryCallBound N
  have hscaled := queryCallBound_scaled_mono N
  have hmono := thresholdEnvelope_monotone D hscaled
  obtain ⟨q, hq, hqnn, hqb⟩ := (queryBBHTLaw T.indexOfRank).initialClock_moment T.skip D
    (thresholdEnvelope D) (thresholdEnvelope_zero _ (queryCallBound_zero N))
    (queryBBHTLaw_moment T.indexOfRank)
    (thresholdEnvelope_skip_step T.skip D hscaled) hN
  refine ⟨q, hq, hqnn, ?_⟩
  have hsum : (∑ i : Fin N, thresholdEnvelope D (T.skip.next i)) ≤
      ∑ i : Fin N, thresholdEnvelope D i.val :=
    Finset.sum_le_sum (fun i _ => hmono (T.skip.le_rank i))
  have hd := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg N)
  have heq : (∑ i : Fin N, thresholdEnvelope D i.val) / (N : ℝ) =
      expectedTraceCost (fun r => D (r - 1)) N := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
    rw [expectedTraceCost_succ]
    simp only [thresholdEnvelope, Nat.add_sub_cancel, Nat.cast_succ]
  rw [heq] at hd
  exact hqb.trans (hd.trans (queryEnvelope_initial_bound N hN))

end Qatlib.Concepts.AmplitudeSearch.Amplification
