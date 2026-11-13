/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.RankEventBridge
import Qatlib.Concepts.AmplitudeSearch.Amplification.TableRun

/-!
# Rank visit laws for BBHT minimum search

This module transfers rank-process visit probabilities to the BBHT search law of a sorted table.
For distinct values, `bbht_visit_hasSum` gives the reciprocal-rank formula; for tied values,
`bbht_visit_tied_bound` gives the corresponding upper bound.

The constructions connect randomized search [BoyerEtAl1998] with the rank analysis of minimum
finding [DurrHoyer1996].

## Main statements

* `bbht_visit_hasSum`: For distinct table values, the BBHT run masses of traces visiting rank
  `r` sum to `1 / r` when `1 ≤ r ≤ t`, and to zero otherwise.
* `bbht_initial_visit_tied_bound`: For uniform initialization and tables allowing ties, the
  visit mass is nonnegative and bounded by `1 / r` on `1 ≤ r ≤ N`, and by zero otherwise.
* `bbht_minimum_threshold_no_visits`: Starting from threshold zero, the mass of traces visiting
  any rank sums to zero.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
* [Dürr and Høyer, 1996][DurrHoyer1996]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment
open Qatlib.Concepts.AmplitudeSearch.Amplification.RankedCallLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification.SortedRankedTable

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

open scoped BigOperators

/-- For a sorted table with distinct values, the lower cut at rank `y` is `y` itself. -/
theorem sorted_lowerCut_eq_rank {N : ℕ} {α : Type*} [LinearOrder α]
    (T : SortedRankedTable N α) (hd : Function.Injective T.value) (y : Fin N) :
    T.lowerCut y = y := by
  have hstrict : StrictMono (fun i => T.value (T.indexOfRank i)) :=
    T.sorted.strictMono_of_injective (hd.comp T.indexOfRank.injective)
  apply le_antisymm (T.lowerCut_le y)
  apply le_of_not_gt
  intro hy
  have hbad := (T.smaller_iff_lowerCut y (T.lowerCut y)).mp (hstrict hy)
  exact (lt_irrefl _) hbad

/-- The rank-skip map of a sorted table with distinct values equals `RankSkip.distinct`. -/
theorem sorted_skip_eq_distinct {N : ℕ} {α : Type*} [LinearOrder α]
    (T : SortedRankedTable N α) (hd : Function.Injective T.value) :
    T.skip = RankSkip.distinct N := by
  have hnext : T.skip.next = Fin.val := by
    funext y
    exact congrArg Fin.val (sorted_lowerCut_eq_rank T hd y)
  cases h : T.skip with
  | mk next hle =>
    rw [h] at hnext
    simp only at hnext
    subst next
    rfl

/-- For distinct table values, the rank prefix below `t` is exactly the set of entries strictly
below the value at rank `t`. -/
theorem distinct_prefix_is_original_marking {N : ℕ} {α : Type*} [LinearOrder α]
    (T : SortedRankedTable N α) (hd : Function.Injective T.value) (t : ℕ) (htN : t < N) :
    rankMarked T.indexOfRank t =
      Finset.univ.filter (fun i => T.value i < T.value (T.indexOfRank ⟨t,htN⟩)) := by
  have h := rankMarked_eq_strict_values T ⟨t,htN⟩
  rwa [sorted_lowerCut_eq_rank T hd] at h

/-- The real-valued rank-hit probability is `1 / r` when `1 ≤ r ≤ t`, and zero otherwise. -/
theorem hitProbability_real_formula (t r : ℕ) :
    (hitProbability t r : ℝ) = if 1 ≤ r ∧ r ≤ t then 1/(r : ℝ) else 0 := by
  rw [hitProbability_formula]
  split_ifs <;> norm_num

/-- For distinct table values, the BBHT run masses of traces visiting rank `r` sum to `1 / r`
when `1 ≤ r ≤ t`, and to zero otherwise. -/
theorem bbht_visit_hasSum {N : ℕ} {α : Type*} [LinearOrder α]
    (T : SortedRankedTable N α) (hN : 0 < N) (hd : Function.Injective T.value)
    (t r : ℕ) (htN : t < N) :
    HasSum (fun xs : List (SearchTrace N) =>
      if r ∈ (sourceBBHTLaw T.indexOfRank hN).rankTrace xs then
        (sourceBBHTLaw T.indexOfRank hN).runMass T.skip t xs else 0)
      (if 1 ≤ r ∧ r ≤ t then 1/(r : ℝ) else 0) := by
  rw [sorted_skip_eq_distinct T hd]
  have h := (sourceBBHTLaw T.indexOfRank hN).hitMass_eq_tree (RankSkip.distinct N) t r htN
  rw [skipExperiment_distinct N t htN.le] at h
  change HasSum _ (hitProbability t r : ℝ) at h
  rwa [hitProbability_real_formula] at h

/-- For distinct table values and uniform initialization, the masses of traces visiting rank `r`
sum to `1 / r` when `1 ≤ r ≤ N`, and to zero otherwise. -/
theorem bbht_initial_visit_hasSum {N : ℕ} {α : Type*} [LinearOrder α]
    (T : SortedRankedTable N α) (hN : 0 < N) (hd : Function.Injective T.value) (r : ℕ) :
    HasSum (fun x : Fin N × List (SearchTrace N) =>
      if r ∈ (sourceBBHTLaw T.indexOfRank hN).initialRankTrace x then
        (sourceBBHTLaw T.indexOfRank hN).initialMass T.skip x else 0)
      (if 1 ≤ r ∧ r ≤ N then 1/(r : ℝ) else 0) := by
  rw [sorted_skip_eq_distinct T hd]
  have h := (sourceBBHTLaw T.indexOfRank hN).initialHitMass_eq_tree (RankSkip.distinct N) hN r
  rw [skipExperiment_distinct N N le_rfl] at h
  change HasSum _ (hitProbability N r : ℝ) at h
  rwa [hitProbability_real_formula] at h

/-- For tables allowing ties, the masses of traces visiting `r` have a nonnegative sum bounded
by `1 / r` on `1 ≤ r ≤ t`, and by zero otherwise. -/
theorem bbht_visit_tied_bound {N : ℕ} {α : Type*} [LinearOrder α]
    (T : SortedRankedTable N α) (hN : 0 < N) (t r : ℕ) (htN : t < N) :
    ∃ q : ℝ, HasSum (fun xs : List (SearchTrace N) =>
      if r ∈ (sourceBBHTLaw T.indexOfRank hN).rankTrace xs then
        (sourceBBHTLaw T.indexOfRank hN).runMass T.skip t xs else 0) q ∧
      0 ≤ q ∧ q ≤ (if 1 ≤ r ∧ r ≤ t then 1/(r : ℝ) else 0) := by
  refine ⟨_,(sourceBBHTLaw T.indexOfRank hN).hitMass_eq_tree T.skip t r htN,?_,?_⟩
  · exact_mod_cast Experiment.probability_nonneg (skipExperiment T.skip t) (fun trace => r ∈ trace)
  · have h : (((skipExperiment T.skip t).probability (fun trace => r ∈ trace) : ℚ) : ℝ) ≤
        (hitProbability t r : ℝ) := by exact_mod_cast skipProbability_le T.skip t r htN.le
    rwa [hitProbability_real_formula] at h

/-- Bounds the total mass of visits to rank `r` when the starting threshold is the lower cut
determined by table index `y`. -/
theorem bbht_threshold_visit_tied_bound {N : ℕ} {α : Type*} [LinearOrder α]
    (T : SortedRankedTable N α) (hN : 0 < N) (y : Fin N) (r : ℕ) :
    ∃ q : ℝ, HasSum (fun xs : List (SearchTrace N) =>
      if r ∈ (sourceBBHTLaw T.indexOfRank hN).rankTrace xs then
        (sourceBBHTLaw T.indexOfRank hN).runMass T.skip
          (T.skip.next (T.indexOfRank.symm y)) xs else 0) q ∧
      0 ≤ q ∧ q ≤ (if 1 ≤ r ∧ r ≤ T.skip.next (T.indexOfRank.symm y)
        then 1/(r : ℝ) else 0) := by
  exact bbht_visit_tied_bound T hN _ r
    (lt_of_le_of_lt (T.skip.le_rank _) (T.indexOfRank.symm y).isLt)

/-- For uniform initialization and tables allowing ties, the visit mass is nonnegative and
bounded by `1 / r` on `1 ≤ r ≤ N`, and by zero otherwise. -/
theorem bbht_initial_visit_tied_bound {N : ℕ} {α : Type*} [LinearOrder α]
    (T : SortedRankedTable N α) (hN : 0 < N) (r : ℕ) :
    ∃ q : ℝ, HasSum (fun x : Fin N × List (SearchTrace N) =>
      if r ∈ (sourceBBHTLaw T.indexOfRank hN).initialRankTrace x then
        (sourceBBHTLaw T.indexOfRank hN).initialMass T.skip x else 0) q ∧
      0 ≤ q ∧ q ≤ (if 1 ≤ r ∧ r ≤ N then 1/(r : ℝ) else 0) := by
  refine ⟨_,(sourceBBHTLaw T.indexOfRank hN).initialHitMass_eq_tree T.skip hN r,?_,?_⟩
  · exact_mod_cast Experiment.probability_nonneg (skipExperiment T.skip N) (fun trace => r ∈ trace)
  · have h : (((skipExperiment T.skip N).probability (fun trace => r ∈ trace) : ℚ) : ℝ) ≤
        (hitProbability N r : ℝ) := by exact_mod_cast skipProbability_le T.skip N r le_rfl
    rwa [hitProbability_real_formula] at h

/-- The mass of visits to rank zero or a rank above the starting rank `t` sums to zero. -/
theorem bbht_visit_outside {N : ℕ} {α : Type*} [LinearOrder α]
    (T : SortedRankedTable N α) (hN : 0 < N) (t r : ℕ) (htN : t < N)
    (hr : r = 0 ∨ t < r) :
    HasSum (fun xs : List (SearchTrace N) =>
      if r ∈ (sourceBBHTLaw T.indexOfRank hN).rankTrace xs then
        (sourceBBHTLaw T.indexOfRank hN).runMass T.skip t xs else 0) 0 := by
  obtain ⟨q,hq,hq0,hqb⟩ := bbht_visit_tied_bound T hN t r htN
  have hc : ¬ (1 ≤ r ∧ r ≤ t) := by omega
  rw [if_neg hc] at hqb
  have hz : q = 0 := le_antisymm hqb hq0
  simpa only [hz] using hq

/-- Starting from threshold zero, the mass of traces visiting any rank sums to zero. -/
theorem bbht_minimum_threshold_no_visits {N : ℕ} {α : Type*} [LinearOrder α]
    (T : SortedRankedTable N α) (hN : 0 < N) (r : ℕ) :
    HasSum (fun xs : List (SearchTrace N) =>
      if r ∈ (sourceBBHTLaw T.indexOfRank hN).rankTrace xs then
        (sourceBBHTLaw T.indexOfRank hN).runMass T.skip 0 xs else 0) 0 := by
  exact bbht_visit_outside T hN 0 r hN (by omega)

end Qatlib.Concepts.AmplitudeSearch.Amplification
