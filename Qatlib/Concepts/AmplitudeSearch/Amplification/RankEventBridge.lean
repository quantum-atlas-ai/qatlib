/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.BBHTCall

/-!
# Rank events for search call laws

The experiment `skipExperiment` models the decreasing rank process with threshold skips, and
`RankedCallLaw.rankTrace` extracts one-based ranks from concrete call traces. Expectation and
event-mass identities connect these concrete runs to finite rank experiments, while
`skipProbability_le` bounds visits by the distinct-rank process used in minimum finding
[DurrHoyer1996].

## Main statements

* `RankedCallLaw.rankTrace_expectation`: identifies nonnegative rank observables under the
  concrete run law.
* `RankedCallLaw.initialRankTrace_expectation`: includes the uniformly chosen initial rank.
* `skipProbability_le`: bounds rank visits in the process with threshold skips.

## References

* [Dürr and Høyer, 1996][DurrHoyer1996]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment
open Qatlib.Concepts.AmplitudeSearch.Amplification.RankedCallLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification.SortedRankedTable

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

/-- The finite rank experiment that samples a rank below the current threshold and continues
from `skip.next` of that rank. It returns the empty trace at threshold zero or above `N`. -/
def skipExperiment {N : ℕ} (skip : RankSkip N) : ℕ → Experiment (List ℕ)
  | 0 => .pure []
  | t + 1 => if ht : t + 1 ≤ N then
      .uniform t (fun k =>
        (skipExperiment skip (skip.next (k.castLE ht))).map (List.cons (k.val + 1)))
    else .pure []
termination_by t => t
decreasing_by
  have h := skip.le_rank (k.castLE ht)
  simp only [Fin.val_castLE] at h
  omega

/-- For a threshold at most `N`, the distinct-rank skip rule recovers `rankExperiment`. -/
theorem skipExperiment_distinct (N t : ℕ) (htN : t ≤ N) :
    skipExperiment (RankSkip.distinct N) t = rankExperiment t := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    cases t with
    | zero => simp only [skipExperiment, rankExperiment]
    | succ t =>
      rw [skipExperiment, dif_pos htN, rankExperiment]
      congr 1
      funext k
      simp only [RankSkip.distinct, Fin.val_castLE]
      exact congrArg (Experiment.map (List.cons (k.val + 1))) (ih k.val k.isLt (by omega))

/-- A sum over `Fin N` restricted to indices below `t` equals the corresponding sum over `Fin
t`, when `t ≤ N`. -/
private theorem sum_lower_values {N t : ℕ} (htN : t ≤ N) (V : Fin N → ℝ) :
    (∑ i : Fin N, if i.val < t then V i else 0) = ∑ k : Fin t, V (k.castLE htN) := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun i hi => (⟨i.val, (Finset.mem_filter.mp hi).2⟩ : Fin t))
  · intro i hi; exact Finset.mem_univ _
  · intro i hi j hj hij
    exact Fin.ext (congrArg (fun x : Fin t => x.val) hij)
  · intro k hk
    refine ⟨k.castLE htN, ?_, ?_⟩
    · simp [k.isLt]
    · rfl
  · intro i hi; rfl

namespace RankedCallLaw

variable {N : ℕ} {Ω : Type}

/-- The list of one-based output ranks extracted from a list of call outcomes. -/
def rankTrace (law : RankedCallLaw N Ω) (xs : List Ω) : List ℕ :=
  xs.map (fun x => (law.outputRank x).val + 1)

/-- For `t < N`, the weighted sum of any nonnegative observable of the concrete rank trace
equals its expectation under `skipExperiment skip t`. -/
theorem rankTrace_expectation (law : RankedCallLaw N Ω) (skip : RankSkip N)
    (t : ℕ) (htN : t < N) (F : List ℕ → ℝ) (hF : ∀ xs, 0 ≤ F xs) :
    HasSum (fun xs => law.runMass skip t xs * F (law.rankTrace xs))
      ((skipExperiment skip t).expectReal F) := by
  induction t using Nat.strong_induction_on generalizing F with
  | h t ih =>
    cases t with
    | zero =>
      have hc : HasSum (fun x : Ω × List Ω =>
          law.runMass skip 0 (x.1 :: x.2) * F (law.rankTrace (x.1 :: x.2))) 0 := by
        simpa only [runMass, if_pos rfl, ite_true, zero_mul] using!
          (hasSum_zero : HasSum (fun _ : Ω × List Ω => (0 : ℝ)) 0)
      have h := list_run_hasSum (fun xs => law.runMass skip 0 xs * F (law.rankTrace xs)) 0 hc
      simpa only [runMass, if_pos rfl, rankTrace, List.map_nil, one_mul, add_zero,
        skipExperiment, Experiment.expectReal, ite_true] using! h
    | succ t =>
      let V : Fin N → ℝ := fun i => (skipExperiment skip (skip.next i)).expectReal
        (fun tail => F ((i.val + 1) :: tail))
      have hfib (x : Ω) : HasSum (fun xs =>
          law.runMass skip (t + 1) (x :: xs) * F (law.rankTrace (x :: xs)))
          (law.mass (t + 1) x * V (law.outputRank x)) := by
        by_cases hx : (law.outputRank x).val < t + 1
        · have hnext : skip.next (law.outputRank x) < t + 1 := lt_of_le_of_lt (skip.le_rank _) hx
          have htail := ih _ hnext (lt_trans hnext htN)
            (fun tail => F (((law.outputRank x).val + 1) :: tail)) (fun _ => hF _)
          have h := htail.mul_left (law.mass (t + 1) x)
          convert! h using 1
          funext xs
          simp only [runMass, if_neg (by omega : ¬ t + 1 = 0), if_pos hx, rankTrace, List.map_cons]
          ring
        · have hz := law.lower_support (t + 1) (by omega) htN x hx
          simpa only [runMass, if_neg (by omega : ¬ t + 1 = 0), if_neg hx, hz, zero_mul]
            using hasSum_zero
      have hrow := law.continuation_finite (t + 1) (by omega) htN V
      have hprod := nonnegative_product_sum
        (fun x xs => law.runMass skip (t + 1) (x :: xs) * F (law.rankTrace (x :: xs)))
        (fun x xs => mul_nonneg (law.runMass_nonneg skip _ htN _) (hF _))
        _ _ hfib hrow
      have h :=
          list_run_hasSum (fun xs => law.runMass skip (t + 1) xs * F (law.rankTrace xs)) _ hprod
      simp only [runMass, if_neg (by omega : ¬ t + 1 = 0), zero_mul, zero_add] at h
      rw [sum_lower_values htN.le] at h
      rw [skipExperiment, dif_pos htN.le, Experiment.expectReal]
      simpa only [Experiment.expectReal_map, V, Fin.val_castLE, Nat.cast_add, Nat.cast_one] using! h

/-- The total run mass of call traces whose one-based rank trace contains `r`. -/
noncomputable def hitMass (law : RankedCallLaw N Ω) (skip : RankSkip N) (t r : ℕ) : ℝ :=
  ∑' xs : List Ω, if r ∈ law.rankTrace xs then law.runMass skip t xs else 0

/-- For `t < N`, the mass of concrete runs visiting rank `r` sums to its visit probability in
the finite experiment with threshold skips. -/
theorem hitMass_eq_tree (law : RankedCallLaw N Ω) (skip : RankSkip N)
    (t r : ℕ) (htN : t < N) :
    HasSum (fun xs => if r ∈ law.rankTrace xs then law.runMass skip t xs else 0)
      (((skipExperiment skip t).probability (fun trace => r ∈ trace) : ℚ) : ℝ) := by
  let f : List ℕ → ℚ := fun trace => if r ∈ trace then 1 else 0
  have h := law.rankTrace_expectation skip t htN (fun trace => (f trace : ℝ))
    (by intro trace; dsimp [f]; split_ifs <;> norm_num)
  rw [Experiment.expectReal_rat] at h
  convert! h using 1
  funext xs
  dsimp [f]
  split_ifs <;> norm_num

/-- The one-based initial rank prepended to the one-based output ranks of the subsequent calls. -/
def initialRankTrace (law : RankedCallLaw N Ω) (x : Fin N × List Ω) : List ℕ :=
  (x.1.val + 1) :: law.rankTrace x.2

/-- For `N > 0`, the initial run law and `skipExperiment skip N` give the same expectation for
every nonnegative rank-trace observable. -/
theorem initialRankTrace_expectation (law : RankedCallLaw N Ω) (skip : RankSkip N)
    (hN : 0 < N) (F : List ℕ → ℝ) (hF : ∀ xs, 0 ≤ F xs) :
    HasSum (fun x : Fin N × List Ω => law.initialMass skip x * F (law.initialRankTrace x))
      ((skipExperiment skip N).expectReal F) := by
  let V : Fin N → ℝ := fun i => (skipExperiment skip (skip.next i)).expectReal
    (fun tail => F ((i.val + 1) :: tail))
  have hfib (i : Fin N) : HasSum (fun xs =>
      law.initialMass skip (i, xs) * F (law.initialRankTrace (i, xs))) (V i / (N : ℝ)) := by
    have h := law.rankTrace_expectation skip (skip.next i)
      (lt_of_le_of_lt (skip.le_rank i) i.isLt) (fun tail => F ((i.val + 1) :: tail))
      (fun _ => hF _)
    convert! h.div_const (N : ℝ) using 1
    funext xs
    simp only [initialMass, initialRankTrace]
    ring
  have hrows : HasSum (fun i : Fin N => V i / (N : ℝ))
      ((∑ i : Fin N, V i) / (N : ℝ)) := by
    rw [Finset.sum_div]
    exact hasSum_fintype _
  have h := nonnegative_product_sum
    (fun i xs => law.initialMass skip (i, xs) * F (law.initialRankTrace (i, xs)))
    (fun i xs => mul_nonneg ((law.initialMass_normalized skip hN).2 (i, xs)) (hF _))
    _ _ hfib hrows
  have heq : (∑ i : Fin N, V i) / (N : ℝ) = (skipExperiment skip N).expectReal F := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
    rw [skipExperiment, dif_pos le_rfl, Experiment.expectReal]
    simp only [V, Experiment.expectReal_map, Fin.castLE_refl, Nat.cast_succ]
  rwa [heq] at h

/-- The total initial run mass of rank traces that visit `r`, including the initial rank. -/
noncomputable def initialHitMass (law : RankedCallLaw N Ω) (skip : RankSkip N) (r : ℕ) : ℝ :=
  ∑' x : Fin N × List Ω, if r ∈ law.initialRankTrace x then law.initialMass skip x else 0

/-- For `N > 0`, the initial mass of runs visiting `r` sums to its visit probability in
`skipExperiment skip N`. -/
theorem initialHitMass_eq_tree (law : RankedCallLaw N Ω) (skip : RankSkip N)
    (hN : 0 < N) (r : ℕ) :
    HasSum (fun x : Fin N × List Ω => if r ∈ law.initialRankTrace x then law.initialMass skip x else 0)
      (((skipExperiment skip N).probability (fun trace => r ∈ trace) : ℚ) : ℝ) := by
  let f : List ℕ → ℚ := fun trace => if r ∈ trace then 1 else 0
  have h := law.initialRankTrace_expectation skip hN (fun trace => (f trace : ℝ))
    (by intro trace; dsimp [f]; split_ifs <;> norm_num)
  rw [Experiment.expectReal_rat] at h
  convert! h using 1
  funext xs
  dsimp [f]
  split_ifs <;> norm_num

end RankedCallLaw

/-- The probability of visiting a fixed rank in `rankExperiment` is monotone in the initial rank
bound. -/
theorem hitProbability_monotone (r : ℕ) : Monotone (fun t => hitProbability t r) := by
  intro a b hab
  change hitProbability a r ≤ hitProbability b r
  by_cases hr : r = 0
  · subst r
    rw [hitProbability_outside a 0 (Or.inl rfl), hitProbability_outside b 0 (Or.inl rfl)]
  by_cases hra : r ≤ a
  · rw [hitProbability_eq_inv a r (by omega) hra,
      hitProbability_eq_inv b r (by omega) (le_trans hra hab)]
  · rw [hitProbability_outside a r (Or.inr (by omega))]
    exact Experiment.probability_nonneg _ _

/-- For a threshold at most `N`, the visit probability under any rank skip rule is bounded by
the visit probability in `rankExperiment`. -/
theorem skipProbability_le {N : ℕ} (skip : RankSkip N) (t r : ℕ) (htN : t ≤ N) :
    (skipExperiment skip t).probability (fun trace => r ∈ trace) ≤ hitProbability t r := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    cases t with
    | zero => simp [skipExperiment, Experiment.probability, Experiment.expect]
    | succ t =>
      rw [skipExperiment, dif_pos htN, hitProbability_succ]
      unfold Experiment.probability
      simp only [Experiment.expect, Experiment.expect_map]
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply Finset.sum_le_sum
      intro k _
      by_cases hr : r = k.val + 1
      · simp [hr]
      · simp only [List.mem_cons, hr, false_or, if_false]
        have hnext : skip.next (k.castLE htN) < t + 1 :=
          lt_of_le_of_lt (skip.le_rank _) k.isLt
        exact (ih _ hnext (by omega)).trans
          (hitProbability_monotone r (skip.le_rank (k.castLE htN)))

end Qatlib.Concepts.AmplitudeSearch.Amplification
