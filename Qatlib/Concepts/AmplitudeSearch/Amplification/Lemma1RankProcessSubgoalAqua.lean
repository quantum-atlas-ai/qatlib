/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.Lemma1RankProcessSubgoalStat

/-!
# Inverse-rank hit probabilities

The module derives a recurrence for the probability of visiting rank `r` in a descending
uniform-rank experiment. `hitProbability_formula` gives probability `1 / r` exactly when `1 ≤ r
≤ t`, and zero otherwise.

`rankExperiment_uniform_interface` connects the experiment to the uniform successful-search
interface, and `lemma1RankProcessSubgoal` packages the rank calculation used in [DurrHoyer1996].

## Main statements

* `hitProbability_eq_inv`: proves the inverse-rank formula inside the starting range.
* `hitProbability_formula`: includes zero and out-of-range cases.
* `lemma1RankProcessSubgoal`: establishes the rank-process specification.

## References

* [Durr and Hoyer, 1996, Lemma 1][DurrHoyer1996]
-/

open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

/-- The rank-hit probability is zero when the initial candidate count is zero. -/
@[simp] theorem hitProbability_zero (r : ℕ) : hitProbability 0 r = 0 := by
  simp [hitProbability, rankExperiment, Experiment.probability, Experiment.expect]

/-- The rank experiment's expected payoff can be decomposed through any
`UniformSuccessfulSearch` interface and its lower-rank continuation experiment. -/
theorem rankExperiment_uniform_interface (search : UniformSuccessfulSearch)
    (t : ℕ) (payoff : List ℕ → ℚ) :
    (rankExperiment (t + 1)).expect payoff =
      (search.output t).expect (fun k =>
        (rankExperiment k.val).expect (fun tail => payoff ((k.val + 1) :: tail))) := by
  rw [search.uniform]
  simp only [rankExperiment, Experiment.expect, Experiment.expect_map]

/-- The hit probability for `t + 1` candidates is the uniform average of immediate-hit
indicators and lower-rank hit probabilities. -/
theorem hitProbability_succ (t r : ℕ) :
    hitProbability (t + 1) r =
      (∑ k : Fin (t + 1), if r = k.val + 1 then 1 else hitProbability k.val r) /
        (t + 1 : ℚ) := by
  simp only [hitProbability, rankExperiment, Experiment.probability, Experiment.expect,
    Experiment.expect_map]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : r = k.val + 1
  · simp [h]
  · simp [h]

/-- The hit probability vanishes for rank zero and for ranks larger than the initial candidate
count. -/
theorem hitProbability_outside (t r : ℕ) (h : r = 0 ∨ t < r) :
    hitProbability t r = 0 := by
  unfold hitProbability Experiment.probability
  calc
    _ = (rankExperiment t).expect (fun _ => 0) := by
      apply Experiment.expect_congr
      apply Experiment.all_mono _ (rankExperiment_valid t)
      intro trace htrace
      have hnot : r ∉ trace := by
        intro hr
        have hb := htrace.mem_bounds hr
        rcases h with h | h <;> omega
      simp [hnot]
    _ = 0 := Experiment.expect_const _ 0

/-- The candidate count times the hit probability equals the sum of immediate-hit indicators and
lower-rank hit probabilities. -/
private theorem weighted_hitProbability (t r : ℕ) :
    (t : ℚ) * hitProbability t r =
      ∑ k : Fin t, if r = k.val + 1 then 1 else hitProbability k.val r := by
  cases t with
  | zero => simp
  | succ t =>
    rw [hitProbability_succ]
    have hn : (t + 1 : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp

/-- The weighted hit probability at `t + 1` equals the weighted probability at `t` plus the new
boundary contribution. -/
theorem hitProbability_step (t r : ℕ) :
    (t + 1 : ℚ) * hitProbability (t + 1) r =
      (t : ℚ) * hitProbability t r +
        (if r = t + 1 then 1 else hitProbability t r) := by
  have h := weighted_hitProbability (t + 1) r
  rw [Fin.sum_univ_castSucc] at h
  simpa only [Nat.cast_add, Nat.cast_one, Fin.val_castSucc, Fin.val_last,
    ← weighted_hitProbability] using h

/-- For `1 ≤ r ≤ t`, the probability of visiting rank `r` equals `1 / r` [Durr and Hoyer, Lemma
1][DurrHoyer1996]. -/
theorem hitProbability_eq_inv (t r : ℕ) (hr : 1 ≤ r) (hrt : r ≤ t) :
    hitProbability t r = 1 / (r : ℚ) := by
  induction t with
  | zero => omega
  | succ t ih =>
    have hn : (t + 1 : ℚ) ≠ 0 := by positivity
    have hstep := hitProbability_step t r
    apply mul_left_cancel₀ hn
    by_cases heq : r = t + 1
    · have hprev := hitProbability_outside t r (Or.inr (by omega))
      rw [if_pos heq, hprev] at hstep
      rw [hstep, heq]
      push_cast
      field_simp
      ring
    · have hprev := ih (by omega)
      rw [if_neg heq, hprev] at hstep
      rw [hstep]
      ring

/-- The rank-hit probability is `1 / r` for `1 ≤ r ≤ t` and zero otherwise. -/
theorem hitProbability_formula (t r : ℕ) :
    hitProbability t r = if 1 ≤ r ∧ r ≤ t then 1 / (r : ℚ) else 0 := by
  split_ifs with h
  · exact hitProbability_eq_inv t r h.1 h.2
  · exact hitProbability_outside t r (by omega)

/-- The rank-process subgoal holds via the explicit inverse-rank hit-probability formula
[DurrHoyer1996]. -/
theorem lemma1RankProcessSubgoal : Lemma1RankProcessSubgoal := by
  intro t r
  exact hitProbability_formula t r

end Qatlib.Concepts.AmplitudeSearch.Amplification
