/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.Lemma1RankProcessSubgoalStat

open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

@[simp] theorem hitProbability_zero (r : ℕ) : hitProbability 0 r = 0 := by
  simp [hitProbability, rankExperiment, Experiment.probability, Experiment.expect]

theorem rankExperiment_uniform_interface (search : UniformSuccessfulSearch)
    (t : ℕ) (payoff : List ℕ → ℚ) :
    (rankExperiment (t + 1)).expect payoff =
      (search.output t).expect (fun k =>
        (rankExperiment k.val).expect (fun tail => payoff ((k.val + 1) :: tail))) := by
  rw [search.uniform]
  simp only [rankExperiment, Experiment.expect, Experiment.expect_map]

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

theorem hitProbability_step (t r : ℕ) :
    (t + 1 : ℚ) * hitProbability (t + 1) r =
      (t : ℚ) * hitProbability t r +
        (if r = t + 1 then 1 else hitProbability t r) := by
  have h := weighted_hitProbability (t + 1) r
  rw [Fin.sum_univ_castSucc] at h
  simpa only [Nat.cast_add, Nat.cast_one, Fin.val_castSucc, Fin.val_last,
    ← weighted_hitProbability] using h

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

theorem hitProbability_formula (t r : ℕ) :
    hitProbability t r = if 1 ≤ r ∧ r ≤ t then 1 / (r : ℚ) else 0 := by
  split_ifs with h
  · exact hitProbability_eq_inv t r h.1 h.2
  · exact hitProbability_outside t r (by omega)

theorem lemma1RankProcessSubgoal : Lemma1RankProcessSubgoal := by
  intro t r
  exact hitProbability_formula t r

end Qatlib.Concepts.AmplitudeSearch.Amplification
