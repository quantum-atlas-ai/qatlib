/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.OrderedSearchRefinedDefs
import Qatlib.Concepts.OrderedBayes.BayesRatioCore.OrderedSearch
import Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
import Qatlib.Concepts.OrderedBayes.BayesRatioCore.NoisyQuantumOracle
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Oracle semantics and information bounds for ordered search

This module proves refined probability, oracle, and information statements for the adaptive
ordered search setting of [BenOrHassidim2007]. It verifies a unitary noisy query backend and its
binary symmetric channel probabilities, distinguishes query costs from pending transition costs,
and checks posterior and lower bound formulas at boundary cases.

Finite entropy chain rules and Fano inequalities yield comparison lower bounds for binary and
cyclic report programs. The stopping and recursive constructions control information by the
expected number of comparisons, culminating in `clause17_rec_total_cost_capacity_bound` for a
decoder of the combined transcript.

## Main statements

* `clause13_cross_pair_joint_bound`: finite tree ratio threshold bound.
* `clause16_noisy_query_backend`: unitary backend with the stated noise semantics.
* `clause17_same_run_comparison_lower_bound`: Fano capacity bound for a fixed query count.
* `clause17_rec_total_cost_capacity_bound`: capacity bound for total expected recursive cost.

## References

* [Ben-Or and Hassidim, 2007][BenOrHassidim2007]
-/

set_option autoImplicit false

open Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma23Quan
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.OrderedBayes.BayesRatioCore.OrderedSearch

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

open scoped BigOperators Classical ENNReal NNReal
open Qatlib
open Qatlib.Concepts.OrderedBayes.BayesRatioCore
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels.OrderedSearch2007
open Qatlib.Concepts.OrderedBayes.BayesRatioCore
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels.OrderedSearch2007

/-- Identifies `CorrectEqualCutPosterior` with the true-answer Bayesian posterior at the cut
cell. -/
theorem clause12_correct_equal_cut_posterior {n : ℕ} (a : Fin n → ℝ) (c : Fin n) (p : ℝ) :
    CorrectEqualCutPosterior a c p = bayesTruePost a c p c := rfl

/-- For a nonnegative normalized prior with positive mass at the cut and another cell, the
printed update differs from the posterior when `1 / 2 < p < 1`. -/
theorem clause12_printed_mismatch_at_equal_cell {n : ℕ} (a : Fin n → ℝ) (c : Fin n)
    (p : ℝ) (hsum : (∑ m, a m) = 1) (hac : 0 < a c) (ha0 : ∀ m, 0 ≤ a m)
    (hother : ∃ m', m' ≠ c ∧ 0 < a m') (hp : 1 / 2 < p) (hp1 : p < 1) :
    PrintedUpdateIsNotThePosterior a c p :=
  printed_updateTrue_ne_bayesTruePost_at_equal a c p hsum hac ha0 hother hp hp1

/-- For a prior concentrated at the cut cell, the printed and Bayesian true-answer updates agree
there when `1 / 2 < p < 1`. -/
theorem clause12_degenerate_equal_cut_agrees {n : ℕ} (a : Fin n → ℝ) (c : Fin n) (p : ℝ)
    (hsum : (∑ m, a m) = 1) (hac : a c = 1) (hother : ∀ m, m ≠ c → a m = 0)
    (hp : 1 / 2 < p) (hp1 : p < 1) :
    updateTrue a c p c = bayesTruePost a c p c :=
  printed_updateTrue_eq_bayesTruePost_at_equal_degenerate a c p hsum hac hother hp hp1

/-- For `0 < p < 1` and `R > 0`, the finite tree weight of a terminal likelihood ratio at least
`R`, starting from the empty record, is at most `1 / R`. -/
theorem clause13_cross_pair_joint_bound {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u v : Fin n) (R : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hR : 0 < R) :
    ∀ m : ℕ, treeCross hn p ε u v R m [] ≤ 1 / R :=
  cross_pair_joint_bound hn p ε u v R hp hp1 hR

/-- Establishes `CrossPairCalibration` for positive `δ` and `0 < p < 1`, calibrating the ratio
threshold to the desired bound. -/
theorem clause14_r_delta_calibration {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u v : Fin n) (δ : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hδ : 0 < δ) :
    CrossPairCalibration hn p ε u v δ := by
  refine ⟨hp, hp1, hδ, ?_⟩
  intro m
  exact r_delta_calibration hn p ε u v δ hp hp1 hδ m

/-- Complex conjugation fixes each entry of the real-valued noise rotation. -/
lemma clause16_starRingEnd_noiseRotation_entry (p : ℝ) (t : Bool) (i j : Fin 2) :
    starRingEnd ℂ (noiseRotation p t i j) = noiseRotation p t i j := by
  fin_cases i <;> fin_cases j <;> cases t <;> simp [noiseRotation, Complex.conj_ofReal]

/-- The matrix star of a noise rotation has entries given by transposing its indices. -/
lemma clause16_star_noiseRotation (p : ℝ) (t : Bool) (i j : Fin 2) :
    star (noiseRotation p t) i j = noiseRotation p t j i := by
  have h : star (noiseRotation p t) i j
      = starRingEnd ℂ (noiseRotation p t j i) := by
    simp [Matrix.conjTranspose_apply]
  rw [h, starRingEnd_apply]
  fin_cases i <;> fin_cases j <;> cases t <;>
    simp [noiseRotation, Complex.conj_ofReal] <;> ring

/-- For `0 ≤ p ≤ 1`, the matrix star of a noise rotation multiplied by the rotation is the
identity. -/
theorem clause16_noise_rotation_is_unitary (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (t : Bool) :
    star (noiseRotation p t) * noiseRotation p t = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> cases t <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, noiseRotation,
      clause16_star_noiseRotation]
  all_goals refine Complex.ext ?_ ?_
  all_goals try { simp [Complex.mul_im, Complex.add_im, Complex.neg_im] }
  all_goals simp [Complex.mul_re, Complex.add_re, Complex.neg_re]
  all_goals nlinarith [Real.sq_sqrt hp0, Real.sq_sqrt (show (0 : ℝ) ≤ 1 - p by linarith)]

/-- Computes the matrix star of the noisy query oracle block by block as transposed noise
rotations. -/
lemma clause16_star_noisyQueryOracle {n : ℕ} (rank : Fin n) (p : ℝ) (x y : Fin n × Fin 2) :
    star (noisyQueryOracle rank p) x y =
      if y.1 = x.1 then noiseRotation p (truthBit rank x.1) y.2 x.2 else 0 := by
  have h : star (noisyQueryOracle rank p) x y
      = starRingEnd ℂ (noisyQueryOracle rank p y x) := by
    simp [Matrix.conjTranspose_apply]
  rw [h]
  by_cases hc : y.1 = x.1
  · rw [if_pos hc]
    rw [show noisyQueryOracle rank p y x = noiseRotation p (truthBit rank x.1) y.2 x.2 by
          simp only [noisyQueryOracle, if_pos hc]]
    exact clause16_starRingEnd_noiseRotation_entry p (truthBit rank x.1) y.2 x.2
  · rw [if_neg hc]
    rw [show noisyQueryOracle rank p y x = 0 by simp only [noisyQueryOracle, if_neg hc]]
    simp

/-- The noisy query oracle belongs to the matrix unitary group when `0 ≤ p ≤ 1`. -/
theorem clause16_noisy_query_oracle_is_unitary {n : ℕ} (rank : Fin n) (p : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) :
    noisyQueryOracle rank p ∈ Matrix.unitaryGroup (Fin n × Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext x x'
  have key : ∀ (x x' : Fin n × Fin 2),
      (star (noisyQueryOracle rank p) * noisyQueryOracle rank p) x x'
        = if x.1 = x'.1 then
            (star (noiseRotation p (truthBit rank x.1))
              * noiseRotation p (truthBit rank x.1)) x.2 x'.2
          else 0 := by
    intro x x'
    simp only [Matrix.mul_apply]
    have hmul : ∀ (z : Fin n × Fin 2),
        star (noisyQueryOracle rank p) x z * noisyQueryOracle rank p z x'
          = if z.1 = x.1 ∧ z.1 = x'.1 then
              noiseRotation p (truthBit rank x.1) z.2 x.2
                * noiseRotation p (truthBit rank x'.1) z.2 x'.2
            else 0 := by
      intro z
      rw [clause16_star_noisyQueryOracle]
      by_cases h1 : z.1 = x.1
      · by_cases h2 : z.1 = x'.1
        · rw [if_pos h1]
          rw [show noisyQueryOracle rank p z x'
                = noiseRotation p (truthBit rank x'.1) z.2 x'.2 by
              simp only [noisyQueryOracle, if_pos h2]]
          rw [if_pos (And.intro h1 h2)]
        · rw [if_pos h1]
          rw [show noisyQueryOracle rank p z x' = 0 by
              simp only [noisyQueryOracle, if_neg h2]]
          rw [if_neg (fun h => h2 h.2)]
          simp
      · rw [if_neg h1]
        rw [if_neg (fun h => h1 h.1)]
        simp
    rw [Fintype.sum_congr _ _ hmul]
    by_cases hxy : x.1 = x'.1
    · rw [← hxy]
      have hsplit : ∀ (z : Fin n × Fin 2),
          (if z.1 = x.1 ∧ z.1 = x.1 then
              noiseRotation p (truthBit rank x.1) z.2 x.2
                * noiseRotation p (truthBit rank x.1) z.2 x'.2
            else 0)
          = (if z.1 = x.1 then
              (noiseRotation p (truthBit rank x.1) z.2 x.2
                * noiseRotation p (truthBit rank x.1) z.2 x'.2)
            else 0) := by
        intro z
        by_cases hz : z.1 = x.1
        · simp [hz]
        · simp [hz]
      rw [Fintype.sum_congr _ _ hsplit]
      rw [Fintype.sum_prod_type]
      have hinner : ∀ (y : Fin n),
          (∑ k : Fin 2, (if y = x.1 then
              noiseRotation p (truthBit rank x.1) k x.2
                * noiseRotation p (truthBit rank x.1) k x'.2
            else 0))
          = (if y = x.1 then
              (∑ k : Fin 2, (noiseRotation p (truthBit rank x.1) k x.2
                  * noiseRotation p (truthBit rank x.1) k x'.2))
            else 0) := by
        intro y
        by_cases hy : y = x.1
        · simp [hy]
        · simp [hy]
      rw [Fintype.sum_congr _ _ hinner]
      rw [Fintype.sum_eq_single x.1 (fun y hy => by simp [hy])]
      simp only [Matrix.mul_apply, clause16_star_noiseRotation]
    · rw [if_neg hxy]
      have hnone : ∀ z : Fin n × Fin 2, ¬ (z.1 = x.1 ∧ z.1 = x'.1) := by
        intro z hz
        exact hxy (hz.1.symm.trans hz.2)
      simp [hnone]
  rw [key]
  by_cases h : x.1 = x'.1
  · rw [if_pos h, clause16_noise_rotation_is_unitary p hp0 hp1]
    simp only [Matrix.one_apply]
    by_cases h2 : x.2 = x'.2
    · have hxy : x = x' := Prod.ext_iff.mpr ⟨h, h2⟩
      simp [h2, hxy]
    · have hne : x ≠ x' := by
        intro he
        exact h2 (Prod.ext_iff.mp he).2
      simp [h2, hne]
  · rw [if_neg h]
    simp only [Matrix.one_apply]
    have hne : x ≠ x' := by
      intro he
      exact h (Prod.ext_iff.mp he).1
    simp [hne]

/-- Converting a Boolean to its answer-register index and back returns the original Boolean. -/
lemma clause16_boolIndex_answerBit (b : Bool) : answerBit (boolIndex b) = b := by
  cases b <;> simp [boolIndex, answerBit]

/-- The first column of the noise rotation equals the complex embedding of the corresponding
noise amplitudes. -/
lemma clause16_noiseRotation_first_column (p : ℝ) (truth : Bool) (answer : Fin 2) :
    noiseRotation p truth answer 0 =
      (noiseAmplitude p truth (answerBit answer) : ℂ) := by
  fin_cases answer <;> cases truth <;> simp [noiseRotation, noiseAmplitude, answerBit]

/-- For `0 ≤ p ≤ 1`, the backend answer probability is `p` for the truth bit and `1 - p` for the
opposite answer. -/
theorem clause16_backend_bsc_law (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (truth answer : Bool) :
    noiseAnswerProb p truth answer = if answer = truth then p else 1 - p := by
  cases answer <;> cases truth <;>
    simp [noiseAnswerProb, noiseAmplitude, Real.sq_sqrt hp0,
      Real.sq_sqrt (show (0 : ℝ) ≤ 1 - p by linarith)]

/-- The true and false backend answer probabilities sum to one when `0 ≤ p ≤ 1`. -/
theorem clause16_backend_answer_probability_sum (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (truth : Bool) :
    noiseAnswerProb p truth true + noiseAnswerProb p truth false = 1 := by
  cases truth <;>
    simp [noiseAnswerProb, noiseAmplitude, Real.sq_sqrt hp0,
      Real.sq_sqrt (show (0 : ℝ) ≤ 1 - p by linarith)]

/-- The noisy oracle entry from a zero answer register equals the noise amplitude for the
comparison truth bit and observed answer. -/
theorem clause16_backend_answer_amplitude {n : ℕ} (rank : Fin n) (p : ℝ) (x : Fin n)
    (answer : Bool) :
    noisyQueryOracle rank p (x, boolIndex answer) (x, ⟨0, by decide⟩) =
      (noiseAmplitude p (truthBit rank x) answer : ℂ) := by
  have h : noisyQueryOracle rank p (x, boolIndex answer) (x, ⟨0, by decide⟩)
      = noiseRotation p (truthBit rank x) (boolIndex answer) 0 := by
    simp [noisyQueryOracle]
  rw [h, clause16_noiseRotation_first_column]
  simp [clause16_boolIndex_answerBit]

/-- For `1 / 2 < p < 1`, the classical true-answer probability is `p` or `1 - p` according to
the comparison truth bit. -/
theorem clause16_backend_matches_classical_bsc {n : ℕ} (rank : Fin n) (p : ℝ)
    (hp : 1 / 2 < p) (hp1 : p < 1) (x : Fin n) :
    (truthAnswerProb rank x p : ℝ) =
      if truthBit rank x = true then p else 1 - p := by
  rw [truthAnswerProb_eq rank x hp hp1]
  by_cases h : x.val ≤ rank.val
  · simp [truthBit, h]
  · simp [truthBit, h]

/-- Every entry of a noise rotation lies in the specified noise field. -/
lemma clause16_noiseRotation_inNoiseField (p : ℝ) (t : Bool) (i j : Fin 2) :
    InNoiseField p (noiseRotation p t i j) := by
  fin_cases i <;> fin_cases j <;> cases t
  · exact ⟨0, 1, 0, 0, by simp [noiseRotation] <;> ring⟩
  · exact ⟨0, 0, 1, 0, by simp [noiseRotation] <;> ring⟩
  · exact ⟨0, 0, -1, 0, by simp [noiseRotation] <;> ring⟩
  · exact ⟨0, 1, 0, 0, by simp [noiseRotation] <;> ring⟩
  · exact ⟨0, 0, 1, 0, by simp [noiseRotation] <;> ring⟩
  · exact ⟨0, 1, 0, 0, by simp [noiseRotation] <;> ring⟩
  · exact ⟨0, 1, 0, 0, by simp [noiseRotation] <;> ring⟩
  · exact ⟨0, 0, -1, 0, by simp [noiseRotation] <;> ring⟩

/-- Every entry of the noisy query oracle satisfies `InNoiseField`. -/
theorem clause16_backend_entries_are_finite_bit {n : ℕ} (rank : Fin n) (p : ℝ)
    (b a : Fin n × Fin 2) :
    InNoiseField p (noisyQueryOracle rank p b a) := by
  by_cases h : b.1 = a.1
  · rw [noisyQueryOracle, if_pos h]
    exact clause16_noiseRotation_inNoiseField p (truthBit rank a.1) b.2 a.2
  · rw [noisyQueryOracle, if_neg h]
    exact ⟨0, 0, 0, 0, by simp⟩

/-- Constructs `NoisyQueryBackend` for the given rank and any `0 ≤ p ≤ 1`. -/
theorem clause16_noisy_query_backend {n : ℕ} (rank : Fin n) (p : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) :
    NoisyQueryBackend n rank p := by
  refine ⟨hp0, hp1, clause16_noisy_query_oracle_is_unitary rank p hp0 hp1, ?_, ?_⟩
  · intro truth answer
    exact clause16_backend_bsc_law p hp0 hp1 truth answer
  · intro b a
    exact clause16_backend_entries_are_finite_bit rank p b a

/-- The printed oracle fails the identity `U† U = 1`. -/
theorem clause16_printed_oracle_is_not_unitary :
    printedOracle.conjTranspose * printedOracle ≠ 1 := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
    Matrix.one_apply, printedOracle] at h01
  norm_num at h01

/-- The proposition `NoisyQuantumOracleContract` is false. -/
theorem clause16_frozen_noisy_oracle_is_refuted : ¬ NoisyQuantumOracleContract :=
  noisyQuantumOracle_obstruction

/-- A truth-step transition has zero expected query cost when some posterior cell reaches the
halting threshold. -/
theorem clause16_truth_step_halt_charges_zero {n : ℕ} (hn : 0 < n) (rank : Fin n)
    (p ε : ℝ) (a : Fin n → ℝ) (hhalts : ∃ i : Fin n, ε ≤ a i) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (truthStepCosted hn rank p ε a) = 0 := by
  rw [truthStepCosted, dif_pos hhalts,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost_ret]

/-- A truth-step transition has expected query cost one when no posterior cell reaches the
halting threshold. -/
theorem clause16_truth_step_running_charges_one {n : ℕ} (hn : 0 < n) (rank : Fin n)
    (p ε : ℝ) (a : Fin n → ℝ) (hruns : ¬ ∃ i : Fin n, ε ≤ a i) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (truthStepCosted hn rank p ε a) = 1 := by
  rw [truthStepCosted, dif_neg hruns, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost,
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
  simp [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const]

/-- The pending-state tick has expected cost one for every posterior state. -/
theorem clause16_pending_ledger_charges_the_halt {n : ℕ} (hn : 0 < n) (rank : Fin n)
    (p ε : ℝ) (a : Fin n → ℝ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost
      (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution.tick (trueLearnerNext hn rank p ε) (.inr a)) = 1 := by
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost,
      Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution.tick, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
  simp [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const]

/-- At a halting posterior, the truth-step query cost is zero while the pending-state tick cost
is one. -/
theorem clause16_query_ledger_differs_from_pending_ledger {n : ℕ} (hn : 0 < n)
    (rank : Fin n) (p ε : ℝ) (a : Fin n → ℝ) (hhalts : ∃ i : Fin n, ε ≤ a i) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (truthStepCosted hn rank p ε a) = 0 ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost
        (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution.tick (trueLearnerNext hn rank p ε) (.inr a)) = 1 :=
  ⟨clause16_truth_step_halt_charges_zero hn rank p ε a hhalts,
    clause16_pending_ledger_charges_the_halt hn rank p ε a⟩

/-- Expresses `binEntropy` as Mathlib's binary entropy divided by `log 2`. -/
theorem clause17_binEntropy_eq_mathlib (δ : ℝ) :
    binEntropy δ = Real.binEntropy δ / Real.log 2 := by
  rw [binEntropy, Real.binEntropy]
  simp only [Real.log_inv]
  ring

/-- Binary entropy is invariant under replacing `δ` by `1 - δ`. -/
theorem clause17_binEntropy_symmetry (δ : ℝ) : binEntropy δ = binEntropy (1 - δ) := by
  simp [binEntropy, add_comm, add_left_comm, add_assoc]

/-- The information per query equals one at noiseless parameter `p = 1`. -/
theorem clause17_queryInfo_one : queryInfo (1 : ℝ) = 1 := by
  rw [queryInfo, clause17_binEntropy_eq_mathlib, Real.binEntropy_one]
  ring

/-- The information per query is positive when `1 / 2 < p < 1`. -/
theorem clause17_queryInfo_pos {p : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) :
    0 < queryInfo p := by
  have hi := zoo_bayes_queryInfo_quadratic_lower hp hp1
  norm_num at hi
  nlinarith

/-- The one-comparison experiment returns the truth with probability `3 / 4`. -/
theorem clause17_one_comparison_success {truth : Bool} :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (oneComparison truth) (fun x => x.1 = truth) = (3 / 4 : ℝ≥0∞) := by
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event, oneComparison,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
  simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure]
  simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation, tsum_fintype,
      Fintype.sum_bool]
  rw [PMF.bernoulli_apply _ true, PMF.bernoulli_apply _ false]
  norm_num

/-- The one-comparison experiment has expected cost one. -/
theorem clause17_one_comparison_cost {truth : Bool} :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (oneComparison truth) = 1 := by
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost, oneComparison,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
  simp [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const]

/-- Expands Mathlib's binary entropy at `3 / 4` as a weighted sum of `log (4 / 3)` and `log 4`. -/
lemma clause17_binEntropy_three_quarters :
    Real.binEntropy (3 / 4 : ℝ) = (3 / 4) * Real.log (4 / 3 : ℝ) + (1 / 4) * Real.log 4 := by
  rw [Real.binEntropy]
  simp only [Real.log_inv]
  have h1 : (1 : ℝ) - 3 / 4 = 1 / 4 := by norm_num
  rw [h1]
  rw [Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (4 : ℝ) ≠ 0),
    Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (4 : ℝ) ≠ 0),
    Real.log_div (by norm_num : (4 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)]
  simp only [Real.log_one]
  ring

/-- The binary entropy expression is strictly less than one away from `δ = 1 / 2`. -/
theorem clause17_binEntropy_lt_one {δ : ℝ} (hδ : δ ≠ 1 / 2) : binEntropy δ < 1 := by
  rw [clause17_binEntropy_eq_mathlib]
  have hδ' : δ ≠ (2 : ℝ)⁻¹ := by rwa [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num] at hδ
  have h := (Real.binEntropy_lt_log_two).2 hδ'
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_lt_iff₀ hlog2]
  linarith

/-- The corrected two-cell capacity bound at correctness `3 / 4` and error `1 / 4` equals one. -/
theorem clause17_fano_bound_at_source_counterexample :
    fanoCapacityBound 2 (3 / 4 : ℝ) (1 / 4 : ℝ) = 1 := by
  have hsym : binEntropy (1 / 4 : ℝ) = binEntropy (3 / 4 : ℝ) := by
    rw [clause17_binEntropy_symmetry]
    norm_num
  have hI : queryInfo (3 / 4 : ℝ) = 1 - binEntropy (3 / 4 : ℝ) := rfl
  have hlog2ne : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hbinlt : binEntropy (3 / 4 : ℝ) < 1 := clause17_binEntropy_lt_one (by norm_num)
  have hden : (1 - binEntropy (3 / 4 : ℝ)) ≠ 0 := by linarith
  unfold fanoCapacityBound fanoNumerator
  rw [hsym, hI]
  rw [show (Real.log ((1 : ℕ) : ℝ)) = 0 by simp]
  rw [div_eq_iff hden]
  field_simp
  norm_num
  ring

/-- For `1 / 2 < p < 1`, `fanoCapacityBound 2 p p` equals one. -/
theorem clause17_fano_bound_tight_for_two_cells {p : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) :
    fanoCapacityBound 2 p p = 1 := by
  have hsym : binEntropy p = binEntropy (1 - p) := clause17_binEntropy_symmetry p
  have hI : queryInfo p = 1 - binEntropy p := rfl
  have hlog2ne : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hbinlt : binEntropy p < 1 := clause17_binEntropy_lt_one (by linarith)
  have hden : (1 - binEntropy p) ≠ 0 := by linarith
  unfold fanoCapacityBound fanoNumerator
  rw [hsym, hI]
  rw [show (Real.log ((1 : ℕ) : ℝ)) = 0 by simp]
  rw [div_eq_iff hden]
  field_simp
  rw [hsym.symm]
  ring

/-- The printed bound at two cells, correctness `3 / 4`, and error `1 / 4` is strictly greater
than one. -/
theorem clause17_printed_bound_is_false_at_source_parameters :
    1 < printedT26Bound 2 (3 / 4 : ℝ) (1 / 4 : ℝ) := by
  have hL2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hL4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hM : Real.log (1 / (1 - 1 / 4 : ℝ)) = Real.log (4 / 3 : ℝ) := by
    congr 1
    norm_num
  have hMlt : Real.log (4 / 3 : ℝ) < Real.log 4 := by
    apply Real.log_lt_log
    · norm_num
    · norm_num
  have hbinlt : Real.binEntropy (3 / 4 : ℝ) < Real.log 2 :=
    (Real.binEntropy_lt_log_two).2 (by norm_num)
  have hden : 0 < Real.log 2 - Real.binEntropy (3 / 4 : ℝ) := by linarith
  have hden2 : 0 < 1 - Real.binEntropy (3 / 4 : ℝ) / Real.log 2 := by
    have h1 : 1 - Real.binEntropy (3 / 4 : ℝ) / Real.log 2
        = (Real.log 2 - Real.binEntropy (3 / 4 : ℝ)) / Real.log 2 := by
      field_simp
    rw [h1]
    exact div_pos hden hL2pos
  have hA : Real.log (↑2 : ℝ) = Real.log 2 := by norm_num
  have hI : queryInfo (3 / 4 : ℝ) = 1 - binEntropy (3 / 4 : ℝ) := rfl
  unfold printedT26Bound
  rw [hM, hI, clause17_binEntropy_eq_mathlib, hA]
  rw [lt_div_iff₀ hden2]
  rw [clause17_binEntropy_three_quarters, hL4]
  field_simp
  have hH : Real.binEntropy (3 / 4 : ℝ) > Real.log (4 / 3 : ℝ) := by
    rw [clause17_binEntropy_three_quarters, hL4]
    have h1 : Real.log (4 / 3 : ℝ) < Real.log 4 := hMlt
    rw [hL4] at h1
    nlinarith
  linarith

/-- The one-comparison experiment has cost one and success `3 / 4`, matching the corrected
two-cell capacity bound at error `1 / 4`. -/
theorem clause17_source_counterexample_saturates_the_corrected_bound {truth : Bool} :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (oneComparison truth) = 1 ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (oneComparison truth) (fun x => x.1 = truth) = (3 / 4 : ℝ≥0∞) ∧
      fanoCapacityBound 2 (3 / 4 : ℝ) (1 / 4 : ℝ) = 1 := by
  exact ⟨clause17_one_comparison_cost, clause17_one_comparison_success,
    clause17_fano_bound_at_source_counterexample⟩

/-- For two cells and `1 / 2 < p ≤ 1`, the capacity bound at error `1 / 2` is zero. -/
theorem clause17_fano_bound_at_error_boundary_two_cells {p : ℝ} (hp : 1 / 2 < p)
    (hp1 : p ≤ 1) : fanoCapacityBound 2 p (1 / 2 : ℝ) = 0 := by
  have hbin : binEntropy (1 / 2 : ℝ) = 1 := by
    have hhalf : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
    rw [clause17_binEntropy_eq_mathlib, hhalf, Real.binEntropy_two_inv]
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    field_simp
  have hI : queryInfo p = 1 - binEntropy p := rfl
  have hlog2ne : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hbinlt : binEntropy p < 1 := clause17_binEntropy_lt_one (by linarith)
  have hden : (1 - binEntropy p) ≠ 0 := by linarith
  unfold fanoCapacityBound fanoNumerator
  rw [hbin, hI]
  rw [show (Real.log ((1 : ℕ) : ℝ)) = 0 by simp]
  rw [div_eq_iff hden]
  field_simp
  ring

/-- Establishes `FanoCapacityContract` for at least two cells, `1 / 2 < p ≤ 1`, and `0 ≤ δ ≤ 1 -
1 / n`. -/
theorem clause17_fano_capacity_contract {n : ℕ} (hn : 2 ≤ n) {p δ : ℝ} (hp : 1 / 2 < p)
    (hp1 : p ≤ 1) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 - 1 / (n : ℝ)) :
    FanoCapacityContract n p δ := by
  have hpos : 0 < queryInfo p := by
    rcases lt_or_eq_of_le hp1 with hlt | heq
    · exact clause17_queryInfo_pos hp hlt
    · rw [heq, clause17_queryInfo_one]
      norm_num
  refine ⟨hn, hp, hp1, hδ, hδ', hpos, ?_, ?_⟩
  · exact clause17_fano_bound_at_error_boundary_two_cells hp hp1
  · intro p' hp' hp'1
    exact clause17_fano_bound_tight_for_two_cells hp' hp'1

/-- Pulls a constant left factor out of a sum over a finite type. -/
theorem sum_const_mul {ι : Type} [Fintype ι] (c : ℝ) (f : ι → ℝ) :
    ∑ i, c * f i = c * ∑ i, f i := by
  rw [Finset.sum_congr rfl (fun i _ => mul_comm c (f i)), ← Finset.sum_mul, mul_comm]

/-- The function `xlog2` vanishes at zero. -/
theorem xlog2_zero : xlog2 0 = 0 := by
  simp [xlog2]

/-- For positive factors, expands `xlog2 (x * y)` as `y * xlog2 x + x * xlog2 y`. -/
theorem xlog2_mul (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    xlog2 (x * y) = y * xlog2 x + x * xlog2 y := by
  unfold xlog2
  rw [Real.log_mul hx.ne' hy.ne']
  ring

/-- For nonnegative joint weights, a conditional row with nonzero left marginal sums to one. -/
theorem condW_sum {α β : Type} [Fintype α] [Fintype β] (d : α × β → ℝ)
    (hd : ∀ i j, 0 ≤ d (i, j)) (i : α) (hm : margL d i ≠ 0) :
    ∑ j, condW d i j = 1 := by
  have hpos : 0 < margL d i := lt_of_le_of_ne
    (Finset.sum_nonneg fun j _ => hd i j) (by exact fun h => hm h.symm)
  simp only [condW, dif_neg hm]
  rw [← Finset.sum_div]
  exact div_self hpos.ne'

/-- Decomposes `xlog2` of a nonnegative joint weight into its left-marginal and
conditional-weight contributions. -/
theorem xlog2_joint_cell {α β : Type} [Fintype α] [Fintype β] (d : α × β → ℝ)
    (hd : ∀ i j, 0 ≤ d (i, j)) (i : α) (j : β) :
    xlog2 (d (i, j)) = condW d i j * xlog2 (margL d i)
      + d (i, j) * (Real.log (condW d i j) / Real.log 2) := by
  by_cases hm : margL d i = 0
  · have hle : d (i, j) ≤ margL d i := by
      unfold margL
      exact Finset.single_le_sum (f := fun j => d (i, j)) (fun j _ => hd i j)
        (Finset.mem_univ j)
    have hdnonneg : 0 ≤ d (i, j) := hd i j
    have hd0 : d (i, j) = 0 := by linarith
    simp [condW, hm, hd0, xlog2]
  · by_cases hd0 : d (i, j) = 0
    · simp [condW, hm, hd0, xlog2]
    · have hpos : 0 < d (i, j) := lt_of_le_of_ne (hd i j) (Ne.symm hd0)
      have hmp : 0 < margL d i := lt_of_le_of_ne
        (Finset.sum_nonneg fun j _ => hd i j) (by exact fun h => hm h.symm)
      have hcw : condW d i j = d (i, j) / margL d i := by simp [condW, hm]
      have hne : d (i, j) ≠ 0 := hd0
      have hne' : margL d i ≠ 0 := hm
      rw [hcw]
      have hmul : d (i, j) / margL d i * margL d i = d (i, j) := by
        field_simp
      have hlog : Real.log (d (i, j) / margL d i) = Real.log (d (i, j)) - Real.log (margL d i) :=
        Real.log_div hne hne'
      unfold xlog2
      rw [hlog]
      field_simp
      ring

/-- Multiplying `xlog2` of a left marginal by the sum of its conditional row leaves it
unchanged, including zero marginal rows. -/
theorem xlog2_margL_mul_condW_sum {α β : Type} [Fintype α] [Fintype β] (d : α × β → ℝ)
    (hd : ∀ i j, 0 ≤ d (i, j)) (i : α) :
    xlog2 (margL d i) * (∑ j, condW d i j) = xlog2 (margL d i) := by
  by_cases hm : margL d i = 0
  · simp [condW, hm, xlog2]
  · rw [condW_sum d hd i hm]
    ring

/-- Splits the sum of joint `xlog2` terms into left-marginal terms and weighted conditional
logarithms. -/
theorem sum_xlog2_joint {α β : Type} [Fintype α] [Fintype β] (d : α × β → ℝ)
    (hd : ∀ i j, 0 ≤ d (i, j)) :
    (∑ i, ∑ j, xlog2 (d (i, j)))
      = (∑ i, xlog2 (margL d i))
        + ∑ i, ∑ j, d (i, j) * (Real.log (condW d i j) / Real.log 2) := by
  have key : ∀ i j, xlog2 (d (i, j))
      = condW d i j * xlog2 (margL d i)
        + d (i, j) * (Real.log (condW d i j) / Real.log 2) :=
    fun i j => xlog2_joint_cell d hd i j
  have hinner (i : α) : (∑ j, condW d i j * xlog2 (margL d i))
      = xlog2 (margL d i) * (∑ j, condW d i j) := by
    rw [← Finset.sum_mul, mul_comm]
  calc
    (∑ i, ∑ j, xlog2 (d (i, j)))
        = ∑ i, ∑ j, (condW d i j * xlog2 (margL d i)
            + d (i, j) * (Real.log (condW d i j) / Real.log 2)) := by
          rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => key i j))]
    _ = (∑ i, ∑ j, condW d i j * xlog2 (margL d i))
        + ∑ i, ∑ j, d (i, j) * (Real.log (condW d i j) / Real.log 2) := by
          simp only [Finset.sum_add_distrib]
    _ = (∑ i, xlog2 (margL d i) * (∑ j, condW d i j))
        + ∑ i, ∑ j, d (i, j) * (Real.log (condW d i j) / Real.log 2) := by
          rw [Finset.sum_congr rfl (fun i _ => hinner i)]
    _ = (∑ i, xlog2 (margL d i))
        + ∑ i, ∑ j, d (i, j) * (Real.log (condW d i j) / Real.log 2) := by
          rw [Finset.sum_congr rfl (fun i _ => xlog2_margL_mul_condW_sum d hd i)]

/-- For nonnegative finite joint weights, joint entropy equals left-marginal entropy plus
conditional entropy. -/
theorem entH_chain_rule {α β : Type} [Fintype α] [Fintype β] (d : α × β → ℝ)
    (hd : ∀ i j, 0 ≤ d (i, j)) :
    entH d = entH (margL d) + condEntH d := by
  unfold entH condEntH
  rw [Fintype.sum_prod_type]
  have h := sum_xlog2_joint d hd
  linarith

/-- A nonnegative vector on a nonempty `Fin m` with total weight `m` has nonnegative sum `∑ i, u
i * log (u i)`. -/
theorem sum_mul_log_nonneg {m : ℕ} (u : Fin m → ℝ) (hu : ∀ i, 0 ≤ u i)
    (husum : ∑ i, u i = (m : ℝ)) (hm : 0 < m) :
    ∑ i, u i * Real.log (u i) ≥ 0 := by
  have hcard : (Finset.univ : Finset (Fin m)).card = m := Finset.card_fin m
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hw0 : ∀ i ∈ (Finset.univ : Finset (Fin m)), 0 ≤ (1 / (m : ℝ)) := by
    intro i _; positivity
  have hw1 : ∑ i ∈ (Finset.univ : Finset (Fin m)), (1 / (m : ℝ)) = 1 := by
    rw [Finset.sum_const, hcard]
    simp only [nsmul_eq_mul]
    field_simp
  have hmem : ∀ i ∈ (Finset.univ : Finset (Fin m)), u i ∈ Set.Ici (0 : ℝ) := by
    intro i _; exact (Set.mem_Ici).2 (hu i)
  have h := Real.convexOn_mul_log.map_sum_le
    (t := (Finset.univ : Finset (Fin m)))
    (w := fun _ => 1 / (m : ℝ)) (p := u) hw0 hw1 hmem
  (try dsimp only at h)
  simp only [smul_eq_mul] at h
  have hleft : (∑ i, (1 / (m : ℝ)) * u i) = 1 := by
    rw [sum_const_mul, husum]
    field_simp
  have h' : (∑ i, (1 / (m : ℝ)) * (u i * Real.log (u i)))
      = (1 / (m : ℝ)) * (∑ i, u i * Real.log (u i)) := by
    rw [sum_const_mul]
  have h2 : 0 ≤ (1 / (m : ℝ)) * (∑ i, u i * Real.log (u i)) := by
    have h3 : (∑ i, (1 / (m : ℝ)) * u i) * Real.log (∑ i, (1 / (m : ℝ)) * u i)
        ≤ ∑ i, (1 / (m : ℝ)) * (u i * Real.log (u i)) := h
    rw [hleft] at h3
    simp only [one_mul, Real.log_one] at h3
    rw [← h']
    exact h3
  have hmul : (1 / (m : ℝ)) * (∑ i, u i * Real.log (u i))
      = (∑ i, u i * Real.log (u i)) / (m : ℝ) := by field_simp
  rw [hmul] at h2
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  simpa using! (le_div_iff₀ hmpos).mp h2

/-- Pulls a constant left factor out of a sum over a finite set. -/
theorem finset_sum_const_mul {α : Type} (S : Finset α) (c : ℝ) (f : α → ℝ) :
    ∑ i ∈ S, c * f i = c * ∑ i ∈ S, f i := by
  rw [← Finset.mul_sum]

/-- Pulls a constant right factor out of a sum over a finite set. -/
theorem finset_sum_mul_const {α : Type} (S : Finset α) (f : α → ℝ) (c : ℝ) :
    ∑ i ∈ S, f i * c = (∑ i ∈ S, f i) * c := by
  rw [← Finset.sum_mul]

/-- Nonnegative weights on a nonempty finite set with total equal to its cardinality have
nonnegative sum of `u * log u`. -/
theorem sum_mul_log_nonneg_finset {α : Type} [Fintype α] (S : Finset α) (u : α → ℝ)
    (hu : ∀ i ∈ S, 0 ≤ u i) (husum : ∑ i ∈ S, u i = (S.card : ℝ)) (hcard : 0 < S.card) :
    ∑ i ∈ S, u i * Real.log (u i) ≥ 0 := by
  have hcardpos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hcard
  have hw0 : ∀ i ∈ S, 0 ≤ (1 / (S.card : ℝ)) := by
    intro i _; positivity
  have hw1 : ∑ i ∈ S, (1 / (S.card : ℝ)) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp
  have hmem : ∀ i ∈ S, u i ∈ Set.Ici (0 : ℝ) := by
    intro i hi; exact (Set.mem_Ici).2 (hu i hi)
  have h := Real.convexOn_mul_log.map_sum_le
    (t := S) (w := fun _ => 1 / (S.card : ℝ)) (p := u) hw0 hw1 hmem
  (try dsimp only at h)
  simp only [smul_eq_mul] at h
  have hleft : (∑ i ∈ S, (1 / (S.card : ℝ)) * u i) = 1 := by
    rw [finset_sum_const_mul, husum]
    field_simp
  have h' : (∑ i ∈ S, (1 / (S.card : ℝ)) * (u i * Real.log (u i)))
      = (1 / (S.card : ℝ)) * (∑ i ∈ S, u i * Real.log (u i)) := by
    rw [finset_sum_const_mul]
  have h2 : 0 ≤ (1 / (S.card : ℝ)) * (∑ i ∈ S, u i * Real.log (u i)) := by
    have h3 : (∑ i ∈ S, (1 / (S.card : ℝ)) * u i) * Real.log (∑ i ∈ S, (1 / (S.card : ℝ)) * u i)
        ≤ ∑ i ∈ S, (1 / (S.card : ℝ)) * (u i * Real.log (u i)) := h
    rw [hleft] at h3
    simp only [one_mul, Real.log_one] at h3
    rw [← h']
    exact h3
  have hmul : (1 / (S.card : ℝ)) * (∑ i ∈ S, u i * Real.log (u i))
      = (∑ i ∈ S, u i * Real.log (u i)) / (S.card : ℝ) := by field_simp
  rw [hmul] at h2
  simpa using! (le_div_iff₀ hcardpos).mp h2

/-- The entropy of nonnegative normalized weights on a nonempty finite type is at most the
base-two logarithm of its cardinality. -/
theorem entH_le_log_card {α : Type} [Fintype α] (w : α → ℝ) (hw : ∀ i, 0 ≤ w i)
    (ht : ∑ i, w i = 1) (hm : 0 < Fintype.card α) :
    entH w ≤ Real.log (Fintype.card α : ℝ) / Real.log 2 := by
  have hcard : 0 < (Finset.univ : Finset α).card := by simpa using! hm
  have hcardpos : (0 : ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast hm
  let u : α → ℝ := fun i => (Fintype.card α : ℝ) * w i
  have hu_nonneg : ∀ i, 0 ≤ u i := fun i => by
    simp only [u]; exact mul_nonneg hcardpos.le (hw i)
  have hu_sum : ∑ i, u i = (Fintype.card α : ℝ) := by
    simp only [u]; rw [sum_const_mul, ht]; ring
  have hjens : ∑ i, u i * Real.log (u i) ≥ 0 :=
    sum_mul_log_nonneg_finset (Finset.univ : Finset α) u
      (fun i _ => hu_nonneg i) hu_sum hcard
  have hkey : ∀ i, w i * Real.log (w i)
      = (u i * Real.log (u i)) / (Fintype.card α : ℝ) - w i * Real.log (Fintype.card α : ℝ) := by
    intro i
    by_cases hw0 : w i = 0
    · simp [u, hw0]
    · have hwpos : 0 < w i := lt_of_le_of_ne (hw i) (Ne.symm hw0)
      have hupos : 0 < u i := by simp only [u]; positivity
      have hcardne : (Fintype.card α : ℝ) ≠ 0 := hcardpos.ne'
      simp only [u]
      rw [Real.log_mul (by positivity) (by positivity)]
      field_simp
      ring
  have hA : (∑ i, w i * Real.log (w i))
      = (∑ i, u i * Real.log (u i)) / (Fintype.card α : ℝ)
        - (∑ i, w i) * Real.log (Fintype.card α : ℝ) := by
    rw [Finset.sum_congr rfl (fun i _ => hkey i), Finset.sum_sub_distrib]
    rw [Finset.sum_div, finset_sum_mul_const]
  have hsum : (∑ i, w i * Real.log (w i))
      = (∑ i, u i * Real.log (u i)) / (Fintype.card α : ℝ) - Real.log (Fintype.card α : ℝ) := by
    rw [hA, ht]
    ring
  have hbits : (∑ i, w i * (Real.log (w i) / Real.log 2))
      = (∑ i, w i * Real.log (w i)) / Real.log 2 := by
    have hc : ∀ i, w i * (Real.log (w i) / Real.log 2)
        = (w i * Real.log (w i)) / Real.log 2 := by
      intro i; field_simp
    rw [Finset.sum_congr rfl (fun i _ => hc i), Finset.sum_div]
  have hsum' : (∑ i, w i * Real.log (w i))
      = -Real.log (Fintype.card α : ℝ)
        + (∑ i, u i * Real.log (u i)) / (Fintype.card α : ℝ) := by
    rw [hsum]; ring
  unfold entH xlog2
  rw [hbits, hsum']
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog2ne : Real.log 2 ≠ 0 := hlog2.ne'
  have hX : 0 ≤ (∑ i, u i * Real.log (u i)) / (Fintype.card α : ℝ) :=
    div_nonneg hjens hcardpos.le
  rw [le_div_iff₀ hlog2]
  field_simp [hlog2ne]
  linarith

/-- Bounds the sum of `r * log₂ r` over a nonempty finite set below by its total mass times the
logarithm of its average mass. -/
theorem sum_xlog2_sub {α : Type} [Fintype α] (S : Finset α) (r : α → ℝ)
    (hr : ∀ i ∈ S, 0 ≤ r i) (hcard : 0 < S.card) (hq : 0 < ∑ i ∈ S, r i) :
    (∑ i ∈ S, r i * (Real.log (r i) / Real.log 2))
      ≥ (∑ i ∈ S, r i) * (Real.log ((∑ i ∈ S, r i) / (S.card : ℝ)) / Real.log 2) := by
  have hcardpos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hcard
  set q : ℝ := ∑ i ∈ S, r i with hq'
  have hq0 : 0 < q := hq
  let u : α → ℝ := fun i => if i ∈ S then (S.card : ℝ) * r i / q else 0
  have hu_nonneg : ∀ i ∈ S, 0 ≤ u i := by
    intro i hi
    simp only [u, if_pos hi]
    exact div_nonneg (mul_nonneg hcardpos.le (hr i hi)) hq0.le
  have hu_sum : ∑ i ∈ S, u i = (S.card : ℝ) := by
    have hc : ∀ i ∈ S, u i = (S.card : ℝ) * r i / q := by
      intro i hi; simp [u, hi]
    have hc2 : ∀ i ∈ S, (S.card : ℝ) * r i / q = (S.card : ℝ) * (r i / q) := by
      intro i _; field_simp
    rw [Finset.sum_congr rfl (fun i hi => hc i hi)]
    rw [Finset.sum_congr rfl (fun i hi => hc2 i hi), ← Finset.mul_sum, ← Finset.sum_div]
    field_simp
    exact hq'.symm
  have hjens : ∑ i ∈ S, u i * Real.log (u i) ≥ 0 :=
    sum_mul_log_nonneg_finset S u hu_nonneg hu_sum hcard
  have hkey : ∀ i ∈ S, r i * Real.log ((S.card : ℝ) * r i / q)
      = r i * (Real.log (S.card : ℝ) + Real.log (r i) - Real.log q) := by
    intro i hi
    by_cases hr0 : r i = 0
    · simp [hr0]
    · have hrpos : 0 < r i := lt_of_le_of_ne (hr i hi) (Ne.symm hr0)
      have hne : (S.card : ℝ) * r i ≠ 0 := mul_ne_zero hcardpos.ne' hr0
      rw [Real.log_div hne hq0.ne']
      rw [Real.log_mul hcardpos.ne' hrpos.ne']
  have hstep : ∀ i ∈ S, r i * Real.log ((S.card : ℝ) * r i / q)
      = (r i * Real.log (S.card : ℝ)) + (r i * Real.log (r i)) - (r i * Real.log q) := by
    intro i hi
    rw [hkey i hi]
    ring
  have hexpand : (∑ i ∈ S, r i * Real.log ((S.card : ℝ) * r i / q))
      = (Real.log (S.card : ℝ)) * q + (∑ i ∈ S, r i * Real.log (r i))
        - (Real.log q) * q := by
    rw [Finset.sum_congr rfl (fun i hi => hstep i hi)]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [finset_sum_mul_const, finset_sum_mul_const]
    simp only [hq']
    ring
  have hrel : (∑ i ∈ S, u i * Real.log (u i))
      = ((S.card : ℝ) / q) * (∑ i ∈ S, r i * Real.log ((S.card : ℝ) * r i / q)) := by
    have hc3 : ∀ i ∈ S, u i * Real.log (u i)
        = (S.card : ℝ) / q * (r i * Real.log ((S.card : ℝ) * r i / q)) := by
      intro i hi
      simp [u, hi]
      ring
    rw [Finset.sum_congr rfl (fun i hi => hc3 i hi)]
    rw [← Finset.mul_sum]
  have hnonneg : 0 ≤ (∑ i ∈ S, r i * Real.log ((S.card : ℝ) * r i / q)) := by
    have h2 := hjens
    rw [hrel] at h2
    have hpos : 0 < (S.card : ℝ) / q := div_pos hcardpos hq0
    exact (mul_nonneg_iff_of_pos_left hpos).mp h2
  have hmain' : (∑ i ∈ S, r i * Real.log (r i)) - (Real.log q) * q
      + (Real.log (S.card : ℝ)) * q ≥ 0 := by
    have hexp := hexpand
    have hW : 0 ≤ (Real.log (S.card : ℝ)) * q + (∑ i ∈ S, r i * Real.log (r i))
        - (Real.log q) * q := by
      rw [← hexp]
      exact hnonneg
    linarith
  have hmain : (∑ i ∈ S, r i * Real.log (r i)) ≥ q * (Real.log q - Real.log (S.card : ℝ)) := by
    have hshift : q * (Real.log q - Real.log (S.card : ℝ))
        = (Real.log q) * q - (Real.log (S.card : ℝ)) * q := by ring
    rw [hshift]
    linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlogdiv : Real.log (q / (S.card : ℝ)) = Real.log q - Real.log (S.card : ℝ) :=
    Real.log_div hq0.ne' hcardpos.ne'
  have hmul : q * (Real.log (q / (S.card : ℝ)) / Real.log 2)
      = q * (Real.log q - Real.log (S.card : ℝ)) / Real.log 2 := by
    rw [hlogdiv]; ring
  have hmul2 : q * (Real.log q - Real.log (S.card : ℝ)) / Real.log 2
      = q * ((Real.log q - Real.log (S.card : ℝ)) / Real.log 2) := by ring
  have hc : ∀ i ∈ S, r i * (Real.log (r i) / Real.log 2)
      = (r i * Real.log (r i)) / Real.log 2 := by
    intro i _; field_simp
  rw [Finset.sum_congr rfl (fun i hi => hc i hi), ← Finset.sum_div, hmul]
  exact div_le_div_of_nonneg_right hmain hlog2.le

/-- For nonnegative joint weights, multiplying a conditional weight by its left marginal
recovers the joint weight. -/
theorem condW_mul_margL {α β : Type} [Fintype α] [Fintype β] (d : α × β → ℝ)
    (hd : ∀ i j, 0 ≤ d (i, j)) (i : α) (j : β) :
    margL d i * condW d i j = d (i, j) := by
  by_cases hm : margL d i = 0
  · have hle : d (i, j) ≤ margL d i := by
      unfold margL
      exact Finset.single_le_sum (f := fun j => d (i, j)) (fun j _ => hd i j)
        (Finset.mem_univ j)
    have hdnonneg : 0 ≤ d (i, j) := hd i j
    have hd0 : d (i, j) = 0 := by linarith
    simp [condW, hm, hd0]
  · simp only [condW, dif_neg hm]
    field_simp

/-- Bounds the entropy of a distribution on at least two cells by the binary entropy of the
error relative to a chosen guess plus the error times `log₂ (n - 1)`. -/
theorem fano_pointwise {n : ℕ} (hn : 2 ≤ n) (P : Fin n → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hsum : ∑ x, P x = 1) (gy : Fin n) :
    -(∑ x, P x * (Real.log (P x) / Real.log 2))
      ≤ binEntropy (1 - P gy) + (1 - P gy) * (Real.log ((n - 1 : ℕ) : ℝ) / Real.log 2) := by
  set S : Finset (Fin n) := (Finset.univ : Finset (Fin n)).erase gy with hS
  have hScard : S.card = n - 1 := by
    have h1 : ((Finset.univ : Finset (Fin n)).erase gy).card
        = (Finset.univ : Finset (Fin n)).card - 1 :=
      Finset.card_erase_of_mem (Finset.mem_univ gy)
    have h2 : (Finset.univ : Finset (Fin n)).card = n := by
      rw [Finset.card_univ, Fintype.card_fin]
    simp only [S]
    omega
  have hScardpos : 0 < S.card := by
    have h1 : 1 ≤ n := by omega
    omega
  have hq : ∑ x ∈ S, P x = 1 - P gy := by
    have h := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
      (fun x => P x) (Finset.mem_univ gy)
    (try simp only [S] at h)
    have h3 : (∑ x ∈ (Finset.univ : Finset (Fin n)), P x) = (∑ x, P x) := rfl
    rw [h3] at h
    rw [hsum] at h
    linarith
  have hsplit : (∑ x, P x * (Real.log (P x) / Real.log 2))
      = P gy * (Real.log (P gy) / Real.log 2)
        + ∑ x ∈ S, P x * (Real.log (P x) / Real.log 2) := by
    have h := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
      (fun x => P x * (Real.log (P x) / Real.log 2)) (Finset.mem_univ gy)
    (try simp only [S] at h)
    have h2 : (∑ x ∈ (Finset.univ : Finset (Fin n)), P x * (Real.log (P x) / Real.log 2))
        = (∑ x, P x * (Real.log (P x) / Real.log 2)) := rfl
    rw [h2] at h
    linarith
  have hPgy_le : P gy ≤ 1 := by
    have hle : P gy ≤ ∑ x, P x := by
      exact Finset.single_le_sum (f := P) (fun x _ => hP x) (Finset.mem_univ gy)
    rw [hsum] at hle
    exact hle
  have hcardne : ((n - 1 : ℕ) : ℝ) ≠ 0 := by
    have h1 : 1 ≤ n := by omega
    have h2 : (0 : ℕ) < n - 1 := by omega
    exact_mod_cast (Nat.ne_of_gt h2)
  by_cases hg : P gy = 1
  · have hzero : ∀ x ∈ S, P x = 0 := by
      intro x hx
      have hx0 : 0 ≤ P x := hP x
      have hle : P x ≤ ∑ y ∈ S, P y := by
        unfold S
        exact Finset.single_le_sum (f := P) (fun y _ => hP y) hx
      rw [hq] at hle
      rw [hg] at hle
      linarith
    have hsumS : (∑ x ∈ S, P x * (Real.log (P x) / Real.log 2)) = 0 := by
      have hc : ∀ x ∈ S, P x * (Real.log (P x) / Real.log 2) = 0 := by
        intro x hx
        rw [hzero x hx]
        simp [Real.log_zero]
      rw [Finset.sum_congr rfl (fun x hx => hc x hx)]
      simp
    rw [hsplit, hsumS, hg]
    simp [binEntropy]
  · have hPgy_lt : P gy < 1 := lt_of_le_of_ne hPgy_le hg
    have hqpos : 0 < ∑ x ∈ S, P x := by
      rw [hq]
      linarith
    have hsub := sum_xlog2_sub S P (fun x hx => hP x) hScardpos hqpos
    have hqne : 1 - P gy ≠ 0 := by
      rw [← hq]
      exact hqpos.ne'
    have hlogdiv : Real.log ((∑ x ∈ S, P x) / (S.card : ℝ))
        = Real.log (1 - P gy) - Real.log ((n - 1 : ℕ) : ℝ) := by
      rw [hq, hScard]
      exact Real.log_div hqne hcardne
    have hbound : (∑ x ∈ S, P x * (Real.log (P x) / Real.log 2))
        ≥ (1 - P gy) * ((Real.log (1 - P gy) - Real.log ((n - 1 : ℕ) : ℝ)) / Real.log 2) := by
      have h := hsub
      rw [hlogdiv] at h
      rw [hq] at h
      exact h
    have hid : binEntropy (1 - P gy) + (1 - P gy) * (Real.log ((n - 1 : ℕ) : ℝ) / Real.log 2)
        = -P gy * (Real.log (P gy) / Real.log 2)
          - (1 - P gy) * ((Real.log (1 - P gy) - Real.log ((n - 1 : ℕ) : ℝ)) / Real.log 2) := by
      unfold binEntropy
      have h1mq : 1 - (1 - P gy) = P gy := by ring
      rw [h1mq]
      ring
    rw [hsplit]
    have h1 : -(P gy * (Real.log (P gy) / Real.log 2)
        + ∑ x ∈ S, P x * (Real.log (P x) / Real.log 2))
        ≤ -P gy * (Real.log (P gy) / Real.log 2)
          - (1 - P gy) * ((Real.log (1 - P gy) - Real.log ((n - 1 : ℕ) : ℝ)) / Real.log 2) := by
      linarith [hbound]
    rw [hid]
    exact h1

/-- Distributes a finite-type sum over pointwise subtraction. -/
theorem fintype_sum_sub {ι : Type} [Fintype ι] (f g : ι → ℝ) :
    (∑ x, (f x - g x)) = (∑ x, f x) - ∑ x, g x := by
  rw [Finset.sum_sub_distrib]

/-- Conditional weights formed from nonnegative joint weights are nonnegative. -/
theorem condW_nonneg {α β : Type} [Fintype α] [Fintype β] (d : α × β → ℝ)
    (hd : ∀ i j, 0 ≤ d (i, j)) (i : α) (j : β) : 0 ≤ condW d i j := by
  by_cases hm : margL d i = 0
  · simp [condW, hm]
  · simp only [condW, dif_neg hm]
    exact div_nonneg (hd i j) (Finset.sum_nonneg fun k _ => hd i k)

/-- Bounds conditional entropy by `binEntropy ε + ε * log₂ (n - 1)` for a decoder with error `ε
≤ 1 / 2` under normalized nonnegative joint weights. -/
theorem fano_cond_ent {n : ℕ} {β : Type} [Fintype β] (hn : 2 ≤ n)
    (d : β × Fin n → ℝ) (hd : ∀ y x, 0 ≤ d (y, x))
    (ht : ∑ y, ∑ x, d (y, x) = 1)
    (g : β → Fin n) (ε : ℝ)
    (hε : ε = ∑ y, ∑ x, d (y, x) * (if g y = x then 0 else 1))
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) :
    condEntH d ≤ binEntropy ε + ε * (Real.log ((n - 1 : ℕ) : ℝ) / Real.log 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hL : 0 ≤ Real.log ((n - 1 : ℕ) : ℝ) / Real.log 2 := by
    have h1 : (1 : ℕ) ≤ n - 1 := by omega
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast h1)) hlog2.le
  have hpw_nonneg : ∀ y, 0 ≤ margL d y := by
    intro y; exact Finset.sum_nonneg fun x _ => hd y x
  have hpw_sum : ∑ y, margL d y = 1 := by
    have h : (∑ y, margL d y) = ∑ y, ∑ x, d (y, x) := rfl
    rw [h, ht]
  set hy : β → ℝ := fun y => -∑ x, condW d y x * (Real.log (condW d y x) / Real.log 2)
    with hhy
  set qy : β → ℝ := fun y => 1 - condW d y (g y) with hqy
  have hper : ∀ y, hy y ≤ binEntropy (qy y) + qy y * (Real.log ((n - 1 : ℕ) : ℝ) / Real.log 2) := by
    intro y
    by_cases hpw : margL d y = 0
    · have hzero : ∀ x, condW d y x = 0 := by
        intro x; simp [condW, hpw]
      have hhy0 : hy y = 0 := by
        simp only [hhy]
        have hc : ∀ x, condW d y x * (Real.log (condW d y x) / Real.log 2) = 0 := by
          intro x
          rw [hzero x]
          simp [Real.log_zero]
        rw [Finset.sum_congr rfl (fun x _ => hc x)]
        simp
      have hqy0 : qy y = 1 := by
        simp only [hqy]
        rw [hzero (g y)]
        simp
      rw [hhy0, hqy0]
      simp [binEntropy]
      linarith
    · have hsum1 : ∑ x, condW d y x = 1 := condW_sum d hd y hpw
      have hnonneg : ∀ x, 0 ≤ condW d y x := fun x => condW_nonneg d hd y x
      have hfw := fano_pointwise hn (condW d y) hnonneg hsum1 (g y)
      simp only [hhy, hqy] at hfw ⊢
      exact hfw

  have hcellpos : ∀ y, margL d y * (∑ x, condW d y x * (Real.log (condW d y x) / Real.log 2))
      = ∑ x, d (y, x) * (Real.log (condW d y x) / Real.log 2) := by
    intro y
    have h1 : margL d y * (∑ x, condW d y x * (Real.log (condW d y x) / Real.log 2))
        = ∑ x, (condW d y x * (Real.log (condW d y x) / Real.log 2)) * margL d y := by
      rw [mul_comm, Finset.sum_mul]
    rw [h1]
    have h2 : ∀ x, (condW d y x * (Real.log (condW d y x) / Real.log 2)) * margL d y
        = d (y, x) * (Real.log (condW d y x) / Real.log 2) := by
      intro x
      have hm := condW_mul_margL d hd y x
      rw [← hm]
      ring
    rw [Finset.sum_congr rfl (fun x _ => h2 x)]
  have hcell : ∀ y, margL d y * hy y
      = -∑ x, d (y, x) * (Real.log (condW d y x) / Real.log 2) := by
    intro y
    simp only [hhy]
    rw [mul_neg, hcellpos]
  have hdecomp : condEntH d = ∑ y, margL d y * hy y := by
    unfold condEntH
    have hR : (∑ y, margL d y * hy y)
        = -∑ y, ∑ x, d (y, x) * (Real.log (condW d y x) / Real.log 2) := by
      rw [Finset.sum_congr rfl (fun y _ => hcell y)]
      rw [Finset.sum_neg_distrib]
    rw [hR]

  have hqsum : (∑ y, margL d y * qy y) = ε := by
    have hcell' : ∀ y, margL d y * qy y = margL d y - d (y, g y) := by
      intro y
      simp only [hqy]
      have hm := condW_mul_margL d hd y (g y)
      calc
        margL d y * (1 - condW d y (g y)) = margL d y - margL d y * condW d y (g y) := by ring
        _ = margL d y - d (y, g y) := by rw [hm]
    rw [Finset.sum_congr rfl (fun y _ => hcell' y)]
    rw [Finset.sum_sub_distrib]
    have h1 : (∑ y, margL d y) = ∑ y, ∑ x, d (y, x) := rfl
    have h2 : (∑ y, ∑ x, d (y, x) * (if g y = x then 0 else 1))
        = (∑ y, ∑ x, d (y, x)) - ∑ y, d (y, g y) := by
      have hyy : ∀ y, ∑ x, d (y, x) * (if g y = x then 0 else 1)
          = (∑ x, d (y, x)) - d (y, g y) := by
        intro y
        have hcell'' : ∀ x, d (y, x) * (if g y = x then 0 else 1)
            = d (y, x) - (if g y = x then d (y, x) else 0) := by
          intro x
          by_cases hgx : g y = x
          · simp [hgx]
          · simp [hgx]
        rw [Finset.sum_congr rfl (fun x _ => hcell'' x)]
        rw [fintype_sum_sub (fun x => d (y, x)) (fun x => if g y = x then d (y, x) else 0)]
        have h3 : (∑ x, (if g y = x then d (y, x) else 0)) = d (y, g y) := by
          have h4 : ∀ x, (if g y = x then d (y, x) else 0)
              = if x = g y then d (y, g y) else 0 := by
            intro x
            by_cases h : g y = x
            · subst h; simp
            · simp [h, Ne.symm h]
          rw [Finset.sum_congr rfl (fun x _ => h4 x)]
          simp
        rw [h3]
      rw [Finset.sum_congr rfl (fun y _ => hyy y)]
      rw [Finset.sum_sub_distrib]
    rw [hε, h2, h1]

  have hqy_range : ∀ y, 0 ≤ qy y ∧ qy y ≤ 1 := by
    intro y
    by_cases hpw : margL d y = 0
    · refine ⟨?_, ?_⟩
      · simp only [hqy]
        rw [condW, dif_pos hpw]
        simp
      · simp only [hqy]
        rw [condW, dif_pos hpw]
        simp
    · have hsum1 : ∑ x, condW d y x = 1 := condW_sum d hd y hpw
      have hnonneg : ∀ x, 0 ≤ condW d y x := fun x => condW_nonneg d hd y x
      have hle : condW d y (g y) ≤ 1 := by
        have h0 := Finset.single_le_sum (f := condW d y) (fun x _ => hnonneg x)
          (Finset.mem_univ (g y))
        rw [hsum1] at h0
        exact h0
      have hgy0 : 0 ≤ condW d y (g y) := hnonneg (g y)
      refine ⟨?_, ?_⟩
      · simp only [hqy]
        linarith
      · simp only [hqy]
        linarith
  have hjensen : (∑ y, margL d y * binEntropy (qy y)) ≤ binEntropy ε := by
    have hconc : (∑ y, margL d y * Real.binEntropy (qy y)) ≤ Real.binEntropy ε := by
      have h := Real.strictConcave_binEntropy.concaveOn.le_map_sum
        (t := (Finset.univ : Finset β))
        (w := fun y => margL d y) (p := qy)
        (fun y _ => hpw_nonneg y) (by exact hpw_sum)
        (fun y _ => hqy_range y)
      (try dsimp only at h)
      simp only [smul_eq_mul] at h
      rw [hqsum] at h
      exact h
    have hbits : (∑ y, margL d y * binEntropy (qy y))
        = (∑ y, margL d y * Real.binEntropy (qy y)) / Real.log 2 := by
      rw [Finset.sum_div]
      have hc : ∀ y, margL d y * binEntropy (qy y)
          = (margL d y * Real.binEntropy (qy y)) / Real.log 2 := by
        intro y
        rw [clause17_binEntropy_eq_mathlib]
        field_simp
      rw [Finset.sum_congr rfl (fun y _ => hc y)]
    rw [hbits]
    have h2 := hconc
    rw [clause17_binEntropy_eq_mathlib]
    rw [div_le_div_iff_of_pos_right hlog2]
    exact h2

  rw [hdecomp]
  have hstep1 : (∑ y, margL d y * hy y)
      ≤ ∑ y, (margL d y * binEntropy (qy y)
        + margL d y * qy y * (Real.log ((n - 1 : ℕ) : ℝ) / Real.log 2)) := by
    have h1 : ∀ y, margL d y * hy y
        ≤ margL d y * binEntropy (qy y)
          + margL d y * qy y * (Real.log ((n - 1 : ℕ) : ℝ) / Real.log 2) := by
      intro y
      have h := hper y
      calc
        margL d y * hy y ≤ margL d y * (binEntropy (qy y)
            + qy y * (Real.log ((n - 1 : ℕ) : ℝ) / Real.log 2)) :=
          mul_le_mul_of_nonneg_left h (hpw_nonneg y)
        _ = margL d y * binEntropy (qy y)
            + margL d y * qy y * (Real.log ((n - 1 : ℕ) : ℝ) / Real.log 2) := by ring
    exact Finset.sum_le_sum fun y _ => h1 y
  calc
    (∑ y, margL d y * hy y)
        ≤ ∑ y, (margL d y * binEntropy (qy y)
          + margL d y * qy y * (Real.log ((n - 1 : ℕ) : ℝ) / Real.log 2)) := hstep1
    _ = (∑ y, margL d y * binEntropy (qy y))
        + (∑ y, margL d y * qy y) * (Real.log ((n - 1 : ℕ) : ℝ) / Real.log 2) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    _ ≤ binEntropy ε + ε * (Real.log ((n - 1 : ℕ) : ℝ) / Real.log 2) := by
          rw [hqsum]
          exact add_le_add hjensen (le_refl _)

/-- For a uniform hidden cell and decoding error at most one half, `log₂ n` is bounded by mutual
information plus the Fano error terms. -/
theorem fano_capacity_arith {n : ℕ} {β : Type} [Fintype β] (hn : 2 ≤ n)
    (d : Fin n × β → ℝ) (hd : ∀ x y, 0 ≤ d (x, y))
    (ht : ∑ x, ∑ y, d (x, y) = 1)
    (hmarg : ∀ x, ∑ y, d (x, y) = 1 / (n : ℝ))
    (g : β → Fin n) (ε : ℝ)
    (hε : ε = ∑ y, ∑ x, d (x, y) * (if g y = x then 0 else 1))
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) :
    Real.log (n : ℝ) / Real.log 2
      ≤ binEntropy ε + ε * (Real.log ((n - 1 : ℕ) : ℝ) / Real.log 2) + mutInfo d := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)

  have hent : entH (margL d) = Real.log (n : ℝ) / Real.log 2 := by
    unfold entH
    have hsum : (∑ i, xlog2 (margL d i)) = -(Real.log (n : ℝ) / Real.log 2) := by
      have hc : ∀ x, margL d x = 1 / (n : ℝ) := by
        intro x
        unfold margL
        rw [hmarg x]
      have hc' : ∀ x, xlog2 (margL d x) = xlog2 (1 / (n : ℝ)) := by
        intro x
        rw [hc x]
      rw [Finset.sum_congr rfl (fun x _ => hc' x)]
      have h1 : (∑ x : Fin n, xlog2 (1 / (n : ℝ)))
          = (1 / (n : ℝ)) * (∑ x : Fin n, (Real.log (1 / (n : ℝ)) / Real.log 2)) := by
        unfold xlog2
        rw [sum_const_mul]
      have h2 : (∑ x : Fin n, (Real.log (1 / (n : ℝ)) / Real.log 2))
          = (n : ℝ) * (Real.log (1 / (n : ℝ)) / Real.log 2) := by
        simp
      rw [h1, h2]
      have hlog : Real.log (1 / (n : ℝ)) = -Real.log (n : ℝ) := by
        rw [one_div, Real.log_inv]
      have h3 : (1 / (n : ℝ)) * ((n : ℝ) * (Real.log (1 / (n : ℝ)) / Real.log 2))
          = Real.log (1 / (n : ℝ)) / Real.log 2 := by
        field_simp
      rw [h3, hlog]
      ring
    rw [hsum]
    ring

  have hε' : ε = ∑ y, ∑ x, (fun p => d (p.2, p.1)) (y, x) * (if g y = x then 0 else 1) := by
    have hc : ∀ y x, (fun p => d (p.2, p.1)) (y, x) = d (x, y) := by
      intro y x
      simp
    rw [Finset.sum_congr rfl
      (fun y _ => Finset.sum_congr rfl (fun x _ => by rw [hc y x]))]
    exact hε
  have hfano : condEntHR d
      ≤ binEntropy ε + ε * (Real.log ((n - 1 : ℕ) : ℝ) / Real.log 2) := by
    have h := fano_cond_ent (β := β) (n := n) hn (fun p => d (p.2, p.1))
      (fun y x => hd x y)
      (by
        have hh : (∑ y, ∑ x, (fun p => d (p.2, p.1)) (y, x)) = ∑ x, ∑ y, d (x, y) := by
          rw [Finset.sum_comm]
        rw [hh]
        exact ht)
      g ε hε' hε0 hε1
    exact h

  have hsplit : entH (margL d) = condEntHR d + mutInfo d := by
    unfold mutInfo
    ring
  rw [hsplit] at hent
  linarith

/-- The answer prefix at an index equals the corresponding transcript restriction. -/
theorem answerPrefix_eq_tRestrict {k : ℕ} (y : Fin k → Bool) (i : Fin k) :
    answerPrefix y i = tRestrict y i := by
  funext l
  simp only [answerPrefix, tRestrict]
  apply congrArg y
  apply Fin.ext
  rfl

/-- Evaluating an extended transcript depends only on the value of its finite index. -/
theorem tExt_val {m : ℕ} {α : Type} (pfx : Fin m → α) (b : α) (i : Fin (m + 1)) :
    tExt pfx b i = tExt pfx b ⟨i.val, by omega⟩ := by
  have hi : i = ⟨i.val, by omega⟩ := by
    apply Fin.ext
    rfl
  rw [hi]

/-- Extending a transcript preserves its entries at all original indices. -/
theorem tExt_castSucc {m : ℕ} {α : Type} (pfx : Fin m → α) (b : α) (j : Fin m) :
    tExt pfx b (j.castSucc) = pfx j := by
  have hcast : j.castSucc = ⟨j.val, by omega⟩ := by
    apply Fin.ext
    rfl
  rw [hcast]
  have hne : (⟨j.val, by omega⟩ : Fin m).val ≠ m := by
    simpa using! Nat.ne_of_lt j.isLt
  simp [tExt, hne]

/-- Taking the prefix of an extended transcript returns the original transcript. -/
theorem tPre_tExt {m : ℕ} {α : Type} (pfx : Fin m → α) (b : α) :
    tPre (tExt pfx b) = pfx := by
  funext j
  simp only [tPre]
  exact tExt_castSucc pfx b j

/-- The last entry of an extended transcript is the appended value. -/
theorem tLast_tExt {m : ℕ} {α : Type} (pfx : Fin m → α) (b : α) :
    tLast (tExt pfx b) = b := by
  simp [tLast, tExt]

/-- A transcript is recovered by appending its last entry to its prefix. -/
theorem tExt_tPre {m : ℕ} {α : Type} (y : Fin (m + 1) → α) :
    tExt (tPre y) (tLast y) = y := by
  funext i
  by_cases hi : i.val = m
  · have hlast : i = Fin.last m := by
      apply Fin.ext
      simpa [Fin.last] using! hi
    simp [tExt, tLast, hlast]
  · simp only [tExt, hi]
    have hcast : (⟨i.val, by omega⟩ : Fin m).castSucc = i := by
      apply Fin.ext
      simp
    simp [tPre, hcast]

/-- Restricting an extended transcript before an original index agrees with restricting the
original transcript. -/
theorem tRestrict_tExt_castSucc {m : ℕ} {α : Type} (pfx : Fin m → α) (b : α) (j : Fin m) :
    tRestrict (tExt pfx b) (j.castSucc) = tRestrict pfx j := by
  funext l
  have hjval : (j.castSucc).val = j.val := rfl
  have hl : l.val < m := by omega
  simp only [tRestrict]
  have hne : (⟨l.val, by omega⟩ : Fin m).val ≠ m := by
    simpa using! Nat.ne_of_lt hl
  simp [tExt, hne]

/-- Restricting an extended transcript before its last index returns the original transcript. -/
theorem tRestrict_tExt_last {m : ℕ} {α : Type} (pfx : Fin m → α) (b : α) :
    tRestrict (tExt pfx b) (Fin.last m) = pfx := by
  funext l
  have hl : l.val < m := by
    have h1 := l.isLt
    simp only [Fin.last] at h1
    omega
  simp only [tRestrict]
  have hne : (⟨l.val, by omega⟩ : Fin m).val ≠ m := by
    simpa using! Nat.ne_of_lt hl
  simp [tExt, hne]

/-- Splits a sum over extended transcripts and their last entries into a sum over prefixes and
appended values. -/
theorem Fintype.sum_tSplit {m : ℕ} {α : Type} [Fintype α] {M : Type} [AddCommMonoid M]
    (F : (Fin (m + 1) → α) → α → M) :
    (∑ y : Fin (m + 1) → α, F y (y (Fin.last m)))
      = ∑ pfx : Fin m → α, ∑ b, F (tExt pfx b) b := by
  have h := Fintype.sum_equiv (tSplitEquiv (m := m)).symm (fun y => F y (y (Fin.last m)))
    (fun p : (Fin m → α) × α => F (tExt p.1 p.2) p.2) (by
      intro y
      have hinv : (tSplitEquiv (m := m)).symm y = (tPre y, tLast y) := rfl
      rw [hinv]
      show F y (y (Fin.last m)) = F (tExt (tPre y) (tLast y)) (tLast y)
      rw [tExt_tPre y]
      rfl)
  rw [Fintype.sum_prod_type] at h
  exact h

/-- Entropy is preserved when a transcript is reindexed as its prefix and last entry alongside
the hidden cell. -/
theorem entH_eq_entH_post {n m : ℕ} {α : Type} [Fintype α]
    (d : Fin n × (Fin (m + 1) → α) → ℝ) :
    entH d = entH (fun p : (Fin n × (Fin m → α)) × α =>
      d (p.1.1, tExt p.1.2 p.2)) := by
  have h := Fintype.sum_equiv (tSplitLawEquiv (n := n) (m := m))
    (fun z => xlog2 (d z))
    (fun z : (Fin n × (Fin m → α)) × α =>
      xlog2 (d (z.1.1, tExt z.1.2 z.2))) (by
      intro z
      obtain ⟨x, y⟩ := z
      have hinv : (tSplitLawEquiv (n := n) (m := m)) (x, y) = ((x, tPre y), tLast y) := rfl
      rw [hinv]
      show xlog2 (d (x, y)) = xlog2 (d (x, tExt (tPre y) (tLast y)))
      rw [tExt_tPre y])
  rw [Fintype.sum_prod_type] at h
  unfold entH
  rw [Fintype.sum_prod_type]
  simpa using! (congrArg Neg.neg h)

/-- Factors an extended binary transcript likelihood into its prefix likelihood and final
conditional answer weight. -/
theorem bscLikPre_split {n m : ℕ} (cuts : ∀ i : Fin (m + 1), (Fin i.val → Bool) → Fin n)
    (p : ℝ) (x : Fin n) (pfx : Fin m → Bool) (b : Bool) :
    bscLikPre cuts p x (tExt pfx b)
      = bscLikPre (fun j => cuts (j.castSucc)) p x pfx
        * bscStepCond cuts p x pfx b := by
  unfold bscLikPre bscStepCond
  rw [Fin.prod_univ_castSucc]
  have hpre : ∀ j : Fin m,
      bscProb p (truthBit x (cuts (j.castSucc) (tRestrict (tExt pfx b) (j.castSucc))))
          ((tExt pfx b) (j.castSucc))
        = bscProb p (truthBit x (cuts (j.castSucc) (tRestrict pfx j))) (pfx j) := by
    intro j
    have h1 : tRestrict (tExt pfx b) (j.castSucc) = tRestrict pfx j :=
      tRestrict_tExt_castSucc pfx b j
    have h2 : (tExt pfx b) (j.castSucc) = pfx j := tExt_castSucc pfx b j
    rw [h1, h2]
  rw [Finset.prod_congr rfl (fun j _ => hpre j)]
  have hlast : bscProb p (truthBit x (cuts (Fin.last m) (tRestrict (tExt pfx b) (Fin.last m))))
      ((tExt pfx b) (Fin.last m))
      = bscProb p (truthBit x (cuts (Fin.last m) pfx)) b := by
    have h1 : tRestrict (tExt pfx b) (Fin.last m) = pfx := tRestrict_tExt_last pfx b
    have h2 : (tExt pfx b) (Fin.last m) = b := tLast_tExt pfx b
    rw [h1, h2]
  rw [hlast]

/-- The false and true binary symmetric channel weights sum to one. -/
theorem bscProb_sum_one {p : ℝ} (t : Bool) : bscProb p t false + bscProb p t true = 1 := by
  cases t <;> simp [bscProb]

/-- The binary symmetric channel weights sum to one over Boolean answers. -/
theorem bscProb_sum {p : ℝ} (t : Bool) : (∑ b, bscProb p t b) = 1 := by
  rw [Fintype.sum_bool, add_comm]
  exact bscProb_sum_one (p := p) t

/-- For each hidden cell, the adaptive binary transcript likelihoods sum to one. -/
theorem bscLikPre_sum_one {n m : ℕ} (cuts : ∀ i : Fin m, (Fin i.val → Bool) → Fin n)
    (p : ℝ) (x : Fin n) :
    (∑ pfx : Fin m → Bool, bscLikPre cuts p x pfx) = 1 := by
  induction m with
  | zero =>
      simp [bscLikPre]
  | succ m ih =>
      have hsplit : (∑ pfx : Fin (m + 1) → Bool, bscLikPre cuts p x pfx)
          = ∑ pfx : Fin m → Bool, ∑ b, bscLikPre cuts p x (tExt pfx b) := by
        have h := Fintype.sum_tSplit (fun y _ => bscLikPre cuts p x y)
        simpa using! h
      rw [hsplit]
      have hstep : ∀ (pfx : Fin m → Bool) (b : Bool),
          bscLikPre cuts p x (tExt pfx b)
            = bscLikPre (fun j => cuts (j.castSucc)) p x pfx
              * bscProb p (truthBit x (cuts (Fin.last m) pfx)) b := by
        intro pfx b
        simpa [bscStepCond] using! (bscLikPre_split cuts p x pfx b)
      rw [Finset.sum_congr rfl (fun pfx _ => Finset.sum_congr rfl (fun b _ => hstep pfx b))]
      have hsum : ∀ (pfx : Fin m → Bool),
          (∑ b, bscLikPre (fun j => cuts (j.castSucc)) p x pfx
            * bscProb p (truthBit x (cuts (Fin.last m) pfx)) b)
          = bscLikPre (fun j => cuts (j.castSucc)) p x pfx := by
        intro pfx
        have h1 : (∑ b, bscProb p (truthBit x (cuts (Fin.last m) pfx)) b) = 1 :=
          bscProb_sum (truthBit x (cuts (Fin.last m) pfx))
        have h2 := Finset.sum_mul (Finset.univ : Finset Bool)
          (fun b : Bool => bscProb p (truthBit x (cuts (Fin.last m) pfx)) b)
          (bscLikPre (fun j => cuts (j.castSucc)) p x pfx)
        rw [Finset.sum_congr rfl (fun b _ => mul_comm _ _)]
        rw [← h2, h1]
        simp
      rw [Finset.sum_congr rfl (fun pfx _ => hsum pfx)]
      exact ih (fun j => cuts (j.castSucc))

/-- Splits a sum over transcripts of length `m + 1` into a sum over prefixes of length `m` and
final values. -/
theorem Fintype.sum_tSplit_gen {m : ℕ} {α : Type} [Fintype α] {M : Type} [AddCommMonoid M]
    (G : (Fin (m + 1) → α) → M) :
    (∑ y : Fin (m + 1) → α, G y) = ∑ pfx : Fin m → α, ∑ b, G (tExt pfx b) := by
  have h := Fintype.sum_equiv (tSplitEquiv (m := m)).symm G
    (fun p : (Fin m → α) × α => G (tExt p.1 p.2)) (by
      intro y
      have hinv : (tSplitEquiv (m := m)).symm y = (tPre y, tLast y) := rfl
      rw [hinv]
      show G y = G (tExt (tPre y) (tLast y))
      rw [tExt_tPre y])
  rw [Fintype.sum_prod_type] at h
  exact h

/-- For nonnegative joint weights, mutual information equals right-marginal entropy minus
conditional entropy. -/
theorem mutInfo_eq_margR {α β : Type} [Fintype α] [Fintype β] (d : α × β → ℝ)
    (hd : ∀ i j, 0 ≤ d (i, j)) :
    mutInfo d = entH (margR d) - condEntH d := by
  have h1 : entH (margL d) + condEntH d = entH d := (entH_chain_rule d hd).symm
  have hswap' : (∑ z : β × α, xlog2 ((fun p : β × α => d (p.2, p.1)) z))
      = ∑ z : α × β, xlog2 (d z) := by
    have hcc : (∑ b : β, ∑ a : α, xlog2 (d (a, b)))
        = ∑ a : α, ∑ b : β, xlog2 (d (a, b)) := by
      have h := Fintype.sum_equiv (Equiv.prodComm α β) (fun z : α × β => xlog2 (d z))
        (fun z : β × α => xlog2 (d (z.2, z.1))) (fun z => rfl)
      simp only [Fintype.sum_prod_type] at h
      exact h.symm
    simp only [Fintype.sum_prod_type]
    exact hcc
  have hswap : entH (fun p : β × α => d (p.2, p.1)) = entH d := by
    unfold entH
    exact congrArg Neg.neg hswap'
  have hml : margL (fun p : β × α => d (p.2, p.1)) = margR d := by
    funext j
    rfl
  have h2 : entH (margR d) + condEntHR d = entH d := by
    have hh := entH_chain_rule (fun p : β × α => d (p.2, p.1)) (fun i j => hd j i)
    rw [hswap, hml] at hh
    have hc : condEntH (fun p : β × α => d (p.2, p.1)) = condEntHR d := rfl
    rw [hc] at hh
    exact hh.symm
  unfold mutInfo
  linarith

/-- Decomposes transcript mutual information into prefix mutual information and the difference
of two final-answer conditional entropies. -/
theorem mutInfo_split {n m : ℕ} {α : Type} [Fintype α]
    (d : Fin n × (Fin (m + 1) → α) → ℝ)
    (dPre : Fin n × (Fin m → α) → ℝ)
    (dM : (Fin m → α) × α → ℝ)
    (dPost : (Fin n × (Fin m → α)) × α → ℝ)
    (hd : ∀ x y, 0 ≤ d (x, y))
    (hdPre : ∀ x pfx, 0 ≤ dPre (x, pfx))
    (hdM : ∀ pfx b, 0 ≤ dM (pfx, b))
    (hdPost : ∀ z b, 0 ≤ dPost (z, b))
    (hPre : ∀ x pfx, dPre (x, pfx) = ∑ b, d (x, tExt pfx b))
    (hM : ∀ pfx b, dM (pfx, b) = ∑ x, d (x, tExt pfx b))
    (hPost : ∀ x pfx b, dPost ((x, pfx), b) = d (x, tExt pfx b)) :
    mutInfo d = mutInfo dPre + condEntH dM - condEntH dPost := by

  have hmargrank : margL d = margL dPre := by
    funext x
    simp only [margL]
    have h := Fintype.sum_tSplit_gen (fun y => d (x, y))
    have h2 : (∑ y : Fin (m + 1) → α, d (x, y))
        = ∑ pfx : Fin m → α, ∑ b, d (x, tExt pfx b) := by
      simpa using! h
    rw [h2]
    rw [Finset.sum_congr rfl (fun pfx _ => hPre x pfx)]

  have hM' : ∀ (pfx : Fin m → α) (b : α),
      margR d (tExt pfx b) = dM (pfx, b) := by
    intro pfx b
    rw [hM pfx b]
    rfl
  have hmargr : entH (margR d) = entH dM := by
    unfold entH
    have h := Fintype.sum_tSplit_gen (fun y => xlog2 (margR d y))
    have h2 : (∑ y : Fin (m + 1) → α, xlog2 (margR d y))
        = ∑ pfx : Fin m → α, ∑ b, xlog2 (margR d (tExt pfx b)) := by
      simpa using! h
    rw [h2]
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_congr rfl (fun pfx _ =>
      Finset.sum_congr rfl (fun b _ => congrArg xlog2 (hM' pfx b)))]

  have hpost : entH d = entH dPost := by
    have h := Fintype.sum_equiv (tSplitLawEquiv (n := n) (m := m))
      (fun z => xlog2 (d z))
      (fun z : (Fin n × (Fin m → α)) × α => xlog2 (dPost z)) (by
        intro z
        obtain ⟨x, y⟩ := z
        have hinv : (tSplitLawEquiv (n := n) (m := m)) (x, y) = ((x, tPre y), tLast y) := rfl
        rw [hinv]
        show xlog2 (d (x, y)) = xlog2 (dPost ((x, tPre y), tLast y))
        rw [hPost x (tPre y) (tLast y), tExt_tPre y])
    rw [Fintype.sum_prod_type] at h
    unfold entH
    rw [Fintype.sum_prod_type]
    exact congrArg Neg.neg h

  have hmargLPost : margL dPost = dPre := by
    funext z
    obtain ⟨x, pfx⟩ := z
    simp only [margL]
    rw [Finset.sum_congr rfl (fun b _ => hPost x pfx b)]
    exact (hPre x pfx).symm
  have hmargLM : margL dM = margR dPre := by
    funext pfx
    simp only [margL, margR]
    have h1 : (∑ b, dM (pfx, b)) = ∑ b, ∑ x, d (x, tExt pfx b) :=
      Finset.sum_congr rfl (fun b _ => hM pfx b)
    have h2 : (∑ i, dPre (i, pfx)) = ∑ x, ∑ b, d (x, tExt pfx b) :=
      Finset.sum_congr rfl (fun i _ => hPre i pfx)
    rw [h1, h2]
    exact Finset.sum_comm

  have hchainPost : entH dPost = entH dPre + condEntH dPost := by
    have hh := entH_chain_rule dPost hdPost
    rw [hmargLPost] at hh
    exact hh
  have hchainM : entH dM = entH (margR dPre) + condEntH dM := by
    have hh := entH_chain_rule dM hdM
    rw [hmargLM] at hh
    exact hh
  have hchainPre : entH dPre = entH (margL dPre) + condEntH dPre := by
    have hh := entH_chain_rule dPre hdPre
    exact hh
  have hchainHR : entH (margR d) + condEntHR d = entH d := by
    have hswap' : (∑ z : (Fin (m + 1) → α) × Fin n,
          xlog2 ((fun p : (Fin (m + 1) → α) × Fin n => d (p.2, p.1)) z))
        = ∑ z : Fin n × (Fin (m + 1) → α), xlog2 (d z) := by
      have hcc : (∑ b : Fin (m + 1) → α, ∑ a : Fin n, xlog2 (d (a, b)))
          = ∑ a : Fin n, ∑ b : Fin (m + 1) → α, xlog2 (d (a, b)) := by
        have h := Fintype.sum_equiv (Equiv.prodComm (Fin n) (Fin (m + 1) → α))
          (fun z : Fin n × (Fin (m + 1) → α) => xlog2 (d z))
          (fun z : (Fin (m + 1) → α) × Fin n => xlog2 (d (z.2, z.1))) (fun z => rfl)
        simp only [Fintype.sum_prod_type] at h
        exact h.symm
      simp only [Fintype.sum_prod_type]
      exact hcc
    have hswap : entH (fun p : (Fin (m + 1) → α) × Fin n => d (p.2, p.1)) = entH d := by
      unfold entH
      exact congrArg Neg.neg hswap'
    have hml : margL (fun p : (Fin (m + 1) → α) × Fin n => d (p.2, p.1)) = margR d := by
      funext j
      rfl
    have hh := entH_chain_rule
      (fun p : (Fin (m + 1) → α) × Fin n => d (p.2, p.1)) (fun i j => hd j i)
    rw [hswap, hml] at hh
    have hc : condEntH (fun p : (Fin (m + 1) → α) × Fin n => d (p.2, p.1)) = condEntHR d := rfl
    rw [hc] at hh
    exact hh.symm

  have hmutPre : mutInfo dPre = entH (margR dPre) - condEntH dPre :=
    mutInfo_eq_margR dPre hdPre
  rw [hmutPre]
  unfold mutInfo
  rw [hmargrank]
  linarith

/-- Binary symmetric channel weights are nonnegative when `0 ≤ p ≤ 1`. -/
theorem bscProb_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : Bool) (b : Bool) :
    0 ≤ bscProb p t b := by
  unfold bscProb
  by_cases h : b = t
  · simp [h, hp0]
  · simp [h]
    linarith

/-- Binary transcript likelihoods are nonnegative when `0 ≤ p ≤ 1`. -/
theorem bscLik_nonneg {n k : ℕ} (prog : BscProgram n k) (p : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (x : Fin n) (y : Fin k → Bool) : 0 ≤ bscLik prog p x y := by
  unfold bscLik
  exact Finset.prod_nonneg fun i _ => bscProb_nonneg hp0 hp1 _ _

/-- The binary program joint weights are nonnegative for a nonempty hidden-cell space and `0 ≤ p
≤ 1`. -/
theorem bscJoint_nonneg {n k : ℕ} (prog : BscProgram n k) (p : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (hn : 0 < n) (x : Fin n) (y : Fin k → Bool) :
    0 ≤ bscJoint prog p x y := by
  unfold bscJoint
  have h1 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  exact mul_nonneg h1 (bscLik_nonneg prog p hp0 hp1 x y)

/-- The prefix-likelihood construction applied to all program cuts equals the program transcript
likelihood. -/
theorem bscLikPre_eq_bscLik {n k : ℕ} (prog : BscProgram n k) (p : ℝ) (x : Fin n)
    (y : Fin k → Bool) : bscLikPre prog.cuts p x y = bscLik prog p x y := by
  unfold bscLikPre bscLik
  have hc : ∀ j : Fin k,
      bscProb p (truthBit x (prog.cuts j (tRestrict y j))) (y j)
        = bscProb p (truthBit x (prog.cuts j (answerPrefix y j))) (y j) := by
    intro j
    rw [← answerPrefix_eq_tRestrict]
  rw [Finset.prod_congr rfl (fun j _ => hc j)]

/-- Conditional entropy is the left-marginal weighted sum of the entropies of conditional rows
for nonnegative joint weights. -/
theorem condEntH_eq_sum {α β : Type} [Fintype α] [Fintype β] (d : α × β → ℝ)
    (hd : ∀ i j, 0 ≤ d (i, j)) :
    condEntH d = ∑ i, margL d i * entH (fun j => condW d i j) := by
  have key : ∀ i : α, -(∑ j, d (i, j) * (Real.log (condW d i j) / Real.log 2))
      = margL d i * entH (fun j => condW d i j) := by
    intro i
    have hmul : ∀ j, d (i, j) = margL d i * condW d i j := by
      intro j
      exact (condW_mul_margL d hd i j).symm
    have helem : ∀ j : β, d (i, j) * (Real.log (condW d i j) / Real.log 2)
        = margL d i * (condW d i j * (Real.log (condW d i j) / Real.log 2)) := by
      intro j
      rw [hmul j]
      ring
    have h1 : (∑ j, d (i, j) * (Real.log (condW d i j) / Real.log 2))
        = ∑ j, margL d i * (condW d i j * (Real.log (condW d i j) / Real.log 2)) := by
      rw [Finset.sum_congr rfl (fun j _ => helem j)]
    have h2 : (∑ j, margL d i * (condW d i j * (Real.log (condW d i j) / Real.log 2)))
        = margL d i * (∑ j, condW d i j * (Real.log (condW d i j) / Real.log 2)) := by
      rw [Finset.mul_sum]
    have h3 : entH (fun j => condW d i j)
        = -(∑ j, condW d i j * (Real.log (condW d i j) / Real.log 2)) := by
      simp only [entH, xlog2]
    rw [h1, h2, h3]
    ring
  unfold condEntH
  rw [← Finset.sum_neg_distrib]
  rw [Finset.sum_congr rfl (fun i _ => key i)]

/-- The entropy of a binary symmetric channel answer row equals `binEntropy p`. -/
theorem entH_bscProb {p : ℝ} (t : Bool) : entH (bscProb p t) = binEntropy p := by
  cases t <;> simp [entH, xlog2, bscProb] <;>
    unfold binEntropy <;> ring

/-- Adaptive binary prefix likelihoods are nonnegative when `0 ≤ p ≤ 1`. -/
theorem bscLikPre_nonneg {n m : ℕ} (cuts : ∀ i : Fin m, (Fin i.val → Bool) → Fin n)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : Fin n) (pfx : Fin m → Bool) :
    0 ≤ bscLikPre cuts p x pfx := by
  unfold bscLikPre
  exact Finset.prod_nonneg fun j _ => bscProb_nonneg hp0 hp1 _ _

/-- The joint weights defined by adaptive binary cuts are nonnegative for `0 ≤ p ≤ 1` and `n >
0`. -/
theorem bscJointCuts_nonneg {n m : ℕ} (cuts : ∀ i : Fin m, (Fin i.val → Bool) → Fin n)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n) (x : Fin n) (y : Fin m → Bool) :
    0 ≤ bscJointCuts cuts p x y := by
  unfold bscJointCuts
  have h1 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  exact mul_nonneg h1 (bscLikPre_nonneg cuts p hp0 hp1 x y)

/-- Given the hidden cell and transcript prefix, the final binary answer has conditional entropy
`binEntropy p` for `0 ≤ p ≤ 1` and `n > 0`. -/
theorem condEntH_bscJointPost {n m : ℕ} (cuts : ∀ i : Fin (m + 1), (Fin i.val → Bool) → Fin n)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n) :
    condEntH (fun z : (Fin n × (Fin m → Bool)) × Bool =>
      bscJointCuts cuts p (z.1.1) (tExt z.1.2 z.2)) = binEntropy p := by
  have hfac : ∀ (x : Fin n) (pfx : Fin m → Bool) (b : Bool),
      bscJointCuts cuts p x (tExt pfx b)
        = bscJointCuts (fun j => cuts (j.castSucc)) p x pfx * bscStepCond cuts p x pfx b := by
    intro x pfx b
    unfold bscJointCuts
    rw [bscLikPre_split cuts p x pfx b]
    ring
  have hmarg : ∀ (x : Fin n) (pfx : Fin m → Bool),
      margL (fun z : (Fin n × (Fin m → Bool)) × Bool =>
        bscJointCuts cuts p (z.1.1) (tExt z.1.2 z.2)) (x, pfx)
        = bscJointCuts (fun j => cuts (j.castSucc)) p x pfx := by
    intro x pfx
    simp only [margL]
    have helem : ∀ b : Bool, bscJointCuts cuts p x (tExt pfx b)
        = bscJointCuts (fun j => cuts (j.castSucc)) p x pfx * bscStepCond cuts p x pfx b :=
      hfac x pfx
    have hsum : (∑ b, bscJointCuts cuts p x (tExt pfx b))
        = bscJointCuts (fun j => cuts (j.castSucc)) p x pfx * (∑ b, bscStepCond cuts p x pfx b) := by
      rw [Finset.sum_congr rfl (fun b _ => helem b)]
      rw [← Finset.mul_sum]
    have h1 : (∑ b, bscStepCond cuts p x pfx b) = 1 := by
      unfold bscStepCond
      exact bscProb_sum (truthBit x (cuts (Fin.last m) pfx))
    rw [hsum, h1]
    simp
  have hcond : ∀ (x : Fin n) (pfx : Fin m → Bool) (b : Bool),
      bscJointCuts (fun j => cuts (j.castSucc)) p x pfx ≠ 0 →
      condW (fun z : (Fin n × (Fin m → Bool)) × Bool =>
        bscJointCuts cuts p (z.1.1) (tExt z.1.2 z.2)) (x, pfx) b
        = bscStepCond cuts p x pfx b := by
    intro x pfx b hne
    have hm : margL (fun z : (Fin n × (Fin m → Bool)) × Bool =>
        bscJointCuts cuts p (z.1.1) (tExt z.1.2 z.2)) (x, pfx) ≠ 0 := by
      rw [hmarg x pfx]
      exact hne
    simp only [condW, dif_neg hm]
    rw [hfac x pfx b, hmarg x pfx]
    field_simp
  have key : ∀ (x : Fin n) (pfx : Fin m → Bool),
      margL (fun z : (Fin n × (Fin m → Bool)) × Bool =>
        bscJointCuts cuts p (z.1.1) (tExt z.1.2 z.2)) (x, pfx)
          * entH (fun b => condW (fun z : (Fin n × (Fin m → Bool)) × Bool =>
              bscJointCuts cuts p (z.1.1) (tExt z.1.2 z.2)) (x, pfx) b)
        = margL (fun z : (Fin n × (Fin m → Bool)) × Bool =>
            bscJointCuts cuts p (z.1.1) (tExt z.1.2 z.2)) (x, pfx) * binEntropy p := by
    intro x pfx
    by_cases hne : bscJointCuts (fun j => cuts (j.castSucc)) p x pfx ≠ 0
    · have hfun : (fun b => condW (fun z : (Fin n × (Fin m → Bool)) × Bool =>
            bscJointCuts cuts p (z.1.1) (tExt z.1.2 z.2)) (x, pfx) b)
          = (fun b => bscStepCond cuts p x pfx b) := by
        funext b
        exact hcond x pfx b hne
      have hent : entH (fun b => bscStepCond cuts p x pfx b) = binEntropy p := by
        unfold bscStepCond
        exact entH_bscProb (truthBit x (cuts (Fin.last m) pfx))
      rw [hfun, hent]
    · have hm0 : margL (fun z : (Fin n × (Fin m → Bool)) × Bool =>
          bscJointCuts cuts p (z.1.1) (tExt z.1.2 z.2)) (x, pfx) = 0 := by
        rw [hmarg x pfx]
        exact not_ne_iff.mp hne
      have hcw : (fun b => condW (fun z : (Fin n × (Fin m → Bool)) × Bool =>
          bscJointCuts cuts p (z.1.1) (tExt z.1.2 z.2)) (x, pfx) b) = (fun _ => 0) := by
        funext b
        simp [condW, hm0]
      have hent0 : entH (fun _ : Bool => 0) = 0 := by
        unfold entH xlog2
        simp
      rw [hcw, hent0]
      simp [hm0]

  have hmass : (∑ z : Fin n × (Fin m → Bool),
      margL (fun z' : (Fin n × (Fin m → Bool)) × Bool =>
        bscJointCuts cuts p (z'.1.1) (tExt z'.1.2 z'.2)) z) = 1 := by
    have helem : ∀ (x : Fin n) (pfx : Fin m → Bool),
        margL (fun z' : (Fin n × (Fin m → Bool)) × Bool =>
          bscJointCuts cuts p (z'.1.1) (tExt z'.1.2 z'.2)) (x, pfx)
          = bscJointCuts (fun j => cuts (j.castSucc)) p x pfx := by
      intro x pfx
      exact hmarg x pfx
    rw [Finset.sum_congr rfl (fun z _ => helem z.1 z.2)]
    rw [Fintype.sum_prod_type]
    have hstep : ∀ (x : Fin n), (∑ pfx : Fin m → Bool,
        bscJointCuts (fun j => cuts (j.castSucc)) p x pfx) = 1 / (n : ℝ) := by
      intro x
      have helem' : ∀ pfx : Fin m → Bool,
          bscJointCuts (fun j => cuts (j.castSucc)) p x pfx
            = (1 / (n : ℝ)) * bscLikPre (fun j => cuts (j.castSucc)) p x pfx := by
        intro pfx
        rfl
      rw [Finset.sum_congr rfl (fun pfx _ => helem' pfx)]
      rw [← Finset.mul_sum]
      rw [bscLikPre_sum_one (fun j => cuts (j.castSucc)) p x]
      simp
    rw [Finset.sum_congr rfl (fun x _ => hstep x)]
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_fin]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    field_simp

  have h := condEntH_eq_sum (fun z : (Fin n × (Fin m → Bool)) × Bool =>
      bscJointCuts cuts p (z.1.1) (tExt z.1.2 z.2)) (fun z b =>
    bscJointCuts_nonneg cuts p hp0 hp1 hn z.1 (tExt z.2 b))
  rw [h]
  have hkey : ∀ z : Fin n × (Fin m → Bool),
      margL (fun z' : (Fin n × (Fin m → Bool)) × Bool =>
        bscJointCuts cuts p (z'.1.1) (tExt z'.1.2 z'.2)) z
          * entH (fun b => condW (fun z' : (Fin n × (Fin m → Bool)) × Bool =>
              bscJointCuts cuts p (z'.1.1) (tExt z'.1.2 z'.2)) z b)
        = margL (fun z' : (Fin n × (Fin m → Bool)) × Bool =>
            bscJointCuts cuts p (z'.1.1) (tExt z'.1.2 z'.2)) z * binEntropy p :=
    fun z => key z.1 z.2
  rw [Finset.sum_congr rfl (fun z _ => hkey z)]
  rw [Finset.sum_congr rfl (fun z _ => mul_comm _ _)]
  rw [← Finset.mul_sum]
  rw [hmass]
  ring

/-- The conditional entropy of a Boolean variable under normalized nonnegative joint weights is
at most one bit. -/
theorem condEntH_le_one {α : Type} [Fintype α] (d : α × Bool → ℝ)
    (hd : ∀ i b, 0 ≤ d (i, b)) (htot : ∑ i, ∑ b, d (i, b) = 1) :
    condEntH d ≤ 1 := by
  have h := condEntH_eq_sum d hd
  rw [h]
  have hkey : ∀ i : α, margL d i * entH (fun b => condW d i b) ≤ margL d i := by
    intro i
    by_cases hm : margL d i = 0
    · have hcw : (fun b => condW d i b) = (fun _ => 0) := by
        funext b
        simp [condW, hm]
      have hent0 : entH (fun _ : Bool => 0) = 0 := by
        unfold entH xlog2
        simp
      rw [hcw, hent0]
      simp [hm]
    · have hsum1 : (∑ b : Bool, condW d i b) = 1 := condW_sum d hd i hm
      have hnonneg : ∀ b : Bool, 0 ≤ condW d i b := fun b => condW_nonneg d hd i b
      have hent : entH (fun b => condW d i b) ≤ 1 := by
        have h1 := entH_le_log_card (fun b => condW d i b) hnonneg hsum1 (by decide)
        have hlog : Real.log (Fintype.card Bool : ℝ) / Real.log 2 = 1 := by
          simp [Fintype.card_bool]
          norm_num
        rw [hlog] at h1
        exact h1
      have hnonneg' : 0 ≤ margL d i := Finset.sum_nonneg fun b _ => hd i b
      simpa using! mul_le_mul_of_nonneg_left hent hnonneg'
  have h1 : (∑ i, margL d i * entH (fun b => condW d i b)) ≤ ∑ i, margL d i :=
    Finset.sum_le_sum fun i _ => hkey i
  have hmass : (∑ i, margL d i) = 1 := by
    have h2 : (∑ i, ∑ b : Bool, d (i, b)) = ∑ i, margL d i := by
      simp only [margL]
    rw [← h2]
    exact htot
  calc (∑ i, margL d i * entH (fun b => condW d i b)) ≤ ∑ i, margL d i := h1
    _ = 1 := hmass

/-- The likelihood of an empty binary transcript equals one. -/
theorem bscLikPre_zero {n : ℕ} (cuts : ∀ i : Fin 0, (Fin i.val → Bool) → Fin n)
    (p : ℝ) (x : Fin n) (y : Fin 0 → Bool) : bscLikPre cuts p x y = 1 := by
  simp [bscLikPre]

/-- The joint weights of a uniform hidden cell and an adaptive binary transcript sum to one when
`n > 0`. -/
theorem bscJointLaw_total {n m : ℕ} (cuts : ∀ i : Fin m, (Fin i.val → Bool) → Fin n)
    (p : ℝ) (hn : 0 < n) :
    (∑ x : Fin n, ∑ y : Fin m → Bool, bscJointLaw cuts p (x, y)) = 1 := by
  have hkey : ∀ x : Fin n, (∑ y : Fin m → Bool, bscJointLaw cuts p (x, y))
      = 1 / (n : ℝ) := by
    intro x
    have h1 : (∑ y : Fin m → Bool, bscLikPre cuts p x y) = 1 :=
      bscLikPre_sum_one cuts p x
    have h2 : (∑ y : Fin m → Bool, bscJointLaw cuts p (x, y))
        = (1 / (n : ℝ)) * (∑ y : Fin m → Bool, bscLikPre cuts p x y) := by
      simp only [bscJointLaw, bscJointCuts]
      rw [sum_const_mul]
    rw [h2, h1]
    simp
  rw [Finset.sum_congr rfl (fun x _ => hkey x)]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_fin]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp

/-- The left marginal of the adaptive binary joint law is the uniform weight `1 / n`. -/
theorem bscJointLaw_margL {n m : ℕ} (cuts : ∀ i : Fin m, (Fin i.val → Bool) → Fin n)
    (p : ℝ) (x : Fin n) :
    margL (bscJointLaw cuts p) x = 1 / (n : ℝ) := by
  simp only [margL, bscJointLaw, bscJointCuts]
  have h1 : (∑ y : Fin m → Bool, bscLikPre cuts p x y) = 1 :=
    bscLikPre_sum_one cuts p x
  rw [sum_const_mul, h1]
  simp

/-- An empty binary transcript has zero mutual information with a uniform hidden cell for `0 ≤ p
≤ 1` and `n > 0`. -/
theorem bscMutInfo_zero {n : ℕ} (cuts : ∀ i : Fin 0, (Fin i.val → Bool) → Fin n)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n) : bscMutInfo cuts p = 0 := by
  have hd : ∀ x y, 0 ≤ bscJointLaw cuts p (x, y) := by
    intro x y
    exact bscJointCuts_nonneg cuts p hp0 hp1 hn x y
  have hdval : ∀ x y, bscJointLaw cuts p (x, y) = 1 / (n : ℝ) := by
    intro x y
    simp [bscJointLaw, bscJointCuts, bscLikPre_zero]
  have hmargR : ∀ y, margR (bscJointLaw cuts p) y = 1 := by
    intro y
    simp only [margR]
    rw [Finset.sum_congr rfl (fun x _ => hdval x y)]
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_fin]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    field_simp
  have hent : entH (margR (bscJointLaw cuts p)) = 0 := by
    unfold entH xlog2
    rw [Finset.sum_congr rfl (fun y _ => by rw [hmargR y])]
    simp
  have hmargL : ∀ x, margL (bscJointLaw cuts p) x = 1 / (n : ℝ) :=
    bscJointLaw_margL cuts p
  have hcW : ∀ x y, condW (bscJointLaw cuts p) x y = 1 := by
    intro x y
    have hmul := condW_mul_margL (bscJointLaw cuts p) hd x y
    rw [hmargL x, hdval x y] at hmul
    have hne : (1 / (n : ℝ)) ≠ 0 := by
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      positivity
    have hmul' : (1 / (n : ℝ)) * condW (bscJointLaw cuts p) x y
        = (1 / (n : ℝ)) * 1 := by rw [hmul]; ring
    exact mul_left_cancel₀ hne hmul'
  have hcond : condEntH (bscJointLaw cuts p) = 0 := by
    unfold condEntH
    rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by
      rw [hcW x y]))]
    simp
  have h := mutInfo_eq_margR (bscJointLaw cuts p) hd
  unfold bscMutInfo
  rw [h, hent, hcond]
  simp

/-- Summing the extended binary joint law over the final answer recovers the prefix joint law. -/
theorem bscJointLaw_prefix_marginal {n m : ℕ}
    (cuts : ∀ i : Fin (m + 1), (Fin i.val → Bool) → Fin n) (p : ℝ) (x : Fin n)
    (pfx : Fin m → Bool) :
    bscJointLaw (cutsPre cuts) p (x, pfx) = ∑ b, bscJointLaw cuts p (x, tExt pfx b) := by
  have hsum : (∑ b, bscLikPre cuts p x (tExt pfx b))
      = bscLikPre (cutsPre cuts) p x pfx := by
    have hstep : ∀ b : Bool,
        bscLikPre cuts p x (tExt pfx b)
          = bscLikPre (cutsPre cuts) p x pfx * bscStepCond cuts p x pfx b := by
      intro b
      have h := bscLikPre_split cuts p x pfx b
      have h' : bscLikPre cuts p x (tExt pfx b)
          = bscLikPre (cutsPre cuts) p x pfx * bscStepCond cuts p x pfx b := by
        simpa only [cutsPre] using! h
      exact h'
    rw [Finset.sum_congr rfl (fun b _ => hstep b)]
    have h1 : (∑ b, bscStepCond cuts p x pfx b) = 1 := by
      unfold bscStepCond
      exact bscProb_sum (truthBit x (cuts (Fin.last m) pfx))
    rw [← Finset.mul_sum, h1]
    simp
  simp only [bscJointLaw, bscJointCuts]
  rw [sum_const_mul, hsum]

/-- Splits binary transcript mutual information into prefix information plus the final-answer
conditional entropy gain. -/
theorem bscMutInfo_step {n m : ℕ} (cuts : ∀ i : Fin (m + 1), (Fin i.val → Bool) → Fin n)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n) :
    bscMutInfo cuts p
      = bscMutInfo (cutsPre cuts) p
        + condEntH (fun z : (Fin m → Bool) × Bool =>
            ∑ x, bscJointCuts cuts p x (tExt z.1 z.2))
        - condEntH (fun z : (Fin n × (Fin m → Bool)) × Bool =>
            bscJointCuts cuts p (z.1.1) (tExt z.1.2 z.2)) := by
  have hd : ∀ x y, 0 ≤ bscJointLaw cuts p (x, y) := by
    intro x y
    exact bscJointCuts_nonneg cuts p hp0 hp1 hn x y
  have hdPre : ∀ x pfx, 0 ≤ bscJointLaw (cutsPre cuts) p (x, pfx) := by
    intro x pfx
    exact bscJointCuts_nonneg (cutsPre cuts) p hp0 hp1 hn x pfx
  have hPre : ∀ (x : Fin n) (pfx : Fin m → Bool),
      bscJointLaw (cutsPre cuts) p (x, pfx) = ∑ b, bscJointLaw cuts p (x, tExt pfx b) :=
    fun x pfx => bscJointLaw_prefix_marginal cuts p x pfx
  have h := mutInfo_split (d := bscJointLaw cuts p)
    (dPre := bscJointLaw (cutsPre cuts) p)
    (dM := fun z : (Fin m → Bool) × Bool => ∑ x, bscJointLaw cuts p (x, tExt z.1 z.2))
    (dPost := fun z : (Fin n × (Fin m → Bool)) × Bool =>
      bscJointLaw cuts p (z.1.1, tExt z.1.2 z.2))
    hd hdPre
    (fun pfx b => Finset.sum_nonneg fun x _ => hd x (tExt pfx b))
    (fun z b => by obtain ⟨x, pfx⟩ := z; exact hd x (tExt pfx b))
    hPre
    (fun pfx b => rfl)
    (fun x pfx b => rfl)
  exact h

/-- For `0 ≤ p ≤ 1` and `n > 0`, the mutual information in `m` adaptive binary answers is at
most `m * queryInfo p`. -/
theorem bscMutInfo_le {n m : ℕ} (cuts : ∀ i : Fin m, (Fin i.val → Bool) → Fin n)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n) :
    bscMutInfo cuts p ≤ (m : ℝ) * queryInfo p := by
  induction m with
  | zero =>
      rw [bscMutInfo_zero cuts p hp0 hp1 hn]
      simp [queryInfo]
  | succ m ih =>
      have hstep := bscMutInfo_step cuts p hp0 hp1 hn
      have hpost : condEntH (fun z : (Fin n × (Fin m → Bool)) × Bool =>
          bscJointCuts cuts p (z.1.1) (tExt z.1.2 z.2)) = binEntropy p :=
        condEntH_bscJointPost cuts p hp0 hp1 hn
      have hM : condEntH (fun z : (Fin m → Bool) × Bool =>
          ∑ x, bscJointCuts cuts p x (tExt z.1 z.2)) ≤ 1 := by
        refine condEntH_le_one _ ?_ ?_
        · intro pfx b
          exact Finset.sum_nonneg fun x _ =>
            bscJointCuts_nonneg cuts p hp0 hp1 hn x (tExt pfx b)
        · have hsplit : (∑ pfx : Fin m → Bool, ∑ b,
              ∑ x, bscJointCuts cuts p x (tExt pfx b))
              = ∑ x : Fin n, ∑ y : Fin (m + 1) → Bool, bscJointCuts cuts p x y := by
            have h := Fintype.sum_tSplit_gen (m := m)
              (fun y : Fin (m + 1) → Bool => ∑ x, bscJointCuts cuts p x y)
            have h2 : (∑ y : Fin (m + 1) → Bool, ∑ x, bscJointCuts cuts p x y)
                = ∑ pfx : Fin m → Bool, ∑ b, ∑ x, bscJointCuts cuts p x (tExt pfx b) := by
              simpa using! h
            rw [← h2]
            exact Finset.sum_comm
          rw [hsplit]
          have h := bscJointLaw_total cuts p hn
          simpa only [bscJointLaw] using! h
      have hih : bscMutInfo (cutsPre cuts) p ≤ (m : ℝ) * queryInfo p :=
        ih (cutsPre cuts)
      have h1 : bscMutInfo cuts p
          ≤ bscMutInfo (cutsPre cuts) p + (1 - binEntropy p) := by
        rw [hstep, hpost]
        linarith
      calc bscMutInfo cuts p
          ≤ bscMutInfo (cutsPre cuts) p + (1 - binEntropy p) := h1
        _ ≤ (m : ℝ) * queryInfo p + (1 - binEntropy p) :=
          add_le_add_left hih (1 - binEntropy p)
        _ = ((m + 1 : ℕ) : ℝ) * queryInfo p := by
            have hq : queryInfo p = 1 - binEntropy p := rfl
            rw [hq]
            simp only [Nat.cast_succ]
            ring

/-- The binary program error probability is nonnegative for `0 ≤ p ≤ 1` and `n > 0`. -/
theorem bscErrorProb_nonneg {n k : ℕ} (prog : BscProgram n k) {p : ℝ} (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (hn : 0 < n) : 0 ≤ bscErrorProb prog p := by
  have hkey : ∀ x y, 0 ≤ bscJoint prog p x y * (if bscError prog x y then 1 else 0) := by
    intro x y
    exact mul_nonneg (bscJoint_nonneg prog p hp0 hp1 hn x y) (by split <;> norm_num)
  unfold bscErrorProb
  exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => hkey x y

/-- Expresses binary program error as the joint-law weighted indicator that the decoder differs
from the hidden cell. -/
theorem bscErrorProb_eq_fano_error {n k : ℕ} (prog : BscProgram n k) (p : ℝ) :
    bscErrorProb prog p
      = ∑ y : Fin k → Bool, ∑ x : Fin n, bscJointLaw prog.cuts p (x, y)
          * (if prog.guess y = x then 0 else 1) := by
  have hkey : ∀ x y, bscJoint prog p x y = bscJointLaw prog.cuts p (x, y) := by
    intro x y
    unfold bscJoint bscJointLaw bscJointCuts
    rw [bscLikPre_eq_bscLik]
  have herror : ∀ x y, (if bscError prog x y = true then (1 : ℝ) else 0)
      = (if prog.guess y = x then 0 else 1) := by
    intro x y
    unfold bscError
    by_cases h : prog.guess y = x
    · simp [h]
    · simp [h]
  have hcell : ∀ x y, bscJoint prog p x y * (if bscError prog x y = true then 1 else 0)
      = bscJointLaw prog.cuts p (x, y) * (if prog.guess y = x then 0 else 1) := by
    intro x y
    rw [hkey x y]
    congr 1
    exact herror x y
  unfold bscErrorProb
  calc (∑ x : Fin n, ∑ y : Fin k → Bool,
        bscJoint prog p x y * (if bscError prog x y = true then 1 else 0))
      = ∑ y : Fin k → Bool, ∑ x : Fin n,
        bscJoint prog p x y * (if bscError prog x y = true then 1 else 0) := Finset.sum_comm
    _ = ∑ y : Fin k → Bool, ∑ x : Fin n,
        bscJointLaw prog.cuts p (x, y) * (if prog.guess y = x then 0 else 1) := by
          rw [Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun x _ => hcell x y))]
    _ = ∑ y : Fin k → Bool, ∑ x : Fin n, bscJointLaw prog.cuts p (x, y)
          * (if prog.guess y = x then 0 else 1) := rfl

/-- The information per query is positive for `1 / 2 < p ≤ 1`, including the noiseless endpoint. -/
theorem clause17_queryInfo_pos_of {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) : 0 < queryInfo p := by
  rcases lt_or_eq_of_le hp1 with hlt | heq
  · exact clause17_queryInfo_pos hp hlt
  · rw [heq, clause17_queryInfo_one]
    norm_num

/-- Binary entropy is monotone on the interval `[0, 1 / 2]`. -/
theorem clause17_binEntropy_mono {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2) (hab : a ≤ b) : binEntropy a ≤ binEntropy b := by
  have hma : a ∈ Set.Icc (0 : ℝ) (2 : ℝ)⁻¹ := by
    refine ⟨ha0, ?_⟩
    rw [show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num]
    exact ha1
  have hmb : b ∈ Set.Icc (0 : ℝ) (2 : ℝ)⁻¹ := by
    refine ⟨hb0, ?_⟩
    rw [show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num]
    exact hb1
  have hmono := Real.binEntropy_strictMonoOn.monotoneOn hma hmb hab
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : Real.binEntropy a / Real.log 2 ≤ Real.binEntropy b / Real.log 2 :=
    div_le_div_of_nonneg_right hmono (le_of_lt hlog2)
  rw [clause17_binEntropy_eq_mathlib, clause17_binEntropy_eq_mathlib]
  exact h1

/-- A binary program with at least two hidden cells, `1 / 2 < p ≤ 1`, and actual error at most
one half uses at least the corresponding Fano capacity bound in comparisons
[BenOrHassidim2007]. -/
theorem clause17_same_run_comparison_lower_bound_actual {n k : ℕ} (hn : 2 ≤ n)
    (prog : BscProgram n k) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp : 1 / 2 < p)
    (hε1 : bscErrorProb prog p ≤ 1 / 2) :
    fanoCapacityBound n p (bscErrorProb prog p) ≤ (k : ℝ) := by
  have hn0 : 0 < n := by omega
  have hd : ∀ x y, 0 ≤ bscJointLaw prog.cuts p (x, y) := by
    intro x y
    exact bscJointCuts_nonneg prog.cuts p hp0 hp1 hn0 x y
  have ht : (∑ x : Fin n, ∑ y : Fin k → Bool, bscJointLaw prog.cuts p (x, y)) = 1 :=
    bscJointLaw_total prog.cuts p hn0
  have hmarg : ∀ x, (∑ y : Fin k → Bool, bscJointLaw prog.cuts p (x, y))
      = 1 / (n : ℝ) := fun x => bscJointLaw_margL prog.cuts p x
  have hε : bscErrorProb prog p
      = ∑ y : Fin k → Bool, ∑ x : Fin n, bscJointLaw prog.cuts p (x, y)
          * (if prog.guess y = x then 0 else 1) := bscErrorProb_eq_fano_error prog p
  have hε0 : 0 ≤ bscErrorProb prog p := bscErrorProb_nonneg prog hp0 hp1 hn0
  have hfano := fano_capacity_arith hn (bscJointLaw prog.cuts p) hd ht hmarg
    prog.guess (bscErrorProb prog p) hε hε0 hε1
  have hmi : mutInfo (bscJointLaw prog.cuts p) ≤ (k : ℝ) * queryInfo p := by
    have h := bscMutInfo_le (n := n) (m := k) prog.cuts p hp0 hp1 hn0
    exact h
  have hnum : fanoNumerator n (bscErrorProb prog p) ≤ (k : ℝ) * queryInfo p := by
    unfold fanoNumerator
    linarith [hfano, hmi]
  have hqi : 0 < queryInfo p := clause17_queryInfo_pos_of hp hp1
  unfold fanoCapacityBound
  rw [div_le_iff₀ hqi]
  exact hnum

/-- A binary program with error at most `δ ≤ 1 / 2` and `1 / 2 < p ≤ 1` uses at least
`fanoCapacityBound n p δ` comparisons when `n ≥ 2` [BenOrHassidim2007]. -/
theorem clause17_same_run_comparison_lower_bound {n k : ℕ} (hn : 2 ≤ n)
    (prog : BscProgram n k) {p δ : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp : 1 / 2 < p)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) (herr : bscErrorProb prog p ≤ δ) :
    (k : ℝ) ≥ fanoCapacityBound n p δ := by
  have hn0 : 0 < n := by omega
  have hε1 : bscErrorProb prog p ≤ 1 / 2 := le_trans herr hδ1
  have hactual : fanoCapacityBound n p (bscErrorProb prog p) ≤ (k : ℝ) :=
    clause17_same_run_comparison_lower_bound_actual hn prog hp0 hp1 hp hε1
  have hqi : 0 < queryInfo p := clause17_queryInfo_pos_of hp hp1
  have hbin : binEntropy (bscErrorProb prog p) ≤ binEntropy δ :=
    clause17_binEntropy_mono (bscErrorProb_nonneg prog hp0 hp1 hn0) hε1 hδ0 hδ1 herr
  have hlogL : (0 : ℝ) ≤ Real.log ((n - 1 : ℕ) : ℝ) / Real.log 2 := by
    have h1 : (1 : ℕ) ≤ n - 1 := by omega
    have h2 : (0 : ℝ) ≤ Real.log ((n - 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast h1)
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    exact div_nonneg h2 (le_of_lt hlog2)
  have hmul : bscErrorProb prog p * (Real.log ((n - 1 : ℕ) : ℝ) / Real.log 2)
      ≤ δ * (Real.log ((n - 1 : ℕ) : ℝ) / Real.log 2) :=
    mul_le_mul_of_nonneg_right herr hlogL
  have hnum : fanoNumerator n δ ≤ (k : ℝ) * queryInfo p := by
    have h1 : fanoNumerator n δ ≤ fanoNumerator n (bscErrorProb prog p) := by
      unfold fanoNumerator
      linarith [hbin, hmul]
    have h2 : fanoNumerator n (bscErrorProb prog p) ≤ (k : ℝ) * queryInfo p := by
      have hnum' : fanoNumerator n (bscErrorProb prog p) ≤ (k : ℝ) * queryInfo p := by
        unfold fanoCapacityBound at hactual
        rw [div_le_iff₀ hqi] at hactual
        exact hactual
      exact hnum'
    exact h1.trans h2
  have hfin : fanoCapacityBound n p δ ≤ (k : ℝ) := by
    unfold fanoCapacityBound
    rw [div_le_iff₀ hqi]
    exact hnum
  exact hfin

/-- Establishes `FanoCapacitySmallN` for at most one hidden cell, `1 / 2 < p ≤ 1`, and `0 ≤ δ ≤
1`. -/
theorem clause17_capacity_small_n {n : ℕ} (hn : n ≤ 1) {p δ : ℝ} (hp : 1 / 2 < p)
    (hp1 : p ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    FanoCapacitySmallN n p δ := by
  intro _
  have hqi : 0 < queryInfo p := clause17_queryInfo_pos_of hp hp1
  have hlog1 : Real.log (n : ℝ) / Real.log 2 = 0 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · have hn1 : n = 1 := by omega
      subst hn1; simp
  have hlog0 : Real.log ((n - 1 : ℕ) : ℝ) / Real.log 2 = 0 := by
    have h : n - 1 = 0 := by omega
    simp [h]
  have hbin : 0 ≤ binEntropy δ := by
    rw [clause17_binEntropy_eq_mathlib]
    have h := Real.binEntropy_nonneg hδ0 hδ1
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    exact div_nonneg h (le_of_lt hlog2)
  unfold fanoCapacityBound
  rw [div_le_iff₀ hqi]
  unfold fanoNumerator
  rw [hlog1, hlog0]
  linarith

/-- At `p = 1`, the Fano capacity bound equals its numerator. -/
theorem clause17_capacity_at_p_one {n : ℕ} (δ : ℝ) :
    fanoCapacityBound n 1 δ = fanoNumerator n δ := by
  unfold fanoCapacityBound
  rw [clause17_queryInfo_one]
  simp

/-- For two hidden cells, the Fano numerator is `1 - binEntropy δ`. -/
theorem clause17_fanoNumerator_two (δ : ℝ) :
    fanoNumerator 2 δ = 1 - binEntropy δ := by
  unfold fanoNumerator
  have hL2 : Real.log ((2 : ℕ) : ℝ) / Real.log 2 = 1 := by
    have hne : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    have hcast : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [hcast, div_self hne]
  have hL1 : Real.log ((2 - 1 : ℕ) : ℝ) / Real.log 2 = 0 := by
    have hcast : ((2 - 1 : ℕ) : ℝ) = 1 := by norm_num
    rw [hcast, Real.log_one, zero_div]
  rw [hL2, hL1]
  ring

/-- The two-cell capacity expression at correctness `3 / 4` and error parameter `9 / 10` is
strictly greater than one. -/
theorem clause17_capacity_at_delta_nine_tenths :
    1 < fanoCapacityBound 2 (3 / 4 : ℝ) (9 / 10 : ℝ) := by
  have hmono : Real.binEntropy (1 / 10 : ℝ) < Real.binEntropy (1 / 4 : ℝ) := by
    have h1 : (1 / 10 : ℝ) ∈ Set.Icc (0 : ℝ) (2 : ℝ)⁻¹ := by
      refine ⟨by norm_num, ?_⟩
      rw [show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num]
      norm_num
    have h2 : (1 / 4 : ℝ) ∈ Set.Icc (0 : ℝ) (2 : ℝ)⁻¹ := by
      refine ⟨by norm_num, ?_⟩
      rw [show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num]
      norm_num
    exact Real.binEntropy_strictMonoOn h1 h2 (by norm_num)
  have hbin : binEntropy (9 / 10 : ℝ) < binEntropy (3 / 4 : ℝ) := by
    have h1 := clause17_binEntropy_symmetry (9 / 10 : ℝ)
    have h2 := clause17_binEntropy_symmetry (3 / 4 : ℝ)
    rw [h1, h2]
    have h1' : (1 - 9 / 10 : ℝ) = 1 / 10 := by norm_num
    have h2' : (1 - 3 / 4 : ℝ) = 1 / 4 := by norm_num
    rw [h1', h2']
    rw [clause17_binEntropy_eq_mathlib, clause17_binEntropy_eq_mathlib]
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    exact (div_lt_div_iff_of_pos_right hlog2).2 hmono
  have hqi : 0 < queryInfo (3 / 4 : ℝ) := clause17_queryInfo_pos (by norm_num) (by norm_num)
  unfold fanoCapacityBound
  rw [lt_div_iff₀ hqi]
  rw [clause17_fanoNumerator_two]
  have hq : queryInfo (3 / 4 : ℝ) = 1 - binEntropy (3 / 4 : ℝ) := rfl
  rw [hq]
  linarith

/-- Binary entropy is strictly increasing on the interval `[0, 1 / 2]`. -/
theorem clause17_binEntropy_mono_strict {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2) (hab : a < b) : binEntropy a < binEntropy b := by
  have hma : a ∈ Set.Icc (0 : ℝ) (2 : ℝ)⁻¹ := by
    refine ⟨ha0, ?_⟩
    rw [show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num]
    exact ha1
  have hmb : b ∈ Set.Icc (0 : ℝ) (2 : ℝ)⁻¹ := by
    refine ⟨hb0, ?_⟩
    rw [show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num]
    exact hb1
  have hmono := Real.binEntropy_strictMonoOn hma hmb hab
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [clause17_binEntropy_eq_mathlib, clause17_binEntropy_eq_mathlib]
  exact (div_lt_div_iff_of_pos_right hlog2).2 hmono

/-- Binary entropy at `9 / 10` is strictly less than binary entropy at `3 / 4`. -/
theorem clause17_binEntropy_nine_tenths_lt_three_quarters :
    binEntropy (9 / 10 : ℝ) < binEntropy (3 / 4 : ℝ) := by
  have hsym := clause17_binEntropy_symmetry (9 / 10 : ℝ)
  rw [hsym]
  have h1' : (1 - 9 / 10 : ℝ) = 1 / 10 := by norm_num
  rw [h1']
  have h2 := clause17_binEntropy_symmetry (3 / 4 : ℝ)
  rw [h2]
  have h3' : (1 - 3 / 4 : ℝ) = 1 / 4 := by norm_num
  rw [h3']
  exact clause17_binEntropy_mono_strict (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- Binary entropy at `1 / 2` exceeds binary entropy at `9 / 10`, exhibiting failure of
monotonicity beyond one half. -/
theorem clause17_delta_form_monotonicity_fails :
    binEntropy (1 / 2 : ℝ) > binEntropy (9 / 10 : ℝ) := by
  have h1 : binEntropy (1 / 4 : ℝ) < binEntropy (1 / 2 : ℝ) :=
    clause17_binEntropy_mono_strict (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  have h2 : binEntropy (3 / 4 : ℝ) = binEntropy (1 / 4 : ℝ) := by
    have hsym := clause17_binEntropy_symmetry (3 / 4 : ℝ)
    rw [hsym]
    norm_num
  linarith [h1, h2, clause17_binEntropy_nine_tenths_lt_three_quarters]

/-- The cost-one, success-`3 / 4` experiment contradicts using the two-cell capacity expression
at error parameter `9 / 10` as its cost lower bound. -/
theorem clause17_large_delta_form_is_refuted {truth : Bool} :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (oneComparison truth) = 1 ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (oneComparison truth) (fun x => x.1 = truth) = (3 / 4 : ℝ≥0∞) ∧
      1 < fanoCapacityBound 2 (3 / 4 : ℝ) (9 / 10 : ℝ) := by
  exact ⟨clause17_one_comparison_cost, clause17_one_comparison_success,
    clause17_capacity_at_delta_nine_tenths⟩

/-- A cyclic shift of normalized report weights remains normalized. -/
theorem cycProb_sum_one {k : ℕ} (p : Fin (k + 1) → ℝ) (hs : (∑ h, p h) = 1)
    (s : Fin (k + 1)) : (∑ h, cycProb p s h) = 1 := by
  unfold cycProb
  have hshift : (∑ h, p (h - s)) = ∑ h, p h := by
    have he := Fintype.sum_equiv (Equiv.subRight s) (fun h => p (h - s)) (fun h => p h)
      (fun h => rfl)
    exact he
  rw [hshift, hs]

/-- A cyclic shift of report weights preserves entropy. -/
theorem entH_cycProb {k : ℕ} (p : Fin (k + 1) → ℝ) (s : Fin (k + 1)) :
    entH (fun h => cycProb p s h) = entH p := by
  unfold entH xlog2 cycProb
  congr 1
  have he := Fintype.sum_equiv (Equiv.subRight s)
    (fun h => p (h - s) * (Real.log (p (h - s)) / Real.log 2))
    (fun h => p h * (Real.log (p h) / Real.log 2)) (fun h => rfl)
  exact he

/-- The cyclic information expression equals `log₂ (k + 1)` minus report entropy. -/
theorem multiInfo_eq_entH {k : ℕ} (p : Fin (k + 1) → ℝ) :
    multiInfo p = Real.log (k + 1) / Real.log 2 - entH p := by
  unfold multiInfo entH xlog2
  rw [Finset.sum_neg_distrib]

/-- Factors a cyclic transcript likelihood into its prefix likelihood and the final shifted
report weight. -/
theorem cycLikCuts_split {n m k : ℕ}
    (sig : ∀ i : Fin (m + 1), (Fin i.val → Fin (k + 1)) → Fin n → Fin (k + 1))
    (p : Fin (k + 1) → ℝ) (x : Fin n) (pfx : Fin m → Fin (k + 1)) (b : Fin (k + 1)) :
    cycLikCuts sig p x (tExt pfx b)
      = cycLikCuts (fun j => sig (j.castSucc)) p x pfx
        * cycProb p (sig (Fin.last m) pfx x) b := by
  unfold cycLikCuts
  rw [Fin.prod_univ_castSucc]
  have hpre : ∀ j : Fin m,
      cycProb p (sig (j.castSucc) (tRestrict (tExt pfx b) (j.castSucc)) x)
          ((tExt pfx b) (j.castSucc))
        = cycProb p (sig (j.castSucc) (tRestrict pfx j) x) (pfx j) := by
    intro j
    have h1 : tRestrict (tExt pfx b) (j.castSucc) = tRestrict pfx j :=
      tRestrict_tExt_castSucc pfx b j
    have h2 : (tExt pfx b) (j.castSucc) = pfx j := tExt_castSucc pfx b j
    rw [h1, h2]
  rw [Finset.prod_congr rfl (fun j _ => hpre j)]
  have hlast : cycProb p (sig (Fin.last m) (tRestrict (tExt pfx b) (Fin.last m)) x)
      ((tExt pfx b) (Fin.last m))
      = cycProb p (sig (Fin.last m) pfx x) b := by
    have h1 : tRestrict (tExt pfx b) (Fin.last m) = pfx := tRestrict_tExt_last pfx b
    have h2 : (tExt pfx b) (Fin.last m) = b := tLast_tExt pfx b
    rw [h1, h2]
  rw [hlast]

/-- Cyclic transcript likelihoods are nonnegative when the report weights are nonnegative. -/
theorem cycLikCuts_nonneg {n m k : ℕ}
    (sig : ∀ i : Fin m, (Fin i.val → Fin (k + 1)) → Fin n → Fin (k + 1))
    (p : Fin (k + 1) → ℝ) (hp : ∀ h, 0 ≤ p h) (x : Fin n) (y : Fin m → Fin (k + 1)) :
    0 ≤ cycLikCuts sig p x y := by
  unfold cycLikCuts cycProb
  exact Finset.prod_nonneg fun i _ => hp _

/-- Cyclic joint weights are nonnegative for nonnegative report weights and a nonempty
hidden-cell space. -/
theorem cycJointCuts_nonneg {n m k : ℕ}
    (sig : ∀ i : Fin m, (Fin i.val → Fin (k + 1)) → Fin n → Fin (k + 1))
    (p : Fin (k + 1) → ℝ) (hp : ∀ h, 0 ≤ p h) (hn : 0 < n) (x : Fin n)
    (y : Fin m → Fin (k + 1)) : 0 ≤ cycJointCuts sig p x y := by
  unfold cycJointCuts
  have h1 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  exact mul_nonneg h1 (cycLikCuts_nonneg sig p hp x y)

/-- For normalized report weights, cyclic transcript likelihoods sum to one for every hidden
cell. -/
theorem cycLikCuts_sum_one {n m k : ℕ}
    (sig : ∀ i : Fin m, (Fin i.val → Fin (k + 1)) → Fin n → Fin (k + 1))
    (p : Fin (k + 1) → ℝ) (hs : (∑ h, p h) = 1) (x : Fin n) :
    (∑ y : Fin m → Fin (k + 1), cycLikCuts sig p x y) = 1 := by
  induction m with
  | zero =>
      simp [cycLikCuts]
  | succ m ih =>
      have hsplit : (∑ y : Fin (m + 1) → Fin (k + 1), cycLikCuts sig p x y)
          = ∑ pfx : Fin m → Fin (k + 1), ∑ b, cycLikCuts sig p x (tExt pfx b) := by
        have h := Fintype.sum_tSplit (fun y _ => cycLikCuts sig p x y)
        simpa using! h
      rw [hsplit]
      have hstep : ∀ (pfx : Fin m → Fin (k + 1)) (b : Fin (k + 1)),
          cycLikCuts sig p x (tExt pfx b)
            = cycLikCuts (fun j => sig (j.castSucc)) p x pfx
              * cycProb p (sig (Fin.last m) pfx x) b := by
        intro pfx b
        exact cycLikCuts_split sig p x pfx b
      rw [Finset.sum_congr rfl (fun pfx _ => Finset.sum_congr rfl (fun b _ => hstep pfx b))]
      have hsum : ∀ (pfx : Fin m → Fin (k + 1)),
          (∑ b, cycLikCuts (fun j => sig (j.castSucc)) p x pfx
            * cycProb p (sig (Fin.last m) pfx x) b)
          = cycLikCuts (fun j => sig (j.castSucc)) p x pfx := by
        intro pfx
        have h1 : (∑ b, cycProb p (sig (Fin.last m) pfx x) b) = 1 :=
          cycProb_sum_one p hs (sig (Fin.last m) pfx x)
        have h2 := Finset.sum_mul (Finset.univ : Finset (Fin (k + 1)))
          (fun b : Fin (k + 1) => cycProb p (sig (Fin.last m) pfx x) b)
          (cycLikCuts (fun j => sig (j.castSucc)) p x pfx)
        rw [Finset.sum_congr rfl (fun b _ => mul_comm _ _)]
        rw [← h2, h1]
        simp
      rw [Finset.sum_congr rfl (fun pfx _ => hsum pfx)]
      exact ih (fun j => sig (j.castSucc))

/-- Cyclic joint weights sum to one for normalized report weights and `n > 0`. -/
theorem cycJointCuts_total {n m k : ℕ}
    (sig : ∀ i : Fin m, (Fin i.val → Fin (k + 1)) → Fin n → Fin (k + 1))
    (p : Fin (k + 1) → ℝ) (hs : (∑ h, p h) = 1) (hn : 0 < n) :
    (∑ x : Fin n, ∑ y : Fin m → Fin (k + 1), cycJointCuts sig p x y) = 1 := by
  have hkey : ∀ x : Fin n, (∑ y : Fin m → Fin (k + 1), cycJointCuts sig p x y)
      = 1 / (n : ℝ) := by
    intro x
    have h1 : (∑ y : Fin m → Fin (k + 1), cycLikCuts sig p x y) = 1 :=
      cycLikCuts_sum_one sig p hs x
    have h2 : (∑ y : Fin m → Fin (k + 1), cycJointCuts sig p x y)
        = (1 / (n : ℝ)) * (∑ y : Fin m → Fin (k + 1), cycLikCuts sig p x y) := by
      simp only [cycJointCuts]
      rw [sum_const_mul]
    rw [h2, h1]
    simp
  rw [Finset.sum_congr rfl (fun x _ => hkey x)]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_fin]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp

/-- The left marginal of the cyclic transcript joint law is the uniform weight `1 / n` when the
report weights sum to one. -/
theorem cycJointLaw_margL {n m k : ℕ}
    (sig : ∀ i : Fin m, (Fin i.val → Fin (k + 1)) → Fin n → Fin (k + 1))
    (p : Fin (k + 1) → ℝ) (hs : (∑ h, p h) = 1) (x : Fin n) :
    margL (cycJointLaw sig p) x = 1 / (n : ℝ) := by
  simp only [margL, cycJointLaw, cycJointCuts]
  have h1 : (∑ y : Fin m → Fin (k + 1), cycLikCuts sig p x y) = 1 :=
    cycLikCuts_sum_one sig p hs x
  rw [sum_const_mul, h1]
  simp

/-- Summing a cyclic joint weight over the final report recovers its prefix joint weight for
normalized report weights. -/
theorem cycJointCuts_prefix_marginal {n m k : ℕ}
    (sig : ∀ i : Fin (m + 1), (Fin i.val → Fin (k + 1)) → Fin n → Fin (k + 1))
    (p : Fin (k + 1) → ℝ) (hs : (∑ h, p h) = 1) (x : Fin n)
    (pfx : Fin m → Fin (k + 1)) :
    cycJointCuts (fun j => sig (j.castSucc)) p x pfx
      = ∑ b, cycJointCuts sig p x (tExt pfx b) := by
  have hsum : (∑ b, cycLikCuts sig p x (tExt pfx b))
      = cycLikCuts (fun j => sig (j.castSucc)) p x pfx := by
    have hstep : ∀ b : Fin (k + 1),
        cycLikCuts sig p x (tExt pfx b)
          = cycLikCuts (fun j => sig (j.castSucc)) p x pfx
            * cycProb p (sig (Fin.last m) pfx x) b := by
      intro b
      exact cycLikCuts_split sig p x pfx b
    rw [Finset.sum_congr rfl (fun b _ => hstep b)]
    have h1 : (∑ b, cycProb p (sig (Fin.last m) pfx x) b) = 1 :=
      cycProb_sum_one p hs (sig (Fin.last m) pfx x)
    rw [← Finset.mul_sum, h1]
    simp
  simp only [cycJointCuts]
  rw [sum_const_mul, hsum]

/-- Conditional entropy under normalized nonnegative joint weights is at most the base-two
logarithm of the nonempty right alphabet's cardinality. -/
theorem condEntH_le_log_card {α β : Type} [Fintype α] [Fintype β] (d : α × β → ℝ)
    (hd : ∀ i b, 0 ≤ d (i, b)) (htot : ∑ i, ∑ b, d (i, b) = 1)
    (hcard : 0 < Fintype.card β) :
    condEntH d ≤ Real.log (Fintype.card β : ℝ) / Real.log 2 := by
  have h := condEntH_eq_sum d hd
  rw [h]
  have hkey : ∀ i : α, margL d i * entH (fun b => condW d i b)
      ≤ margL d i * (Real.log (Fintype.card β : ℝ) / Real.log 2) := by
    intro i
    by_cases hm : margL d i = 0
    · have hcw : (fun b => condW d i b) = (fun _ => 0) := by
        funext b
        simp [condW, hm]
      have hent0 : entH (fun _ : β => 0) = 0 := by
        unfold entH xlog2
        simp
      rw [hcw, hent0]
      simp [hm]
    · have hsum1 : (∑ b : β, condW d i b) = 1 := condW_sum d hd i hm
      have hnonneg : ∀ b : β, 0 ≤ condW d i b := fun b => condW_nonneg d hd i b
      have hent : entH (fun b => condW d i b)
          ≤ Real.log (Fintype.card β : ℝ) / Real.log 2 :=
        entH_le_log_card (fun b => condW d i b) hnonneg hsum1 hcard
      have hnonneg' : 0 ≤ margL d i := Finset.sum_nonneg fun b _ => hd i b
      exact mul_le_mul_of_nonneg_left hent hnonneg'
  have h1 : (∑ i, margL d i * entH (fun b => condW d i b))
      ≤ ∑ i, margL d i * (Real.log (Fintype.card β : ℝ) / Real.log 2) :=
    Finset.sum_le_sum fun i _ => hkey i
  have hmass : (∑ i, margL d i) = 1 := by
    have h2 : (∑ i, ∑ b : β, d (i, b)) = ∑ i, margL d i := by
      simp only [margL]
    rw [← h2]
    exact htot
  calc (∑ i, margL d i * entH (fun b => condW d i b))
      ≤ ∑ i, margL d i * (Real.log (Fintype.card β : ℝ) / Real.log 2) := h1
    _ = (Real.log (Fintype.card β : ℝ) / Real.log 2) * (∑ i, margL d i) := by
        rw [Finset.mul_sum]
        rw [Finset.sum_congr rfl (fun i _ => mul_comm _ _)]
    _ = Real.log (Fintype.card β : ℝ) / Real.log 2 := by rw [hmass]; ring

/-- An empty cyclic transcript has zero mutual information for nonnegative normalized report
weights and `n > 0`. -/
theorem cycSigMutInfo_zero {n k : ℕ}
    (sig : ∀ i : Fin 0, (Fin i.val → Fin (k + 1)) → Fin n → Fin (k + 1))
    (p : Fin (k + 1) → ℝ) (hp : ∀ h, 0 ≤ p h) (hs : (∑ h, p h) = 1) (hn : 0 < n) :
    cycSigMutInfo sig p = 0 := by
  have hd : ∀ x y, 0 ≤ cycJointLaw sig p (x, y) := by
    intro x y
    exact cycJointCuts_nonneg sig p hp hn x y
  have hdval : ∀ x y, cycJointLaw sig p (x, y) = 1 / (n : ℝ) := by
    intro x y
    simp [cycJointLaw, cycJointCuts, cycLikCuts]
  have hmargR : ∀ y, margR (cycJointLaw sig p) y = 1 := by
    intro y
    simp only [margR]
    rw [Finset.sum_congr rfl (fun x _ => hdval x y)]
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_fin]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    field_simp
  have hent : entH (margR (cycJointLaw sig p)) = 0 := by
    unfold entH xlog2
    rw [Finset.sum_congr rfl (fun y _ => by rw [hmargR y])]
    simp
  have hmargL : ∀ x, margL (cycJointLaw sig p) x = 1 / (n : ℝ) :=
    cycJointLaw_margL sig p hs
  have hcW : ∀ x y, condW (cycJointLaw sig p) x y = 1 := by
    intro x y
    have hmul := condW_mul_margL (cycJointLaw sig p) hd x y
    rw [hmargL x, hdval x y] at hmul
    have hne : (1 / (n : ℝ)) ≠ 0 := by
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      positivity
    have hmul' : (1 / (n : ℝ)) * condW (cycJointLaw sig p) x y
        = (1 / (n : ℝ)) * 1 := by rw [hmul]; ring
    exact mul_left_cancel₀ hne hmul'
  have hcond : condEntH (cycJointLaw sig p) = 0 := by
    unfold condEntH
    rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by
      rw [hcW x y]))]
    simp
  have h := mutInfo_eq_margR (cycJointLaw sig p) hd
  unfold cycSigMutInfo
  rw [h, hent, hcond]
  simp

/-- Given the hidden cell and prefix, the final cyclic report has the entropy of the report
weights when they are nonnegative and normalized and `n > 0`. -/
theorem condEntH_cycJointPost {n m k : ℕ}
    (sig : ∀ i : Fin (m + 1), (Fin i.val → Fin (k + 1)) → Fin n → Fin (k + 1))
    (p : Fin (k + 1) → ℝ) (hp : ∀ h, 0 ≤ p h) (hs : (∑ h, p h) = 1) (hn : 0 < n) :
    condEntH (fun z : (Fin n × (Fin m → Fin (k + 1))) × Fin (k + 1) =>
      cycJointCuts sig p (z.1.1) (tExt z.1.2 z.2)) = entH p := by
  have hfac : ∀ (x : Fin n) (pfx : Fin m → Fin (k + 1)) (b : Fin (k + 1)),
      cycJointCuts sig p x (tExt pfx b)
        = cycJointCuts (fun j => sig (j.castSucc)) p x pfx
          * cycProb p (sig (Fin.last m) pfx x) b := by
    intro x pfx b
    unfold cycJointCuts
    rw [cycLikCuts_split sig p x pfx b]
    ring
  have hmarg : ∀ (x : Fin n) (pfx : Fin m → Fin (k + 1)),
      margL (fun z : (Fin n × (Fin m → Fin (k + 1))) × Fin (k + 1) =>
        cycJointCuts sig p (z.1.1) (tExt z.1.2 z.2)) (x, pfx)
        = cycJointCuts (fun j => sig (j.castSucc)) p x pfx := by
    intro x pfx
    simp only [margL]
    have helem : ∀ b : Fin (k + 1), cycJointCuts sig p x (tExt pfx b)
        = cycJointCuts (fun j => sig (j.castSucc)) p x pfx
          * cycProb p (sig (Fin.last m) pfx x) b :=
      hfac x pfx
    have hsum : (∑ b, cycJointCuts sig p x (tExt pfx b))
        = cycJointCuts (fun j => sig (j.castSucc)) p x pfx
          * (∑ b, cycProb p (sig (Fin.last m) pfx x) b) := by
      rw [Finset.sum_congr rfl (fun b _ => helem b)]
      rw [← Finset.mul_sum]
    have h1 : (∑ b, cycProb p (sig (Fin.last m) pfx x) b) = 1 :=
      cycProb_sum_one p hs (sig (Fin.last m) pfx x)
    rw [hsum, h1]
    simp
  have hcond : ∀ (x : Fin n) (pfx : Fin m → Fin (k + 1)) (b : Fin (k + 1)),
      cycJointCuts (fun j => sig (j.castSucc)) p x pfx ≠ 0 →
      condW (fun z : (Fin n × (Fin m → Fin (k + 1))) × Fin (k + 1) =>
        cycJointCuts sig p (z.1.1) (tExt z.1.2 z.2)) (x, pfx) b
        = cycProb p (sig (Fin.last m) pfx x) b := by
    intro x pfx b hne
    have hm : margL (fun z : (Fin n × (Fin m → Fin (k + 1))) × Fin (k + 1) =>
        cycJointCuts sig p (z.1.1) (tExt z.1.2 z.2)) (x, pfx) ≠ 0 := by
      rw [hmarg x pfx]
      exact hne
    simp only [condW, dif_neg hm]
    rw [hfac x pfx b, hmarg x pfx]
    field_simp
  have key : ∀ (x : Fin n) (pfx : Fin m → Fin (k + 1)),
      margL (fun z : (Fin n × (Fin m → Fin (k + 1))) × Fin (k + 1) =>
        cycJointCuts sig p (z.1.1) (tExt z.1.2 z.2)) (x, pfx)
          * entH (fun b => condW (fun z : (Fin n × (Fin m → Fin (k + 1))) × Fin (k + 1) =>
              cycJointCuts sig p (z.1.1) (tExt z.1.2 z.2)) (x, pfx) b)
        = margL (fun z : (Fin n × (Fin m → Fin (k + 1))) × Fin (k + 1) =>
            cycJointCuts sig p (z.1.1) (tExt z.1.2 z.2)) (x, pfx) * entH p := by
    intro x pfx
    by_cases hne : cycJointCuts (fun j => sig (j.castSucc)) p x pfx ≠ 0
    · have hfun : (fun b => condW (fun z : (Fin n × (Fin m → Fin (k + 1))) × Fin (k + 1) =>
            cycJointCuts sig p (z.1.1) (tExt z.1.2 z.2)) (x, pfx) b)
          = (fun b => cycProb p (sig (Fin.last m) pfx x) b) := by
        funext b
        exact hcond x pfx b hne
      have hent : entH (fun b => cycProb p (sig (Fin.last m) pfx x) b) = entH p := by
        exact entH_cycProb p (sig (Fin.last m) pfx x)
      rw [hfun, hent]
    · have hm0 : margL (fun z : (Fin n × (Fin m → Fin (k + 1))) × Fin (k + 1) =>
          cycJointCuts sig p (z.1.1) (tExt z.1.2 z.2)) (x, pfx) = 0 := by
        rw [hmarg x pfx]
        exact not_ne_iff.mp hne
      have hcw : (fun b => condW (fun z : (Fin n × (Fin m → Fin (k + 1))) × Fin (k + 1) =>
          cycJointCuts sig p (z.1.1) (tExt z.1.2 z.2)) (x, pfx) b) = (fun _ => 0) := by
        funext b
        simp [condW, hm0]
      have hent0 : entH (fun _ : Fin (k + 1) => 0) = 0 := by
        unfold entH xlog2
        simp
      rw [hcw, hent0]
      simp [hm0]

  have hmass : (∑ z : Fin n × (Fin m → Fin (k + 1)),
      margL (fun z' : (Fin n × (Fin m → Fin (k + 1))) × Fin (k + 1) =>
        cycJointCuts sig p (z'.1.1) (tExt z'.1.2 z'.2)) z) = 1 := by
    have helem : ∀ (x : Fin n) (pfx : Fin m → Fin (k + 1)),
        margL (fun z' : (Fin n × (Fin m → Fin (k + 1))) × Fin (k + 1) =>
          cycJointCuts sig p (z'.1.1) (tExt z'.1.2 z'.2)) (x, pfx)
          = cycJointCuts (fun j => sig (j.castSucc)) p x pfx := by
      intro x pfx
      exact hmarg x pfx
    rw [Finset.sum_congr rfl (fun z _ => helem z.1 z.2)]
    rw [Fintype.sum_prod_type]
    have hstep : ∀ (x : Fin n), (∑ pfx : Fin m → Fin (k + 1),
        cycJointCuts (fun j => sig (j.castSucc)) p x pfx) = 1 / (n : ℝ) := by
      intro x
      have helem' : ∀ pfx : Fin m → Fin (k + 1),
          cycJointCuts (fun j => sig (j.castSucc)) p x pfx
            = (1 / (n : ℝ)) * cycLikCuts (fun j => sig (j.castSucc)) p x pfx := by
        intro pfx
        rfl
      rw [Finset.sum_congr rfl (fun pfx _ => helem' pfx)]
      rw [← Finset.mul_sum]
      rw [cycLikCuts_sum_one (fun j => sig (j.castSucc)) p hs x]
      simp
    rw [Finset.sum_congr rfl (fun x _ => hstep x)]
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_fin]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    field_simp

  have h := condEntH_eq_sum (fun z : (Fin n × (Fin m → Fin (k + 1))) × Fin (k + 1) =>
      cycJointCuts sig p (z.1.1) (tExt z.1.2 z.2)) (fun z b =>
    cycJointCuts_nonneg sig p hp hn z.1 (tExt z.2 b))
  rw [h]
  have hkey : ∀ z : Fin n × (Fin m → Fin (k + 1)),
      margL (fun z' : (Fin n × (Fin m → Fin (k + 1))) × Fin (k + 1) =>
        cycJointCuts sig p (z'.1.1) (tExt z'.1.2 z'.2)) z
          * entH (fun b => condW (fun z' : (Fin n × (Fin m → Fin (k + 1))) × Fin (k + 1) =>
              cycJointCuts sig p (z'.1.1) (tExt z'.1.2 z'.2)) z b)
        = margL (fun z' : (Fin n × (Fin m → Fin (k + 1))) × Fin (k + 1) =>
            cycJointCuts sig p (z'.1.1) (tExt z'.1.2 z'.2)) z * entH p :=
    fun z => key z.1 z.2
  rw [Finset.sum_congr rfl (fun z _ => hkey z)]
  rw [Finset.sum_congr rfl (fun z _ => mul_comm _ _)]
  rw [← Finset.mul_sum]
  rw [hmass]
  ring

/-- For nonnegative normalized report weights and `n > 0`, splits cyclic transcript mutual
information into prefix information and the final-report conditional entropy gain. -/
theorem cycSigMutInfo_step {n m k : ℕ}
    (sig : ∀ i : Fin (m + 1), (Fin i.val → Fin (k + 1)) → Fin n → Fin (k + 1))
    (p : Fin (k + 1) → ℝ) (hp : ∀ h, 0 ≤ p h) (hs : (∑ h, p h) = 1) (hn : 0 < n) :
    cycSigMutInfo sig p
      = cycSigMutInfo (fun j => sig (j.castSucc)) p
        + condEntH (fun z : (Fin m → Fin (k + 1)) × Fin (k + 1) =>
            ∑ x, cycJointCuts sig p x (tExt z.1 z.2))
        - condEntH (fun z : (Fin n × (Fin m → Fin (k + 1))) × Fin (k + 1) =>
            cycJointCuts sig p (z.1.1) (tExt z.1.2 z.2)) := by
  have hd : ∀ x y, 0 ≤ cycJointLaw sig p (x, y) := by
    intro x y
    exact cycJointCuts_nonneg sig p hp hn x y
  have hdPre : ∀ x pfx, 0 ≤ cycJointLaw (fun j => sig (j.castSucc)) p (x, pfx) := by
    intro x pfx
    exact cycJointCuts_nonneg (fun j => sig (j.castSucc)) p hp hn x pfx
  have hPre : ∀ (x : Fin n) (pfx : Fin m → Fin (k + 1)),
      cycJointLaw (fun j => sig (j.castSucc)) p (x, pfx)
        = ∑ b, cycJointLaw sig p (x, tExt pfx b) := by
    intro x pfx
    exact cycJointCuts_prefix_marginal sig p hs x pfx
  have h := mutInfo_split (d := cycJointLaw sig p)
    (dPre := cycJointLaw (fun j => sig (j.castSucc)) p)
    (dM := fun z : (Fin m → Fin (k + 1)) × Fin (k + 1) =>
      ∑ x, cycJointCuts sig p x (tExt z.1 z.2))
    (dPost := fun z : (Fin n × (Fin m → Fin (k + 1))) × Fin (k + 1) =>
      cycJointCuts sig p (z.1.1) (tExt z.1.2 z.2))
    hd hdPre
    (fun pfx b => Finset.sum_nonneg fun x _ => hd x (tExt pfx b))
    (fun z b => by obtain ⟨x, pfx⟩ := z; exact hd x (tExt pfx b))
    hPre
    (fun pfx b => rfl)
    (fun x pfx b => rfl)
  exact h

/-- For nonnegative normalized report weights and `n > 0`, the information in `m` cyclic reports
is at most `m * multiInfo p`. -/
theorem cycSigMutInfo_le {n m k : ℕ}
    (sig : ∀ i : Fin m, (Fin i.val → Fin (k + 1)) → Fin n → Fin (k + 1))
    (p : Fin (k + 1) → ℝ) (hp : ∀ h, 0 ≤ p h) (hs : (∑ h, p h) = 1) (hn : 0 < n) :
    cycSigMutInfo sig p ≤ (m : ℝ) * multiInfo p := by
  induction m with
  | zero =>
      rw [cycSigMutInfo_zero sig p hp hs hn]
      simp [multiInfo]
  | succ m ih =>
      have hstep := cycSigMutInfo_step sig p hp hs hn
      have hpost : condEntH (fun z : (Fin n × (Fin m → Fin (k + 1))) × Fin (k + 1) =>
          cycJointCuts sig p (z.1.1) (tExt z.1.2 z.2)) = entH p :=
        condEntH_cycJointPost sig p hp hs hn
      have hMcard : condEntH (fun z : (Fin m → Fin (k + 1)) × Fin (k + 1) =>
          ∑ x, cycJointCuts sig p x (tExt z.1 z.2))
          ≤ Real.log ((Fintype.card (Fin (k + 1)) : ℕ) : ℝ) / Real.log 2 := by
        refine condEntH_le_log_card
          (d := fun z : (Fin m → Fin (k + 1)) × Fin (k + 1) =>
            ∑ x, cycJointCuts sig p x (tExt z.1 z.2)) ?_ ?_ ?_
        · intro pfx b
          exact Finset.sum_nonneg fun x _ =>
            cycJointCuts_nonneg sig p hp hn x (tExt pfx b)
        · have h2 : (∑ y : Fin (m + 1) → Fin (k + 1), ∑ x, cycJointCuts sig p x y)
                = ∑ pfx : Fin m → Fin (k + 1), ∑ b, ∑ x, cycJointCuts sig p x (tExt pfx b) := by
            have h := Fintype.sum_tSplit_gen (m := m)
              (fun y : Fin (m + 1) → Fin (k + 1) => ∑ x, cycJointCuts sig p x y)
            simpa using! h
          rw [← h2, Finset.sum_comm]
          exact cycJointCuts_total sig p hs hn
        · simp
      have hM : condEntH (fun z : (Fin m → Fin (k + 1)) × Fin (k + 1) =>
          ∑ x, cycJointCuts sig p x (tExt z.1 z.2))
          ≤ Real.log (k + 1 : ℝ) / Real.log 2 := by
        simpa [Fintype.card_fin] using! hMcard
      have hih : cycSigMutInfo (fun j => sig (j.castSucc)) p ≤ (m : ℝ) * multiInfo p :=
        ih (fun j => sig (j.castSucc))
      have h1 : cycSigMutInfo sig p
          ≤ cycSigMutInfo (fun j => sig (j.castSucc)) p
            + (Real.log (k + 1 : ℝ) / Real.log 2 - entH p) := by
        rw [hstep, hpost]
        linarith [hM]
      calc cycSigMutInfo sig p
          ≤ cycSigMutInfo (fun j => sig (j.castSucc)) p
              + (Real.log (k + 1 : ℝ) / Real.log 2 - entH p) := h1
        _ ≤ (m : ℝ) * multiInfo p + (Real.log (k + 1 : ℝ) / Real.log 2 - entH p) :=
          add_le_add_left hih _
        _ = ((m + 1 : ℕ) : ℝ) * multiInfo p := by
            rw [multiInfo_eq_entH]
            simp only [Nat.cast_succ]
            ring

/-- The cyclic program error probability is nonnegative for nonnegative report weights and `n >
0`. -/
theorem cycErrorProb_nonneg {n m k : ℕ} (prog : CycProgram n m k)
    (p : Fin (k + 1) → ℝ) (hp : ∀ h, 0 ≤ p h) (hn : 0 < n) : 0 ≤ cycErrorProb prog p := by
  have hkey : ∀ x y, 0 ≤ cycJointLaw prog.sig p (x, y)
      * (if cycError prog x y then 1 else 0) := by
    intro x y
    exact mul_nonneg (cycJointCuts_nonneg prog.sig p hp hn x y) (by split <;> norm_num)
  unfold cycErrorProb
  exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => hkey x y

/-- Expresses cyclic program error as the joint-law weighted indicator that the decoder differs
from the hidden cell. -/
theorem cycErrorProb_eq_fano_error {n m k : ℕ} (prog : CycProgram n m k)
    (p : Fin (k + 1) → ℝ) :
    cycErrorProb prog p
      = ∑ y : Fin m → Fin (k + 1), ∑ x : Fin n, cycJointLaw prog.sig p (x, y)
          * (if prog.guess y = x then 0 else 1) := by
  have herror : ∀ x y, (if cycError prog x y = true then (1 : ℝ) else 0)
      = (if prog.guess y = x then 0 else 1) := by
    intro x y
    unfold cycError
    by_cases h : prog.guess y = x
    · simp [h]
    · simp [h]
  have hcell : ∀ x y, cycJointLaw prog.sig p (x, y)
      * (if cycError prog x y = true then 1 else 0)
      = cycJointLaw prog.sig p (x, y) * (if prog.guess y = x then 0 else 1) := by
    intro x y
    congr 1
    exact herror x y
  unfold cycErrorProb
  calc (∑ x : Fin n, ∑ y : Fin m → Fin (k + 1),
        cycJointLaw prog.sig p (x, y) * (if cycError prog x y = true then 1 else 0))
      = ∑ y : Fin m → Fin (k + 1), ∑ x : Fin n,
        cycJointLaw prog.sig p (x, y) * (if cycError prog x y = true then 1 else 0) :=
      Finset.sum_comm
    _ = ∑ y : Fin m → Fin (k + 1), ∑ x : Fin n,
        cycJointLaw prog.sig p (x, y) * (if prog.guess y = x then 0 else 1) := by
          rw [Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun x _ => hcell x y))]
    _ = ∑ y : Fin m → Fin (k + 1), ∑ x : Fin n,
        cycJointLaw prog.sig p (x, y) * (if prog.guess y = x then 0 else 1) := rfl

/-- With nonnegative normalized report weights and positive `multiInfo p`, a cyclic program on
at least two hidden cells with actual error at most one half uses at least the corresponding
cyclic capacity bound in comparisons. -/
theorem cyc_same_run_comparison_lower_bound_actual {n m k : ℕ} (hn : 2 ≤ n)
    (prog : CycProgram n m k) (p : Fin (k + 1) → ℝ) (hp : ∀ h, 0 ≤ p h)
    (hs : (∑ h, p h) = 1) (hmi : 0 < multiInfo p)
    (hε1 : cycErrorProb prog p ≤ 1 / 2) :
    cycCapacityBound n k p (cycErrorProb prog p) ≤ (m : ℝ) := by
  have hn0 : 0 < n := by omega
  have hd : ∀ x y, 0 ≤ cycJointLaw prog.sig p (x, y) := by
    intro x y
    exact cycJointCuts_nonneg prog.sig p hp hn0 x y
  have ht : (∑ x : Fin n, ∑ y : Fin m → Fin (k + 1), cycJointLaw prog.sig p (x, y)) = 1 :=
    cycJointCuts_total prog.sig p hs hn0
  have hmarg : ∀ x, (∑ y : Fin m → Fin (k + 1), cycJointLaw prog.sig p (x, y))
      = 1 / (n : ℝ) := fun x => cycJointLaw_margL prog.sig p hs x
  have hε : cycErrorProb prog p
      = ∑ y : Fin m → Fin (k + 1), ∑ x : Fin n, cycJointLaw prog.sig p (x, y)
          * (if prog.guess y = x then 0 else 1) := cycErrorProb_eq_fano_error prog p
  have hε0 : 0 ≤ cycErrorProb prog p := cycErrorProb_nonneg prog p hp hn0
  have hfano := fano_capacity_arith hn (cycJointLaw prog.sig p) hd ht hmarg
    prog.guess (cycErrorProb prog p) hε hε0 hε1
  have hmi' : mutInfo (cycJointLaw prog.sig p) ≤ (m : ℝ) * multiInfo p :=
    cycSigMutInfo_le prog.sig p hp hs hn0
  have hnum : fanoNumerator n (cycErrorProb prog p) ≤ (m : ℝ) * multiInfo p := by
    unfold fanoNumerator
    linarith [hfano, hmi']
  unfold cycCapacityBound
  rw [div_le_iff₀ hmi]
  exact hnum

/-- With nonnegative normalized report weights and positive `multiInfo p`, a cyclic program on
at least two hidden cells with error at most `0 ≤ δ ≤ 1 / 2` uses at least `cycCapacityBound
n k p δ` comparisons. -/
theorem cyc_same_run_comparison_lower_bound {n m k : ℕ} (hn : 2 ≤ n)
    (prog : CycProgram n m k) (p : Fin (k + 1) → ℝ) (hp : ∀ h, 0 ≤ p h)
    (hs : (∑ h, p h) = 1) (hmi : 0 < multiInfo p)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) (herr : cycErrorProb prog p ≤ δ) :
    (m : ℝ) ≥ cycCapacityBound n k p δ := by
  have hn0 : 0 < n := by omega
  have hε1 : cycErrorProb prog p ≤ 1 / 2 := le_trans herr hδ1
  have hactual : cycCapacityBound n k p (cycErrorProb prog p) ≤ (m : ℝ) :=
    cyc_same_run_comparison_lower_bound_actual hn prog p hp hs hmi hε1
  have hbin : binEntropy (cycErrorProb prog p) ≤ binEntropy δ :=
    clause17_binEntropy_mono (cycErrorProb_nonneg prog p hp hn0) hε1 hδ0 hδ1 herr
  have hlogL : (0 : ℝ) ≤ Real.log ((n - 1 : ℕ) : ℝ) / Real.log 2 := by
    have h1 : (1 : ℕ) ≤ n - 1 := by omega
    have h2 : (0 : ℝ) ≤ Real.log ((n - 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast h1)
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    exact div_nonneg h2 (le_of_lt hlog2)
  have hmul : cycErrorProb prog p * (Real.log ((n - 1 : ℕ) : ℝ) / Real.log 2)
      ≤ δ * (Real.log ((n - 1 : ℕ) : ℝ) / Real.log 2) :=
    mul_le_mul_of_nonneg_right herr hlogL
  have hnum : fanoNumerator n δ ≤ (m : ℝ) * multiInfo p := by
    have h1 : fanoNumerator n δ ≤ fanoNumerator n (cycErrorProb prog p) := by
      unfold fanoNumerator
      linarith [hbin, hmul]
    have h2 : fanoNumerator n (cycErrorProb prog p) ≤ (m : ℝ) * multiInfo p := by
      have hnum' : fanoNumerator n (cycErrorProb prog p) ≤ (m : ℝ) * multiInfo p := by
        unfold cycCapacityBound at hactual
        rw [div_le_iff₀ hmi] at hactual
        exact hactual
      exact hnum'
    exact h1.trans h2
  have hfin : fanoNumerator n δ / multiInfo p ≤ (m : ℝ) := by
    rw [div_le_iff₀ hmi]
    exact hnum
  unfold cycCapacityBound
  exact hfin

/-- The entropy of the two weights `p` and `1 - p` equals `binEntropy p`. -/
theorem entH_bin_pair (p : ℝ) :
    entH (fun h : Fin 2 => if h.val = 0 then p else 1 - p) = binEntropy p := by
  unfold entH xlog2 binEntropy
  rw [Fin.sum_univ_two]
  simp

/-- The cyclic information expression for the two weights `p` and `1 - p` equals `queryInfo p`. -/
theorem multiInfo_bin_pair (p : ℝ) :
    multiInfo (fun h : Fin 2 => if h.val = 0 then p else 1 - p) = queryInfo p := by
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  rw [multiInfo_eq_entH, entH_bin_pair]
  unfold queryInfo
  field_simp
  ring_nf

/-- The entropy of uniform weights on `Fin (k + 1)` equals `log₂ (k + 1)`. -/
theorem entH_uniform {k : ℕ} :
    entH (fun _ : Fin (k + 1) => 1 / ((k + 1 : ℕ) : ℝ)) = Real.log (k + 1) / Real.log 2 := by
  unfold entH xlog2
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_fin]
  have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by
    rw [Nat.cast_add, Nat.cast_one]
  rw [hcast]
  have hn0 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hlog : Real.log (1 / ((k : ℝ) + 1)) = -Real.log ((k : ℝ) + 1) := by
    rw [one_div, Real.log_inv]
  rw [hlog]
  field_simp

/-- Uniform cyclic report weights have zero `multiInfo`. -/
theorem multiInfo_uniform_zero {k : ℕ} :
    multiInfo (fun _ : Fin (k + 1) => 1 / ((k + 1 : ℕ) : ℝ)) = 0 := by
  rw [multiInfo_eq_entH, entH_uniform]
  ring

/-- For at most one hidden cell, positive cyclic information, and `0 ≤ δ ≤ 1`, the cyclic
capacity expression is nonpositive. -/
theorem cyc_capacity_small_n {n k : ℕ} (hn : n ≤ 1) (p : Fin (k + 1) → ℝ) (δ : ℝ)
    (hmi : 0 < multiInfo p) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    cycCapacityBound n k p δ ≤ 0 := by
  have hlog1 : Real.log (n : ℝ) / Real.log 2 = 0 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · have hn1 : n = 1 := by omega
      subst hn1; simp
  have hlog0 : Real.log ((n - 1 : ℕ) : ℝ) / Real.log 2 = 0 := by
    have h : n - 1 = 0 := by omega
    simp [h]
  have hbin : 0 ≤ binEntropy δ := by
    rw [clause17_binEntropy_eq_mathlib]
    have h := Real.binEntropy_nonneg hδ0 hδ1
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    exact div_nonneg h (le_of_lt hlog2)
  unfold cycCapacityBound
  rw [div_le_iff₀ hmi]
  unfold fanoNumerator
  rw [hlog1, hlog0]
  linarith

/-- For a cyclic program with nonnegative normalized report weights, positive information, at
least two hidden cells, and error at most `0 ≤ δ ≤ 1 / 2`, establishes the query-information
and same-run contracts together with the cyclic capacity lower bound [BenOrHassidim2007]. -/
theorem clause17_multiway_contract {n m k : ℕ} (hn : 2 ≤ n)
    (prog : CycProgram n m k) (p : Fin (k + 1) → ℝ) (hp : ∀ h, 0 ≤ p h)
    (hs : (∑ h, p h) = 1) (hmi : 0 < multiInfo p) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1 / 2) (herr : cycErrorProb prog p ≤ δ) :
    CycQueryInfoBound prog p ∧
      CycSameRunBound prog p δ ∧
      (m : ℝ) ≥ cycCapacityBound n k p δ := by
  have hn0 : 0 < n := by omega
  refine ⟨?_, ?_, ?_⟩
  · exact cycSigMutInfo_le prog.sig p hp hs hn0
  · intro hδ hderr
    exact cyc_same_run_comparison_lower_bound hn prog p hp hs hmi hδ0 hδ1 hderr
  · exact cyc_same_run_comparison_lower_bound hn prog p hp hs hmi hδ0 hδ1 herr

/-- For `0 ≤ p ≤ 1`, the quantum step probability equals the binary symmetric channel
probability for the comparison truth bit. -/
theorem clause17_quantum_step_prob {n : ℕ} (rank : Fin n) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : Fin n) (b : Bool) :
    qStepProb rank p x b = bscProb p (truthBit rank x) b := by
  have hbool : boolIndex (answerBit (boolIndex b)) = boolIndex b := by
    rw [clause16_boolIndex_answerBit]
  have hamp : qStepState rank p x (boolIndex b)
      = (noiseAmplitude p (truthBit rank x) b : ℂ) := by
    unfold qStepState
    rw [hbool]
    exact clause16_backend_answer_amplitude rank p x b
  have hsq : noiseAmplitude p (truthBit rank x) b * noiseAmplitude p (truthBit rank x) b
      = noiseAnswerProb p (truthBit rank x) b := by
    unfold noiseAnswerProb
    ring
  unfold qStepProb bornProb
  rw [hamp, Complex.normSq_ofReal, hsq]
  unfold bscProb
  exact clause16_backend_bsc_law p hp0 hp1 (truthBit rank x) b

/-- Quantum step probabilities sum to one over Boolean answers when `0 ≤ p ≤ 1`. -/
theorem clause17_quantum_step_prob_sum {n : ℕ} (rank : Fin n) (p : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (x : Fin n) : ∑ b, qStepProb rank p x b = 1 := by
  rw [Fintype.sum_bool]
  have h1 : qStepProb rank p x true + qStepProb rank p x false = 1 := by
    rw [clause17_quantum_step_prob rank p hp0 hp1 x true,
      clause17_quantum_step_prob rank p hp0 hp1 x false]
    cases h : truthBit rank x <;> simp [bscProb]
  linarith

/-- For `0 ≤ p ≤ 1`, a `QuantumQueryProgram` has the same transcript likelihood as its
associated binary program. -/
theorem clause17_quantum_transcript_law {n q : ℕ} (prog : QuantumQueryProgram n q) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (rank : Fin n) (y : Fin q → Bool) :
    qLik prog p rank y = bscLik (toBscProg prog) p rank y := by
  unfold qLik bscLik
  apply Finset.prod_congr rfl
  intro i hi
  rw [clause17_quantum_step_prob rank p hp0 hp1 (prog.cuts i (answerPrefix y i)) (y i)]
  rfl

/-- For `0 ≤ p ≤ 1`, a `QuantumQueryProgram` has the same joint weights as its associated binary
program. -/
theorem clause17_quantum_joint_law {n q : ℕ} (prog : QuantumQueryProgram n q) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (rank : Fin n) (y : Fin q → Bool) :
    qJoint prog p rank y = bscJoint (toBscProg prog) p rank y := by
  unfold qJoint bscJoint
  rw [clause17_quantum_transcript_law prog p hp0 hp1 rank y]

/-- For `0 ≤ p ≤ 1`, a `QuantumQueryProgram` has the same error probability as its associated
binary program. -/
theorem clause17_quantum_error_prob {n q : ℕ} (prog : QuantumQueryProgram n q) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    qErrorProb prog p = bscErrorProb (toBscProg prog) p := by
  unfold qErrorProb bscErrorProb
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [clause17_quantum_joint_law prog p hp0 hp1 x y]
  rfl

/-- Establishes `QuantumQueryLowerBound` for the specified `QuantumQueryProgram` when `n ≥ 2`,
`1 / 2 < p ≤ 1`, and its error is at most `0 ≤ δ ≤ 1 / 2` [BenOrHassidim2007]. -/
theorem clause17_quantum_query_lower_bound {n q : ℕ} (hn : 2 ≤ n)
    (prog : QuantumQueryProgram n q) {p δ : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp : 1 / 2 < p)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) (herr : qErrorProb prog p ≤ δ) :
    QuantumQueryLowerBound n q p δ := by
  have herr' : bscErrorProb (toBscProg prog) p ≤ δ := by
    rw [← clause17_quantum_error_prob prog p hp0 hp1]
    exact herr
  have h := clause17_same_run_comparison_lower_bound hn (toBscProg prog) hp0 hp1 hp hδ0 hδ1 herr'
  exact h

/-- Under the stated backend and error hypotheses, gives the program's query lower bound,
preserves the backend proposition, and identifies its error with that of its associated
binary program. -/
theorem clause17_quantum_scope {n q : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : 1 / 2 < p) (hbackend : QuantumQueryBackend n p)
    (prog : QuantumQueryProgram n q) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2)
    (herr : qErrorProb prog p ≤ δ) :
    QuantumQueryLowerBound n q p δ ∧ QuantumQueryBackend n p ∧
      qErrorProb prog p = bscErrorProb (toBscProg prog) p := by
  refine ⟨clause17_quantum_query_lower_bound hn prog hp0 hp1 hp hδ0 hδ1 herr, hbackend, ?_⟩
  exact clause17_quantum_error_prob prog p hp0 hp1

/-- Establishes `QuantumQueryBackend` for every `0 ≤ p ≤ 1`. -/
theorem clause17_quantum_backend_holds {n : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    QuantumQueryBackend n p := by
  refine ⟨hp0, hp1, ?_, ?_, ?_⟩
  · intro rank
    exact clause16_noisy_query_oracle_is_unitary rank p hp0 hp1
  · intro rank x b
    exact clause17_quantum_step_prob rank p hp0 hp1 x b
  · intro rank x
    exact clause17_quantum_step_prob_sum rank p hp0 hp1 x

/-- Computes the legal noise rotation at `p = 16 / 25` and false truth bit, with diagonal
entries `4 / 5` and off-diagonal entries `-3 / 5` and `3 / 5`. -/
theorem clause17_legal_rotation_at_source_parameters :
    noiseRotation (16 / 25 : ℝ) false 0 0 = (4 / 5 : ℂ) ∧
      noiseRotation (16 / 25 : ℝ) false 0 1 = -(3 / 5 : ℂ) ∧
      noiseRotation (16 / 25 : ℝ) false 1 0 = (3 / 5 : ℂ) ∧
      noiseRotation (16 / 25 : ℝ) false 1 1 = (4 / 5 : ℂ) := by
  have h16 : Real.sqrt (16 / 25 : ℝ) = 4 / 5 := by
    rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
    norm_num
  have h9 : Real.sqrt (9 / 25 : ℝ) = 3 / 5 := by
    rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
    norm_num
  have h9' : Real.sqrt (1 - 16 / 25 : ℝ) = 3 / 5 := by
    rw [show (1 - 16 / 25 : ℝ) = 9 / 25 by norm_num, h9]
  constructor
  · simp [noiseRotation, h16]
  constructor
  · simp [noiseRotation, h9']
  constructor
  · simp [noiseRotation, h9']
  · simp [noiseRotation, h16]

/-- Computes the printed oracle entries as `4 / 5` on the diagonal and `3 / 5` off the diagonal. -/
theorem clause17_printed_oracle_at_source_parameters :
    printedOracle 0 0 = (4 / 5 : ℂ) ∧ printedOracle 0 1 = (3 / 5 : ℂ) ∧
      printedOracle 1 0 = (3 / 5 : ℂ) ∧ printedOracle 1 1 = (4 / 5 : ℂ) := by
  constructor
  · simp [printedOracle]
  constructor
  · simp [printedOracle]
  constructor
  · simp [printedOracle]
  · simp [printedOracle]

/-- The first column of the legal rotation at `p = 16 / 25` and false truth bit equals the first
column of the printed oracle. -/
theorem clause17_legal_rotation_agrees_with_printed_on_truth_state :
    (noiseRotation (16 / 25 : ℝ) false 0 0, noiseRotation (16 / 25 : ℝ) false 1 0)
      = (printedOracle 0 0, printedOracle 1 0) := by
  obtain ⟨h00, h01, h10, h11⟩ := clause17_legal_rotation_at_source_parameters
  obtain ⟨p00, p01, p10, p11⟩ := clause17_printed_oracle_at_source_parameters
  rw [h00, h10, p00, p10]

/-- Both the squared norm of the printed oracle's upper-left entry and the legal backend's
correct-answer probability equal `16 / 25`. -/
theorem clause17_source_reliability_is_preserved :
    Complex.normSq (printedOracle 0 0) = 16 / 25 ∧
      noiseAnswerProb (16 / 25 : ℝ) false false = 16 / 25 := by
  constructor
  · have h := clause17_printed_oracle_at_source_parameters.1
    rw [h]
    norm_num [Complex.normSq_apply]
  · rw [clause16_backend_bsc_law (16 / 25) (by norm_num) (by norm_num) false false]
    simp

/-- The printed oracle fails the unitary identity `U† U = 1`. -/
theorem clause17_printed_oracle_is_not_a_backend :
    printedOracle.conjTranspose * printedOracle ≠ 1 :=
  clause16_printed_oracle_is_not_unitary

/-- The stopping cost of every transcript is nonnegative. -/
theorem clause17_stop_cost_nonneg {n k : ℕ} (prog : BscStopProgram n k) (y : Fin k → Bool) :
    0 ≤ stopCost prog y := by
  unfold stopCost
  exact Nat.cast_nonneg _

/-- Binary transcript marginal weights are nonnegative for `0 ≤ p ≤ 1` and `n > 0`. -/
theorem clause17_transcript_marginal_nonneg {n k : ℕ} (prog : BscProgram n k) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n) (y : Fin k → Bool) :
    0 ≤ bscTransMarginal prog p y := by
  unfold bscTransMarginal
  exact Finset.sum_nonneg fun x _ => bscJoint_nonneg prog p hp0 hp1 hn x y

/-- Binary transcript marginal weights sum to one when `n > 0`. -/
theorem clause17_transcript_marginal_sum_one {n k : ℕ} (prog : BscProgram n k) (p : ℝ)
    (hn : 0 < n) :
    (∑ y, bscTransMarginal prog p y) = 1 := by
  have hkey : ∀ x : Fin n, ∀ y : Fin k → Bool,
      bscJoint prog p x y = bscJointLaw prog.cuts p (x, y) := by
    intro x y
    unfold bscJoint bscJointLaw bscJointCuts
    rw [bscLikPre_eq_bscLik]
  calc (∑ y, bscTransMarginal prog p y)
      = ∑ y, ∑ x, bscJoint prog p x y := by
          unfold bscTransMarginal
          rfl
    _ = ∑ x, ∑ y, bscJoint prog p x y := by
          rw [Finset.sum_comm]
    _ = ∑ x, ∑ y, bscJointLaw prog.cuts p (x, y) := by
          rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => hkey x y))]
    _ = 1 := bscJointLaw_total prog.cuts p hn

/-- For `0 ≤ p ≤ 1` and `n > 0`, the expected stopping cost is at most the transcript length
`k`. -/
theorem clause17_expected_cost_le_k {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n) :
    expectedStopCost prog p ≤ (k : ℝ) := by
  have hcost : ∀ y : Fin k → Bool, stopCost prog y ≤ (k : ℝ) := by
    intro y
    unfold stopCost
    have h1 : (prog.stop y).val ≤ k := by
      have h2 : (prog.stop y).val < k + 1 := (prog.stop y).isLt
      omega
    exact_mod_cast h1
  have hnonneg : ∀ y : Fin k → Bool, 0 ≤ bscTransMarginal (stopToBscProg prog) p y := by
    intro y
    exact clause17_transcript_marginal_nonneg (stopToBscProg prog) p hp0 hp1 hn y
  have hsum : (∑ y, bscTransMarginal (stopToBscProg prog) p y) = 1 :=
    clause17_transcript_marginal_sum_one (stopToBscProg prog) p hn
  unfold expectedStopCost
  calc (∑ y, bscTransMarginal (stopToBscProg prog) p y * stopCost prog y)
      ≤ ∑ y, bscTransMarginal (stopToBscProg prog) p y * (k : ℝ) := by
        exact Finset.sum_le_sum fun y _ =>
          mul_le_mul_of_nonneg_left (hcost y) (hnonneg y)
    _ = (k : ℝ) * (∑ y, bscTransMarginal (stopToBscProg prog) p y) := by
        calc (∑ y, bscTransMarginal (stopToBscProg prog) p y * (k : ℝ))
            = ∑ y, (k : ℝ) * bscTransMarginal (stopToBscProg prog) p y := by
              rw [Finset.sum_congr rfl (fun y _ => mul_comm _ _)]
          _ = (k : ℝ) * (∑ y, bscTransMarginal (stopToBscProg prog) p y) := by
            rw [Finset.mul_sum]
    _ = (k : ℝ) := by rw [hsum]; ring

/-- For `0 ≤ p ≤ 1`, `n > 0`, and `t > 0`, the stopping-cost tail probability is at most the
expected cost divided by `t`. -/
theorem clause17_expected_cost_tail_bound {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n) {t : ℝ} (ht : 0 < t) :
    stopTailProb prog p t ≤ expectedStopCost prog p / t := by
  have hnonneg : ∀ y : Fin k → Bool, 0 ≤ bscTransMarginal (stopToBscProg prog) p y := by
    intro y
    exact clause17_transcript_marginal_nonneg (stopToBscProg prog) p hp0 hp1 hn y
  have hcell : ∀ y : Fin k → Bool,
      bscTransMarginal (stopToBscProg prog) p y * t * stopCostTail prog t y
        ≤ bscTransMarginal (stopToBscProg prog) p y * stopCost prog y := by
    intro y
    by_cases h : stopCost prog y ≥ t
    · have h1 : stopCostTail prog t y = 1 := by simp [stopCostTail, h]
      have h2 : t ≤ stopCost prog y := h
      have h3 : 0 ≤ bscTransMarginal (stopToBscProg prog) p y := hnonneg y
      rw [h1]
      have h4 := mul_le_mul_of_nonneg_left h2 h3
      simpa using! h4
    · have h1 : stopCostTail prog t y = 0 := by simp [stopCostTail, h]
      have h3 : 0 ≤ bscTransMarginal (stopToBscProg prog) p y := hnonneg y
      rw [h1]
      have h4 : 0 ≤ stopCost prog y := clause17_stop_cost_nonneg prog y
      have h5 := mul_nonneg h3 h4
      linarith
  have hkey : t * stopTailProb prog p t ≤ expectedStopCost prog p := by
    unfold stopTailProb expectedStopCost
    calc t * (∑ y, bscTransMarginal (stopToBscProg prog) p y * stopCostTail prog t y)
        = ∑ y, t * (bscTransMarginal (stopToBscProg prog) p y * stopCostTail prog t y) := by
          rw [Finset.mul_sum]
      _ ≤ ∑ y, bscTransMarginal (stopToBscProg prog) p y * stopCost prog y := by
          exact Finset.sum_le_sum fun y _ => by
            simpa [mul_assoc, mul_left_comm, mul_comm] using! hcell y
  rw [le_div_iff₀ ht]
  linarith

/-- For positive expected stopping cost and `0 < b < c`, the tail at `(c / b)` times the
expectation is at most `b / c`, under valid binary channel parameters and `n > 0`. -/
theorem clause17_cost_tail_probability {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n) {b c : ℝ} (hb : 0 < b) (hc : b < c)
    (hE : 0 < expectedStopCost prog p) :
    stopTailProb prog p ((c / b) * expectedStopCost prog p) ≤ b / c := by
  have hc0 : 0 < c := lt_trans hb hc
  have ht : (0 : ℝ) < (c / b) * expectedStopCost prog p := mul_pos (div_pos hc0 hb) hE
  have hbound := clause17_expected_cost_tail_bound prog p hp0 hp1 hn ht
  have hdiv : expectedStopCost prog p / ((c / b) * expectedStopCost prog p) = b / c := by
    field_simp
  rw [hdiv] at hbound
  exact hbound

/-- If a stopping program always guesses the same cell and `n > 0`, its uniform-prior error
probability is `1 - 1 / n`. -/
theorem clause17_early_return_error_probability {n k : ℕ} (hn : 0 < n) (prog : BscStopProgram n k)
    (p : ℝ) (g : Fin n) (hguess : ∀ y : Fin k → Bool, prog.guess y = g) :
    stopErrorProb prog p = 1 - 1 / (n : ℝ) := by
  have hlik : ∀ x : Fin n, (∑ y : Fin k → Bool, bscLik (stopToBscProg prog) p x y) = 1 := by
    intro x
    have h1 := bscLikPre_sum_one (stopToBscProg prog).cuts p x
    simp only [bscLikPre_eq_bscLik] at h1
    exact h1
  have hcell : ∀ x : Fin n, ∀ y : Fin k → Bool,
      bscJoint (stopToBscProg prog) p x y * (if prog.guess y ≠ x then 1 else 0)
        = (1 / (n : ℝ)) * bscLik (stopToBscProg prog) p x y * (if g ≠ x then 1 else 0) := by
    intro x y
    have hg : prog.guess y = g := hguess y
    simp only [bscJoint, hg]
  have hfac : ∀ x : Fin n,
      (∑ y, (1 / (n : ℝ)) * bscLik (stopToBscProg prog) p x y * (if g ≠ x then 1 else 0))
        = (1 / (n : ℝ)) * (∑ y, bscLik (stopToBscProg prog) p x y) * (if g ≠ x then 1 else 0) := by
    intro x
    have h1 : (∑ y, (1 / (n : ℝ)) * bscLik (stopToBscProg prog) p x y
          * (if g ≠ x then 1 else 0))
        = (1 / (n : ℝ)) * (∑ y, bscLik (stopToBscProg prog) p x y
          * (if g ≠ x then 1 else 0)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          ring
    have h2 : (∑ y, bscLik (stopToBscProg prog) p x y * (if g ≠ x then 1 else 0))
        = (∑ y, bscLik (stopToBscProg prog) p x y) * (if g ≠ x then 1 else 0) := by
          rw [← Finset.sum_mul]
    rw [h1, h2]
    ring
  have hcount : (∑ x : Fin n, (if g ≠ x then (1 : ℝ) else 0)) = (n : ℝ) - 1 := by
    have hpoint : ∀ x : Fin n, (if g ≠ x then (1 : ℝ) else 0)
        = (1 : ℝ) - (if g = x then (1 : ℝ) else 0) := by
      intro x
      by_cases h : g = x
      · simp [h]
      · simp [h]
    have h1 : (∑ x : Fin n, (if g ≠ x then (1 : ℝ) else 0))
        = (∑ x : Fin n, (1 : ℝ)) - ∑ x : Fin n, (if g = x then (1 : ℝ) else 0) := by
      rw [Finset.sum_congr rfl (fun x _ => hpoint x), Finset.sum_sub_distrib]
    rw [h1]
    simp [Finset.sum_ite_eq' (s := (Finset.univ : Finset (Fin n))) (b := g)
      (f := fun _ => (1 : ℝ)) (Finset.mem_univ g)]
  calc (∑ x, ∑ y, bscJoint (stopToBscProg prog) p x y * (if prog.guess y ≠ x then 1 else 0))
      = ∑ x, ∑ y, (1 / (n : ℝ)) * bscLik (stopToBscProg prog) p x y
          * (if g ≠ x then 1 else 0) := by
          rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => hcell x y))]
    _ = ∑ x, (1 / (n : ℝ)) * (∑ y, bscLik (stopToBscProg prog) p x y)
          * (if g ≠ x then 1 else 0) := by
          rw [Finset.sum_congr rfl (fun x _ => hfac x)]
    _ = ∑ x, (1 / (n : ℝ)) * 1 * (if g ≠ x then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [hlik x]
    _ = (1 / (n : ℝ)) * (∑ x, (if g ≠ x then (1 : ℝ) else 0)) := by
          calc (∑ x, (1 / (n : ℝ)) * 1 * (if g ≠ x then (1 : ℝ) else 0))
              = ∑ x, (1 / (n : ℝ)) * (if g ≠ x then (1 : ℝ) else 0) := by
                apply Finset.sum_congr rfl
                intro x _
                ring
            _ = (1 / (n : ℝ)) * (∑ x, (if g ≠ x then (1 : ℝ) else 0)) := by
              rw [Finset.mul_sum]
    _ = (1 / (n : ℝ)) * ((n : ℝ) - 1) := by rw [hcount]
    _ = 1 - 1 / (n : ℝ) := by field_simp

/-- A noiseless binary program on at least two cells with error at most `0 ≤ δ ≤ 1 / 2` uses at
least `fanoCapacityBound n 1 δ` comparisons [BenOrHassidim2007]. -/
theorem clause17_cor27_noiseless_expectation {n k : ℕ} (hn : 2 ≤ n)
    (prog : BscProgram n k) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2)
    (herr : bscErrorProb prog 1 ≤ δ) :
    (k : ℝ) ≥ fanoCapacityBound n 1 δ := by
  have h := clause17_same_run_comparison_lower_bound hn prog (by norm_num) (by norm_num)
    (by norm_num) hδ0 hδ1 herr
  exact h

/-- A noiseless binary program that guesses perfectly on at least two cells uses at least `log₂
n` comparisons [BenOrHassidim2007]. -/
theorem clause17_cor27_noiseless_perfect_guess {n k : ℕ} (hn : 2 ≤ n)
    (prog : BscProgram n k) (herr : bscErrorProb prog 1 = 0) :
    (k : ℝ) ≥ Real.log (n : ℝ) / Real.log 2 := by
  have h := clause17_cor27_noiseless_expectation (δ := 0) hn prog (by norm_num) (by norm_num)
    (by rw [herr])
  have hbin : binEntropy 0 = 0 := by
    unfold binEntropy
    simp
  have hnum : fanoNumerator n 0 = Real.log (n : ℝ) / Real.log 2 := by
    unfold fanoNumerator
    rw [hbin]
    ring
  have hqi : queryInfo 1 = 1 := clause17_queryInfo_one
  unfold fanoCapacityBound at h
  rw [hqi, hnum] at h
  simpa using! h

/-- The number of indices in `Fin n` strictly below `m` is `min m n`. -/
theorem clause17_fin_sum_count : ∀ (n m : ℕ), (∑ i : Fin n, (if m > i.val then 1 else 0)) = min m n := by
  intro n
  induction n with
  | zero =>
      intro m
      simp
  | succ n ih =>
      intro m
      have hsplit : (∑ i : Fin (n + 1), (if m > i.val then 1 else 0))
          = (if m > 0 then 1 else 0)
            + (∑ i : Fin n, (if m > (Fin.succ i).val then 1 else 0)) := by
        rw [Fin.sum_univ_succ]
        simp only [Fin.val_zero]
        rfl
      rw [hsplit]
      by_cases hm0 : m = 0
      · have hmz : m = 0 := by omega
        subst hmz
        simp
      · have hmpos : 0 < m := by omega
        have hfirst : (if m > 0 then 1 else 0) = 1 := by
          rw [if_pos (by omega)]
        rw [hfirst]
        have htail : (∑ i : Fin n, (if m > (Fin.succ i).val then 1 else 0))
            = ∑ i : Fin n, (if (m - 1) > i.val then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro i _
          have hsucc : (Fin.succ i).val = i.val + 1 := rfl
          rw [hsucc]
          by_cases h : m > i.val + 1
          · rw [if_pos h]
            rw [if_pos (by omega)]
          · rw [if_neg h]
            rw [if_neg (by omega)]
        rw [htail]
        have hih := ih (m - 1)
        rw [hih]
        simp only [Nat.min_def]
        split <;> split <;> omega

/-- If `m ≤ k`, the number of indices in `Fin (k + 1)` strictly below `m` is `m`. -/
theorem clause17_fin_sum_count_le {k : ℕ} (m : ℕ) (hm : m ≤ k) :
    (∑ i : Fin (k + 1), (if m > i.val then 1 else 0)) = m := by
  have h := clause17_fin_sum_count (k + 1) m
  rw [h]
  have hle : m ≤ k + 1 := by omega
  rw [Nat.min_eq_left hle]

/-- A transcript prefix is alive at time `i ≤ k` exactly when the transcript's stopping index is
greater than `i`. -/
theorem clause17_stop_alive_of_transcript {n k : ℕ} (prog : BscStopProgram n k) {i : ℕ}
    (hk : i ≤ k) (y : Fin k → Bool) :
    stopAlive prog i (stopPrefix i hk y) ↔ (prog.stop y).val > i := by
  unfold stopAlive
  have hprefix : ∀ (j : Fin i), stopPrefix i hk y j = y ⟨j.val, lt_of_lt_of_le j.isLt hk⟩ := by
    intro j
    rfl
  have hprefixeq : ∀ (j : Fin k) (hj : j.val < i),
      y j = stopExt i (stopPrefix i hk y) j := by
    intro j hj
    simp only [stopExt, dif_pos hj]
    rw [hprefix ⟨j.val, hj⟩]
  by_cases hm : (prog.stop y).val ≤ i
  · have hagree : ∀ j : Fin k, j.val < (prog.stop y).val →
        y j = stopExt i (stopPrefix i hk y) j := by
      intro j hj
      have hji : j.val < i := by omega
      exact hprefixeq j hji
    have hstop : prog.stop (stopExt i (stopPrefix i hk y)) = prog.stop y :=
      (prog.prefixDetermined y (stopExt i (stopPrefix i hk y)) hagree).symm
    constructor
    · intro hL
      rw [hstop] at hL
      omega
    · intro hR
      rw [hstop]
      omega
  · have hcontra : ¬ ((prog.stop (stopExt i (stopPrefix i hk y))).val ≤ i) := by
      intro hle
      have hagree2 : ∀ j : Fin k, j.val < (prog.stop (stopExt i (stopPrefix i hk y))).val →
          stopExt i (stopPrefix i hk y) j = y j := by
        intro j hj
        have hji : j.val < i := by omega
        exact (hprefixeq j hji).symm
      have hstop : prog.stop (stopExt i (stopPrefix i hk y)) = prog.stop y :=
        prog.prefixDetermined (stopExt i (stopPrefix i hk y)) y hagree2
      rw [hstop] at hle
      omega
    constructor
    · intro _
      omega
    · intro _
      omega

/-- Transcripts agreeing before time `i ≤ k` have equivalent alive-prefix predicates at time
`i`. -/
theorem clause17_stop_alive_of_prefix {n k : ℕ} (prog : BscStopProgram n k) {i : ℕ}
    (hk : i ≤ k) (y y' : Fin k → Bool)
    (hag : ∀ j : Fin k, j.val < i → y j = y' j) :
    stopAlive prog i (stopPrefix i hk y) ↔ stopAlive prog i (stopPrefix i hk y') := by
  unfold stopAlive
  have hpre : stopPrefix i hk y = stopPrefix i hk y' := by
    funext j
    have hj : j.val < i := j.isLt
    have hkey : (⟨j.val, lt_of_lt_of_le j.isLt hk⟩ : Fin k).val < i := by
      rw [Fin.val_mk]
      exact hj
    exact hag ⟨j.val, lt_of_lt_of_le j.isLt hk⟩ hkey
  rw [hpre]

/-- The expected stopping cost equals the sum of the stopping survival profile over `Fin (k +
1)`. -/
theorem clause17_expected_stop_cost_eq_survival {n k : ℕ} (prog : BscStopProgram n k)
    (p : ℝ) :
    expectedStopCost prog p = ∑ i : Fin (k + 1), stopSurvivalProfile prog p i := by
  have hstep : ∀ y : Fin k → Bool,
      ((∑ i : Fin (k + 1), (if (prog.stop y).val > i.val then 1 else 0)) : ℝ)
        = ((prog.stop y).val : ℝ) := by
    intro y
    have hle : (prog.stop y).val ≤ k := Nat.lt_succ_iff.mp (prog.stop y).isLt
    exact_mod_cast (clause17_fin_sum_count_le (k := k) (prog.stop y).val hle)
  unfold expectedStopCost stopSurvivalProfile
  have hmain : (∑ y : Fin k → Bool, bscTransMarginal (stopToBscProg prog) p y * stopCost prog y)
      = ∑ y : Fin k → Bool, bscTransMarginal (stopToBscProg prog) p y
          * ((∑ i : Fin (k + 1), (if (prog.stop y).val > i.val then 1 else 0)) : ℝ) := by
    apply Finset.sum_congr rfl
    intro y _
    congr 1
    exact (hstep y).symm
  rw [hmain]
  calc (∑ y : Fin k → Bool, bscTransMarginal (stopToBscProg prog) p y
        * ((∑ i : Fin (k + 1), (if (prog.stop y).val > i.val then 1 else 0)) : ℝ))
      = ∑ y : Fin k → Bool, ∑ i : Fin (k + 1),
          bscTransMarginal (stopToBscProg prog) p y * (if (prog.stop y).val > i.val then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro y _
        rw [Finset.mul_sum]
    _ = ∑ i : Fin (k + 1), ∑ y : Fin k → Bool,
          bscTransMarginal (stopToBscProg prog) p y * (if (prog.stop y).val > i.val then 1 else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ i : Fin (k + 1), stopAliveProb prog p i.val (Nat.lt_succ_iff.mp i.isLt) := by
        apply Finset.sum_congr rfl
        intro i _
        unfold stopAliveProb
        apply Finset.sum_congr rfl
        intro y _
        have hiff := clause17_stop_alive_of_transcript prog (Nat.lt_succ_iff.mp i.isLt) y
        by_cases h : stopAlive prog i.val (stopPrefix i.val (Nat.lt_succ_iff.mp i.isLt) y)
        · have h2 : (prog.stop y).val > i.val := hiff.mp h
          simp [h, h2]
        · have h2 : ¬ ((prog.stop y).val > i.val) := fun hh => h (hiff.mpr hh)
          simp [h, h2]

/-- Each stopping survival-profile value is nonnegative for `0 ≤ p ≤ 1` and `n > 0`. -/
theorem clause17_survival_profile_nonneg {n k : ℕ} (prog : BscStopProgram n k) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n) (i : Fin (k + 1)) :
    0 ≤ stopSurvivalProfile prog p i := by
  unfold stopSurvivalProfile stopAliveProb
  apply Finset.sum_nonneg
  intro y _
  apply mul_nonneg
  · exact clause17_transcript_marginal_nonneg (stopToBscProg prog) p hp0 hp1 hn y
  · split <;> norm_num

/-- Each stopping survival-profile value is at most one for `0 ≤ p ≤ 1` and `n > 0`. -/
theorem clause17_survival_profile_le_one {n k : ℕ} (prog : BscStopProgram n k) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n) (i : Fin (k + 1)) :
    stopSurvivalProfile prog p i ≤ 1 := by
  unfold stopSurvivalProfile stopAliveProb
  have hsum : (∑ y : Fin k → Bool, bscTransMarginal (stopToBscProg prog) p y) = 1 :=
    clause17_transcript_marginal_sum_one (stopToBscProg prog) p hn
  calc (∑ y : Fin k → Bool, bscTransMarginal (stopToBscProg prog) p y
        * (if stopAlive prog i.val (stopPrefix i.val (by omega) y) then 1 else 0))
      ≤ ∑ y : Fin k → Bool, bscTransMarginal (stopToBscProg prog) p y * 1 := by
        apply Finset.sum_le_sum
        intro y _
        have hnonneg : 0 ≤ bscTransMarginal (stopToBscProg prog) p y :=
          clause17_transcript_marginal_nonneg (stopToBscProg prog) p hp0 hp1 hn y
        by_cases h : stopAlive prog i.val (stopPrefix i.val (by omega) y)
        · simp [h]
        · simp [h, hnonneg]
    _ = 1 := by rw [← Finset.sum_mul, hsum]; simp

/-- Summing a weighted equality indicator over its target index evaluates the remaining factor
at the selected image. -/
theorem clause17_sum_ite_reindex {α β : Type} [Fintype α] [Fintype β] (f : α → ℝ) (g : α → β)
    (w : α → β → ℝ) :
    (∑ b : β, ∑ a : α, (f a * (if g a = b then 1 else 0)) * w a b) = ∑ a : α, f a * w a (g a) := by
  calc (∑ b : β, ∑ a : α, (f a * (if g a = b then 1 else 0)) * w a b)
      = ∑ a : α, ∑ b : β, (f a * (if g a = b then 1 else 0)) * w a b := Finset.sum_comm
    _ = ∑ a : α, f a * (∑ b : β, (if g a = b then 1 else 0) * w a b) := by
        apply Finset.sum_congr rfl
        intro a _
        have hper : (∑ b : β, (f a * (if g a = b then 1 else 0)) * w a b)
            = f a * (∑ b : β, (if g a = b then 1 else 0) * w a b) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          ring
        exact hper
    _ = ∑ a : α, f a * w a (g a) := by
        apply Finset.sum_congr rfl
        intro a _
        have h1 : (∑ b : β, (if g a = b then 1 else 0) * w a b) = w a (g a) := by
          have h2 : (∑ b : β, (if g a = b then 1 else 0) * w a b)
              = ∑ b : β, (if g a = b then w a b else 0) := by
            apply Finset.sum_congr rfl
            intro b _
            by_cases hb : g a = b
            · simp [hb]
            · simp [hb]
          rw [h2, Fintype.sum_ite_eq]
        rw [h1]

/-- Decoding a padded stopping transcript recovers every answer before its stopping index. -/
theorem clause17_stop_pad_decode_used {n k : ℕ} (prog : BscStopProgram n k) (y : Fin k → Bool)
    (j : Fin k) (hj : j.val < (prog.stop y).val) :
    stopPadDecode (stopPad prog y) j = y j := by
  simp only [stopPadDecode, stopPad, if_pos hj]

/-- Padding, decoding, and padding a stopping transcript again gives the same padded transcript. -/
theorem clause17_stop_pad_roundtrip {n k : ℕ} (prog : BscStopProgram n k) (y : Fin k → Bool) :
    stopPad prog (stopPadDecode (stopPad prog y)) = stopPad prog y := by
  have hstop : prog.stop (stopPadDecode (stopPad prog y)) = prog.stop y := by
    have hagree : ∀ j : Fin k, j.val < (prog.stop y).val →
        y j = stopPadDecode (stopPad prog y) j := by
      intro j hj
      rw [clause17_stop_pad_decode_used prog y j hj]
    exact (prog.prefixDetermined y (stopPadDecode (stopPad prog y)) hagree).symm
  funext i
  show (if i.val < (prog.stop (stopPadDecode (stopPad prog y))).val
      then Sum.inl ((stopPadDecode (stopPad prog y)) i) else Sum.inr ())
      = stopPad prog y i
  rw [hstop]
  show (if i.val < (prog.stop y).val
      then Sum.inl ((stopPadDecode (stopPad prog y)) i) else Sum.inr ())
      = (if i.val < (prog.stop y).val then Sum.inl (y i) else Sum.inr ())
  by_cases hi : i.val < (prog.stop y).val
  · rw [if_pos hi, if_pos hi]
    congr 1
    exact clause17_stop_pad_decode_used prog y i hi
  · rw [if_neg hi, if_neg hi]

/-- If the guess depends only on used answers, the used-transcript decoder agrees with the
original guess on padded transcripts. -/
theorem clause17_stop_used_guess_eq {n k : ℕ} (prog : BscStopProgram n k)
    (hguess : StopGuessFromUsed prog) (y : Fin k → Bool) :
    stopUsedGuess prog (stopPad prog y) = prog.guess y := by
  unfold stopUsedGuess
  have hrt : stopPad prog y = stopPad prog (stopPadDecode (stopPad prog y)) :=
    (clause17_stop_pad_roundtrip prog y).symm
  exact (hguess y (stopPadDecode (stopPad prog y)) hrt).symm

/-- For `0 ≤ p ≤ 1` and `n > 0`, the joint weights of the hidden cell and padded used transcript
sum to one. -/
theorem clause17_stop_used_joint_total {n k : ℕ} (prog : BscStopProgram n k) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n) :
    (∑ x : Fin n, ∑ e : Fin k → (Sum Bool Unit), stopUsedJoint prog p x e) = 1 := by
  calc (∑ x : Fin n, ∑ e : Fin k → (Sum Bool Unit), stopUsedJoint prog p x e)
      = ∑ x : Fin n, ∑ y : Fin k → Bool, bscJointCuts prog.cuts p x y := by
        apply Finset.sum_congr rfl
        intro x _
        unfold stopUsedJoint
        have h := clause17_sum_ite_reindex (f := bscJointCuts prog.cuts p x)
          (g := fun y => stopPad prog y) (w := fun _ _ => (1 : ℝ))
        simpa using! h
    _ = 1 := by
        have h := bscJointLaw_total prog.cuts p hn
        simpa only [bscJointLaw] using! h

/-- For `0 ≤ p ≤ 1` and `n > 0`, summing the used-transcript joint weights over transcripts
gives `1 / n` for each hidden cell. -/
theorem clause17_stop_used_joint_margL {n k : ℕ} (prog : BscStopProgram n k) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n) (x : Fin n) :
    (∑ e : Fin k → (Sum Bool Unit), stopUsedJoint prog p x e) = 1 / (n : ℝ) := by
  calc (∑ e : Fin k → (Sum Bool Unit), stopUsedJoint prog p x e)
      = ∑ y : Fin k → Bool, bscJointCuts prog.cuts p x y := by
        unfold stopUsedJoint
        have h := clause17_sum_ite_reindex (f := bscJointCuts prog.cuts p x)
          (g := fun y => stopPad prog y) (w := fun _ _ => (1 : ℝ))
        simpa using! h
    _ = 1 / (n : ℝ) := by
        unfold bscJointCuts
        rw [sum_const_mul]
        have h1 := bscLikPre_sum_one prog.cuts p x
        rw [h1]
        simp

/-- Used-transcript joint weights are nonnegative for `0 ≤ p ≤ 1` and `n > 0`. -/
theorem clause17_stop_used_joint_nonneg {n k : ℕ} (prog : BscStopProgram n k) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n) (x : Fin n) (e : Fin k → (Sum Bool Unit)) :
    0 ≤ stopUsedJoint prog p x e := by
  unfold stopUsedJoint
  apply Finset.sum_nonneg
  intro y _
  apply mul_nonneg
  · exact bscJointCuts_nonneg prog.cuts p hp0 hp1 hn x y
  · split <;> norm_num

/-- When the guess depends only on used answers, the stopping error equals the used-transcript
joint-law error of `stopUsedGuess`. -/
theorem clause17_stop_error_eq_used_error {n k : ℕ} (prog : BscStopProgram n k) {p : ℝ}
    (hguess : StopGuessFromUsed prog) :
    stopErrorProb prog p
      = ∑ e : Fin k → (Sum Bool Unit), ∑ x : Fin n,
          stopUsedJoint prog p x e * (if stopUsedGuess prog e = x then 0 else 1) := by
  have hkey : ∀ (x : Fin n) (y : Fin k → Bool),
      bscJointCuts prog.cuts p x y = bscJoint (stopToBscProg prog) p x y := by
    intro x y
    unfold bscJoint bscJointCuts
    have h1 := bscLikPre_eq_bscLik (stopToBscProg prog) p x y
    have h2 : bscLikPre prog.cuts p x y = bscLik (stopToBscProg prog) p x y := by
      simpa using! h1
    rw [h2]
  have hRHS : (∑ e : Fin k → (Sum Bool Unit), ∑ x : Fin n,
          stopUsedJoint prog p x e * (if stopUsedGuess prog e = x then 0 else 1))
      = stopErrorProb prog p := by
    calc (∑ e : Fin k → (Sum Bool Unit), ∑ x : Fin n,
          stopUsedJoint prog p x e * (if stopUsedGuess prog e = x then 0 else 1))
        = ∑ x : Fin n, ∑ e : Fin k → (Sum Bool Unit),
            stopUsedJoint prog p x e * (if stopUsedGuess prog e = x then 0 else 1) := by
          rw [Finset.sum_comm]
      _ = ∑ x : Fin n, ∑ e : Fin k → (Sum Bool Unit), ∑ y : Fin k → Bool,
            (bscJointCuts prog.cuts p x y * (if stopPad prog y = e then 1 else 0))
              * (if stopUsedGuess prog e = x then 0 else 1) := by
          apply Finset.sum_congr rfl
          intro e _
          apply Finset.sum_congr rfl
          intro x _
          unfold stopUsedJoint
          rw [Finset.sum_mul]
      _ = ∑ x : Fin n, ∑ e : Fin k → (Sum Bool Unit), ∑ y : Fin k → Bool,
            (bscJointCuts prog.cuts p x y * (if stopPad prog y = e then 1 else 0))
              * (if stopUsedGuess prog e = x then 0 else 1) := by
          rw [Finset.sum_comm]
      _ = ∑ x : Fin n, ∑ y : Fin k → Bool, bscJointCuts prog.cuts p x y
            * (if stopUsedGuess prog (stopPad prog y) = x then 0 else 1) := by
          apply Finset.sum_congr rfl
          intro x _
          have h := clause17_sum_ite_reindex (f := bscJointCuts prog.cuts p x)
            (g := fun y => stopPad prog y)
            (w := fun _ e => (if stopUsedGuess prog e = x then 0 else 1))
          simpa using! h
      _ = ∑ x : Fin n, ∑ y : Fin k → Bool, bscJointCuts prog.cuts p x y
            * (if prog.guess y = x then 0 else 1) := by
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro y _
          have hg := clause17_stop_used_guess_eq prog hguess y
          simp [hg]
      _ = stopErrorProb prog p := by
          unfold stopErrorProb
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro y _
          rw [hkey x y]
          by_cases h : prog.guess y = x <;> simp [h]
  exact hRHS.symm

/-- For at least two hidden cells and `0 ≤ p ≤ 1`, a stopping program whose guess uses only
observed answers and whose error is at most one half has used-transcript information at
least its actual-error Fano numerator. -/
theorem clause17_stop_used_fano_actual {n k : ℕ} (hn : 2 ≤ n) (prog : BscStopProgram n k)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hguess : StopGuessFromUsed prog)
    (herr1 : stopErrorProb prog p ≤ 1 / 2) :
    fanoNumerator n (stopErrorProb prog p) ≤ stopUsedMutInfo prog p := by
  have hn0 : 0 < n := by omega
  have hd : ∀ (x : Fin n) (e : Fin k → (Sum Bool Unit)), 0 ≤ stopUsedJointLaw prog p (x, e) := by
    intro x e
    exact clause17_stop_used_joint_nonneg prog hp0 hp1 hn0 x e
  have ht : (∑ x : Fin n, ∑ e : Fin k → (Sum Bool Unit), stopUsedJointLaw prog p (x, e)) = 1 := by
    simpa only [stopUsedJointLaw] using!
      (clause17_stop_used_joint_total prog hp0 hp1 hn0)
  have hmarg : ∀ x : Fin n,
      (∑ e : Fin k → (Sum Bool Unit), stopUsedJointLaw prog p (x, e)) = 1 / (n : ℝ) := by
    intro x
    simpa only [stopUsedJointLaw] using!
      (clause17_stop_used_joint_margL prog hp0 hp1 hn0 x)
  have hε : stopErrorProb prog p
      = ∑ e : Fin k → (Sum Bool Unit), ∑ x : Fin n,
          stopUsedJointLaw prog p (x, e) * (if stopUsedGuess prog e = x then 0 else 1) := by
    have h := clause17_stop_error_eq_used_error (p := p) prog hguess
    simpa only [stopUsedJointLaw] using! h
  have hε0 : 0 ≤ stopErrorProb prog p := by
    unfold stopErrorProb
    apply Finset.sum_nonneg
    intro x _
    apply Finset.sum_nonneg
    intro y _
    apply mul_nonneg
    · exact bscJointCuts_nonneg prog.cuts p hp0 hp1 hn0 x y
    · split <;> norm_num
  have hfano := fano_capacity_arith hn (stopUsedJointLaw prog p) hd ht hmarg
    (stopUsedGuess prog) (stopErrorProb prog p) hε hε0 herr1
  have hmi : stopUsedMutInfo prog p = mutInfo (stopUsedJointLaw prog p) := rfl
  unfold fanoNumerator at hfano ⊢
  rw [hmi]
  linarith

/-- For at least two hidden cells and `0 ≤ p ≤ 1`, a stopping program with a guess based on used
answers and error at most `0 ≤ δ ≤ 1 / 2` has used-transcript information at least
`fanoNumerator n δ`. -/
theorem clause17_stop_used_fano {n k : ℕ} (hn : 2 ≤ n) (prog : BscStopProgram n k)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hguess : StopGuessFromUsed prog)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) (herr : stopErrorProb prog p ≤ δ) :
    fanoNumerator n δ ≤ stopUsedMutInfo prog p := by
  have hn0 : 0 < n := by omega
  have hε1 : stopErrorProb prog p ≤ 1 / 2 := le_trans herr hδ1
  have hactual := clause17_stop_used_fano_actual hn prog hp0 hp1 hguess hε1
  have hε0 : 0 ≤ stopErrorProb prog p := by
    unfold stopErrorProb
    apply Finset.sum_nonneg
    intro x _
    apply Finset.sum_nonneg
    intro y _
    apply mul_nonneg
    · exact bscJointCuts_nonneg prog.cuts p hp0 hp1 hn0 x y
    · split <;> norm_num
  have hbin : binEntropy (stopErrorProb prog p) ≤ binEntropy δ :=
    clause17_binEntropy_mono hε0 hε1 hδ0 hδ1 herr
  have hactual' := hactual
  have hlogL : (0 : ℝ) ≤ Real.log ((n - 1 : ℕ) : ℝ) / Real.log 2 := by
    have h1 : (1 : ℕ) ≤ n - 1 := by omega
    have h2 : (0 : ℝ) ≤ Real.log ((n - 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast h1)
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    exact div_nonneg h2 (le_of_lt hlog2)
  have hmul : stopErrorProb prog p * (Real.log ((n - 1 : ℕ) : ℝ) / Real.log 2)
      ≤ δ * (Real.log ((n - 1 : ℕ) : ℝ) / Real.log 2) :=
    mul_le_mul_of_nonneg_right herr hlogL
  unfold fanoNumerator at hactual' ⊢
  linarith [hbin, hmul]

/-- The transcript prefix is independent of the proof that its length is bounded by the full
length. -/
theorem tPrefix_irrel {k i : ℕ} (h1 h2 : i ≤ k) {α : Type} (y : Fin k → α) :
    tPrefix i h1 y = tPrefix i h2 y := by
  funext j
  apply congrArg y
  apply Fin.ext
  rfl

/-- The prefix of an adaptive cut family is independent of the proof of the length bound. -/
theorem cutsPrefix_irrel {n k i : ℕ}
    (cuts : ∀ j : Fin k, (Fin j.val → Bool) → Fin n) (h1 h2 : i ≤ k) :
    cutsPrefix i cuts h1 = cutsPrefix i cuts h2 := by
  funext j
  funext c
  change cuts ⟨j.val, lt_of_lt_of_le j.isLt h1⟩ c
      = cuts ⟨j.val, lt_of_lt_of_le j.isLt h2⟩ c
  congr 1

/-- Taking a prefix no longer than the original transcript ignores an appended final value. -/
theorem tPrefix_tExt_prefix {k i : ℕ} (hk : i ≤ k + 1) (hki : i ≤ k) {α : Type}
    (pfx : Fin k → α) (b : α) :
    tPrefix i hk (tExt pfx b) = tPrefix i hki pfx := by
  funext j
  have hj : j.val < i := j.isLt
  have hne : (j.val : ℕ) ≠ k := by omega
  simp only [tPrefix]
  have hcast : (⟨j.val, lt_of_lt_of_le j.isLt hk⟩ : Fin (k + 1))
      = ⟨j.val, Nat.lt_succ_of_lt (lt_of_lt_of_le j.isLt hki)⟩ := by
    apply Fin.ext
    rfl
  rw [hcast]
  simp [tExt, hne]

/-- Taking a cut-family prefix commutes with first removing the last cut, provided the requested
prefix fits. -/
theorem cutsPrefix_pre {n k i : ℕ}
    (cuts : ∀ j : Fin (k + 1), (Fin j.val → Bool) → Fin n) (hki : i ≤ k) (hki1 : i ≤ k + 1) :
    cutsPrefix i (cutsPre cuts) hki = cutsPrefix i cuts hki1 := by
  funext j
  funext c
  change cuts ((⟨j.val, lt_of_lt_of_le j.isLt hki⟩ : Fin k).castSucc) c
      = cuts ⟨j.val, lt_of_lt_of_le j.isLt hki1⟩ c
  congr 1

/-- Taking the full-length prefix of an adaptive cut family returns the original family. -/
theorem cutsPrefix_full {n k : ℕ}
    (cuts : ∀ j : Fin k, (Fin j.val → Bool) → Fin n) (hk : k ≤ k) :
    cutsPrefix k cuts hk = cuts := by
  funext j
  funext c
  change cuts ⟨j.val, lt_of_lt_of_le j.isLt hk⟩ c = cuts j c
  congr 1

/-- Splits the weight sum over a fixed transcript prefix into shorter transcripts with that
prefix and their final values. -/
theorem sumOverPrefix_last_split {k' i : ℕ} {α : Type}
    [Fintype α] [DecidableEq α] (g : (Fin (k' + 1) → α) → ℝ) (w : Fin i → α)
    (hk : i ≤ k' + 1) (hki : i ≤ k') :
    sumOverPrefix g w hk
      = ∑ pfx : Fin k' → α,
          (if tPrefix i hki pfx = w then ∑ b, g (tExt pfx b) else 0) := by
  unfold sumOverPrefix
  have hsplit : (∑ y : Fin (k' + 1) → α, g y * (if tPrefix i hk y = w then 1 else 0))
      = ∑ pfx : Fin k' → α, ∑ b,
          (g (tExt pfx b) * (if tPrefix i hk (tExt pfx b) = w then 1 else 0)) := by
    have h := Fintype.sum_tSplit_gen (m := k')
      (G := fun y : Fin (k' + 1) → α => g y * (if tPrefix i hk y = w then 1 else 0))
    simpa using! h
  rw [hsplit]
  apply Finset.sum_congr rfl
  intro pfx _
  have hkey : ∀ b : α, tPrefix i hk (tExt pfx b) = tPrefix i hki pfx := by
    intro b
    exact tPrefix_tExt_prefix hk hki pfx b
  by_cases hc : tPrefix i hki pfx = w
  · have h1 : ∀ b : α,
        (g (tExt pfx b) * (if tPrefix i hk (tExt pfx b) = w then 1 else 0)) = g (tExt pfx b) := by
      intro b
      rw [hkey b, if_pos hc]
      simp
    rw [Finset.sum_congr rfl (fun b _ => h1 b)]
    simp [hc]
  · have h1 : ∀ b : α,
        (g (tExt pfx b) * (if tPrefix i hk (tExt pfx b) = w then 1 else 0)) = 0 := by
      intro b
      rw [hkey b, if_neg hc]
      simp
    rw [Finset.sum_congr rfl (fun b _ => h1 b)]
    simp [hc]

/-- Summing full binary transcript likelihoods over extensions of a fixed prefix gives that
prefix's likelihood under the restricted cuts. -/
theorem clause17_bsc_prefix_marginal {n : ℕ} (k : ℕ) :
    ∀ (i : ℕ) (hi : i ≤ k) (cuts : ∀ j : Fin k, (Fin j.val → Bool) → Fin n) (p : ℝ)
      (x : Fin n) (w : Fin i → Bool),
    sumOverPrefix (bscLikPre cuts p x) w hi = bscLikPre (cutsPrefix i cuts hi) p x w := by
  induction k with
  | zero =>
      intro i hi cuts p x w
      have hi0 : i = 0 := by omega
      subst hi0
      have hkey : ∀ y : Fin 0 → Bool, tPrefix 0 hi y = w := by
        intro y
        funext j
        exact Fin.elim0 j
      unfold sumOverPrefix
      simp [bscLikPre, hkey]
  | succ k ih =>
      intro i hi cuts p x w
      rcases Nat.eq_or_lt_of_le hi with h | h
      · subst h
        have hfull : ∀ y : Fin (k + 1) → Bool, tPrefix (k + 1) hi y = y := by
          intro y
          funext j
          apply congrArg y
          apply Fin.ext
          rfl
        have hLHS : sumOverPrefix (bscLikPre cuts p x) w hi = bscLikPre cuts p x w := by
          unfold sumOverPrefix
          have key : ∀ y : Fin (k + 1) → Bool,
              bscLikPre cuts p x y * (if tPrefix (k + 1) hi y = w then 1 else 0)
                = (if w = y then bscLikPre cuts p x y else 0) := by
            intro y
            by_cases hy : y = w
            · rw [hfull y]
              rw [if_pos hy, if_pos hy.symm]
              simp
            · rw [hfull y]
              rw [if_neg hy, if_neg (fun hc => hy hc.symm)]
              simp
          rw [Finset.sum_congr rfl (fun y _ => key y)]
          simpa only [eq_comm] using!
            (Fintype.sum_ite_eq (i := w) (f := bscLikPre cuts p x))
        have hRHS : bscLikPre (cutsPrefix (k + 1) cuts hi) p x w = bscLikPre cuts p x w := by
          rw [cutsPrefix_full cuts (hk := (by omega))]
        rw [hLHS, hRHS]
      · have hki : i ≤ k := by omega
        have hsplit : ∀ (pfx : Fin k → Bool) (b : Bool),
            bscLikPre cuts p x (tExt pfx b)
              = bscLikPre (cutsPre cuts) p x pfx * bscStepCond cuts p x pfx b := by
          intro pfx b
          have h := bscLikPre_split cuts p x pfx b
          simpa only [cutsPre] using! h
        have hsum : ∀ pfx : Fin k → Bool,
            (∑ b, bscLikPre cuts p x (tExt pfx b)) = bscLikPre (cutsPre cuts) p x pfx := by
          intro pfx
          rw [Finset.sum_congr rfl (fun b _ => hsplit pfx b)]
          have h3 : (∑ b, bscStepCond cuts p x pfx b) = 1 := by
            unfold bscStepCond
            exact bscProb_sum (truthBit x (cuts (Fin.last k) pfx))
          rw [← Finset.mul_sum, h3]
          simp
        have h1 : sumOverPrefix (bscLikPre cuts p x) w hi
            = ∑ pfx : Fin k → Bool,
                (if tPrefix i hki pfx = w then ∑ b, bscLikPre cuts p x (tExt pfx b) else 0) := by
          exact sumOverPrefix_last_split (bscLikPre cuts p x) w hi hki
        rw [h1]
        have h2 : ∀ pfx : Fin k → Bool,
            (if tPrefix i hki pfx = w then ∑ b, bscLikPre cuts p x (tExt pfx b) else 0)
              = bscLikPre (cutsPre cuts) p x pfx
                * (if tPrefix i hki pfx = w then 1 else 0) := by
          intro pfx
          by_cases hc : tPrefix i hki pfx = w
          · rw [if_pos hc, if_pos hc]
            rw [hsum pfx]
            simp
          · rw [if_neg hc, if_neg hc]
            simp
        rw [Finset.sum_congr rfl (fun pfx _ => h2 pfx)]
        rw [← cutsPrefix_pre cuts hki hi]
        have h3 := ih i hki (cutsPre cuts) p x w
        rw [← h3]
        rfl

/-- The likelihood mass of all binary transcripts extending a given prefix equals the likelihood
of that prefix. -/
theorem clause17_bsc_prefix_marginal' {n k i : ℕ}
    (cuts : ∀ j : Fin k, (Fin j.val → Bool) → Fin n) (p : ℝ) (x : Fin n)
    (w : Fin i → Bool) (hi : i ≤ k) :
    sumOverPrefix (bscLikPre cuts p x) w hi = bscLikPre (cutsPrefix i cuts hi) p x w :=
  clause17_bsc_prefix_marginal k i hi cuts p x w

/-- Summing binary joint weights over transcripts with a specified prefix gives the joint weight
under the prefix cut family. -/
theorem clause17_bsc_joint_prefix_marginal {n k i : ℕ}
    (cuts : ∀ j : Fin k, (Fin j.val → Bool) → Fin n) (p : ℝ) (x : Fin n)
    (w : Fin i → Bool) (hi : i ≤ k) :
    (∑ y : Fin k → Bool, bscJointCuts cuts p x y * (if tPrefix i hi y = w then 1 else 0))
      = bscJointCuts (cutsPrefix i cuts hi) p x w := by
  have hd : ∀ y : Fin k → Bool,
      bscJointCuts cuts p x y = (1 / (n : ℝ)) * bscLikPre cuts p x y := by
    intro y
    rfl
  have h := clause17_bsc_prefix_marginal k i hi cuts p x w
  unfold sumOverPrefix at h
  calc
    (∑ y : Fin k → Bool, bscJointCuts cuts p x y * (if tPrefix i hi y = w then 1 else 0))
        = (1 / (n : ℝ)) * ∑ y : Fin k → Bool,
            bscLikPre cuts p x y * (if tPrefix i hi y = w then 1 else 0) := by
          rw [Finset.sum_congr rfl (fun y _ => by rw [hd])]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          ring
    _ = (1 / (n : ℝ)) * bscLikPre (cutsPrefix i cuts hi) p x w := by rw [h]
    _ = bscJointCuts (cutsPrefix i cuts hi) p x w := by
      have hd' : bscJointCuts (cutsPrefix i cuts hi) p x w
          = (1 / (n : ℝ)) * bscLikPre (cutsPrefix i cuts hi) p x w := by rfl
      rw [hd']

/-- Whether the stopping index exceeds `i ≤ k` depends only on the answers before `i`. -/
theorem clause17_stop_gt_of_prefix {n k : ℕ} (prog : BscStopProgram n k) {i : ℕ} (hk : i ≤ k)
    (y y' : Fin k → Bool) (hag : ∀ j : Fin k, j.val < i → y j = y' j) :
    (prog.stop y).val > i ↔ (prog.stop y').val > i := by
  have h1 := clause17_stop_alive_of_transcript prog hk y
  have h2 := clause17_stop_alive_of_transcript prog hk y'
  have h3 := clause17_stop_alive_of_prefix prog hk y y' hag
  constructor
  · intro hM
    exact h2.mp (h3.mp (h1.mpr hM))
  · intro hM
    exact h1.mp (h3.mpr (h2.mpr hM))

/-- A padded transcript stores the original Boolean answer at index `j` exactly when `j`
precedes the stopping index. -/
theorem clause17_stop_pad_inl_iff {n k : ℕ} (prog : BscStopProgram n k) (y : Fin k → Bool)
    (j : Fin k) :
    stopPad prog y j = Sum.inl (y j) ↔ j.val < (prog.stop y).val := by
  simp [stopPad]

/-- A padded transcript stores the stop marker at index `j` exactly when the stopping index is
at most `j`. -/
theorem clause17_stop_pad_inr_iff {n k : ℕ} (prog : BscStopProgram n k) (y : Fin k → Bool)
    (j : Fin k) :
    stopPad prog y j = Sum.inr () ↔ (prog.stop y).val ≤ j.val := by
  simp [stopPad]

/-- A Boolean-valued entry in a padded transcript lies before the stopping index and equals the
original answer there. -/
theorem clause17_stop_pad_inl {n k : ℕ} (prog : BscStopProgram n k) (y : Fin k → Bool) (i : Fin k)
    (h : ∃ b : Bool, stopPad prog y i = Sum.inl b) :
    i.val < (prog.stop y).val ∧ stopPad prog y i = Sum.inl (y i) := by
  by_cases hlt : i.val < (prog.stop y).val
  · exact ⟨hlt, by simp [stopPad, hlt]⟩
  · obtain ⟨b, hb⟩ := h
    rw [show stopPad prog y i = Sum.inr () by simp [stopPad, hlt]] at hb
    exact absurd hb (by simp)

/-- Evaluates a transcript prefix by embedding its index into the full transcript. -/
theorem tPrefix_take {k i : ℕ} (hk : i ≤ k) {α : Type} (y : Fin k → α) (j : Fin i) :
    tPrefix i hk y j = y ⟨j.val, by omega⟩ := rfl

/-- A padded prefix of length `j` consists entirely of encoded Boolean answers exactly when `j`
is at most the stopping index. -/
theorem clause17_stop_pad_prefix_all_inl {n k : ℕ} (prog : BscStopProgram n k) {j : ℕ}
    (hj : j ≤ k) (y : Fin k → Bool) :
    (∀ i : Fin j, (tPrefix j hj (stopPad prog y)) i
        = Sum.inl (stopPadDecode (tPrefix j hj (stopPad prog y)) i))
      ↔ j ≤ (prog.stop y).val := by
  constructor
  · intro hall
    by_cases hj0 : j = 0
    · omega
    · have hinl : ∃ b : Bool, stopPad prog y ⟨j - 1, by omega⟩ = Sum.inl b := by
        have h := hall ⟨j - 1, by omega⟩
        rw [tPrefix_take hj] at h
        exact ⟨stopPadDecode (tPrefix j hj (stopPad prog y)) ⟨j - 1, by omega⟩, h⟩
      obtain ⟨hlt, heq⟩ := clause17_stop_pad_inl prog y ⟨j - 1, by omega⟩ hinl
      have hlt' : (j - 1 : ℕ) < (prog.stop y).val := hlt
      omega
  · intro hM
    intro i
    have hlt : i.val < (prog.stop y).val := by omega
    have h1 : stopPad prog y ⟨i.val, by omega⟩ = Sum.inl (y ⟨i.val, by omega⟩) :=
      (clause17_stop_pad_inl_iff prog y ⟨i.val, by omega⟩).mpr hlt
    have h2 : (tPrefix j hj (stopPad prog y)) i = stopPad prog y ⟨i.val, by omega⟩ :=
      tPrefix_take hj _ i
    have h3 : stopPadDecode (tPrefix j hj (stopPad prog y)) i = y ⟨i.val, by omega⟩ := by
      have h4 : stopPadDecode (tPrefix j hj (stopPad prog y)) i
          = stopPadDecode (stopPad prog y) ⟨i.val, by omega⟩ := by
        show stopPadDecode (stopPad prog y) ⟨i.val, by omega⟩
          = stopPadDecode (stopPad prog y) ⟨i.val, by omega⟩
        rfl
      rw [h4]
      show stopPadDecode (stopPad prog y) ⟨i.val, by omega⟩ = y ⟨i.val, by omega⟩
      simp [stopPadDecode, h1]
    rw [h2, h1, h3]

/-- Decoding a padded prefix containing only Boolean answers recovers the corresponding original
transcript entries. -/
theorem clause17_stop_pad_prefix_decode {n k : ℕ} (prog : BscStopProgram n k) {j : ℕ}
    (hj : j ≤ k) (y : Fin k → Bool)
    (hall : ∀ i : Fin j, (tPrefix j hj (stopPad prog y)) i
        = Sum.inl (stopPadDecode (tPrefix j hj (stopPad prog y)) i)) :
    ∀ i : Fin j, stopPadDecode (tPrefix j hj (stopPad prog y)) i = y ⟨i.val, by omega⟩ := by
  intro i
  have hinl : ∃ b : Bool, stopPad prog y ⟨i.val, by omega⟩ = Sum.inl b := by
    have h := hall i
    rw [tPrefix_take hj] at h
    exact ⟨stopPadDecode (tPrefix j hj (stopPad prog y)) i, h⟩
  obtain ⟨hlt, heq⟩ := clause17_stop_pad_inl prog y ⟨i.val, by omega⟩ hinl
  have h4 : stopPadDecode (tPrefix j hj (stopPad prog y)) i
      = stopPadDecode (stopPad prog y) ⟨i.val, by omega⟩ := by
    show stopPadDecode (stopPad prog y) ⟨i.val, by omega⟩
      = stopPadDecode (stopPad prog y) ⟨i.val, by omega⟩
    rfl
  rw [h4]
  show stopPadDecode (stopPad prog y) ⟨i.val, by omega⟩ = y ⟨i.val, by omega⟩
  simp [stopPadDecode, heq]

/-- Equal padded prefixes of length `j` determine the same truth value of whether the stopping
index exceeds `j`. -/
theorem clause17_stop_pad_alive_of_prefix {n k : ℕ} (prog : BscStopProgram n k) {j : ℕ}
    (hj : j ≤ k) (y y' : Fin k → Bool)
    (heq : tPrefix j hj (stopPad prog y) = tPrefix j hj (stopPad prog y')) :
    (prog.stop y).val > j ↔ (prog.stop y').val > j := by
  by_cases hall : ∀ i : Fin j, (tPrefix j hj (stopPad prog y)) i
      = Sum.inl (stopPadDecode (tPrefix j hj (stopPad prog y)) i)
  · have hall' : ∀ i : Fin j, (tPrefix j hj (stopPad prog y')) i
        = Sum.inl (stopPadDecode (tPrefix j hj (stopPad prog y')) i) := by
      intro i
      have h := hall i
      rw [heq] at h
      exact h
    have hdec := clause17_stop_pad_prefix_decode prog hj y hall
    have hdec' := clause17_stop_pad_prefix_decode prog hj y' hall'
    have hag : ∀ (i : Fin k), i.val < j → y i = y' i := by
      intro i hi
      have hMge : j ≤ (prog.stop y).val := (clause17_stop_pad_prefix_all_inl prog hj y).mp hall
      have hMge' : j ≤ (prog.stop y').val := (clause17_stop_pad_prefix_all_inl prog hj y').mp hall'
      have h1 : stopPad prog y ⟨i.val, by omega⟩ = Sum.inl (y ⟨i.val, by omega⟩) := by
        have hlt : i.val < (prog.stop y).val := by omega
        exact (clause17_stop_pad_inl_iff prog y ⟨i.val, by omega⟩).mpr hlt
      have h2 : stopPad prog y' ⟨i.val, by omega⟩ = Sum.inl (y' ⟨i.val, by omega⟩) := by
        have hlt : i.val < (prog.stop y').val := by omega
        exact (clause17_stop_pad_inl_iff prog y' ⟨i.val, by omega⟩).mpr hlt
      have h3 : stopPad prog y ⟨i.val, by omega⟩ = stopPad prog y' ⟨i.val, by omega⟩ := by
        have h4 : tPrefix j hj (stopPad prog y) ⟨i.val, by omega⟩
            = tPrefix j hj (stopPad prog y') ⟨i.val, by omega⟩ := by
          rw [heq]
        rw [tPrefix_take hj] at h4
        simp only [Fin.val_mk] at h4
        exact h4
      rw [h1, h2] at h3
      injection h3
    exact clause17_stop_gt_of_prefix prog hj y y' hag
  · have hMlt : (prog.stop y).val < j := by
      have hnot : ¬ (j ≤ (prog.stop y).val) := by
        intro hM
        exact hall ((clause17_stop_pad_prefix_all_inl prog hj y).mpr hM)
      omega
    have hinr : stopPad prog y ⟨(prog.stop y).val, by omega⟩ = Sum.inr () := by
      have hne : ¬ (((prog.stop y).val : ℕ) < (prog.stop y).val) := Nat.lt_irrefl _
      simp [stopPad, hne]
    have hinr' : stopPad prog y' ⟨(prog.stop y).val, by omega⟩ = Sum.inr () := by
      have heqi : tPrefix j hj (stopPad prog y) ⟨(prog.stop y).val, by omega⟩
          = tPrefix j hj (stopPad prog y') ⟨(prog.stop y).val, by omega⟩ := by
        rw [heq]
      rw [tPrefix_take hj] at heqi
      simp only [Fin.val_mk] at heqi
      rw [hinr] at heqi
      exact heqi.symm
    have hM' : (prog.stop y').val ≤ (prog.stop y).val :=
      (clause17_stop_pad_inr_iff prog y' ⟨(prog.stop y).val, by omega⟩).mp hinr'
    constructor <;> intro h <;> omega

/-- A padded transcript prefix contains the original answers before the stopping index and stop
markers thereafter. -/
theorem clause17_stop_pad_prefix_shape {n k : ℕ} (prog : BscStopProgram n k) {i : ℕ} (hi : i ≤ k)
    (y : Fin k → Bool) :
    tPrefix i hi (stopPad prog y)
      = fun j : Fin i => if j.val < (prog.stop y).val then Sum.inl (y ⟨j.val, by omega⟩)
        else Sum.inr () := by
  funext j
  have h1 : (⟨j.val, lt_of_lt_of_le j.isLt hi⟩ : Fin k) = ⟨j.val, by omega⟩ := by
    apply Fin.ext
    rfl
  simp only [tPrefix]
  rw [h1]
  simp [stopPad]

/-- A prefix of length `i + 1` is obtained by extending the length-`i` prefix with the next
transcript entry. -/
theorem clause17_tPrefix_snoc {k i : ℕ} (hk : i ≤ k) (hk1 : i + 1 ≤ k) {α : Type} (e : Fin k → α) :
    tPrefix (i + 1) hk1 e
      = tExt (tPrefix i hk e) (e ⟨i, Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hk1⟩) := by
  funext j
  by_cases hj : j.val = i
  · simp only [tPrefix, tExt, dif_pos hj]
    congr 1
    apply Fin.ext
    rw [hj]
  · simp only [tPrefix, tExt, dif_neg hj]

/-- Equal extended transcripts have equal prefixes and equal appended values. -/
theorem clause17_tExt_inj {m : ℕ} {α : Type} (a c : Fin m → α) (b d : α)
    (h : tExt a b = tExt c d) : a = c ∧ b = d := by
  constructor
  · funext j
    have hj : (⟨j.val, by omega⟩ : Fin (m + 1)).val ≠ m := by
      exact Nat.ne_of_lt j.isLt
    have h1 := congrFun h ⟨j.val, by omega⟩
    simp only [tExt, dif_neg hj] at h1
    exact h1
  · have h1 := congrFun h ⟨m, by omega⟩
    simp only [tExt] at h1
    exact h1

/-- A padded prefix containing only Boolean answers has length at most the stopping index, and
decoding it gives the original answer prefix. -/
theorem clause17_stop_allinl_shape {n k : ℕ} (prog : BscStopProgram n k) {i : ℕ} (hi : i ≤ k)
    (pfx : Fin i → (Sum Bool Unit)) (hall : padAllInl pfx) (y : Fin k → Bool)
    (heq : tPrefix i hi (stopPad prog y) = pfx) :
    i ≤ (prog.stop y).val ∧ tPrefix i hi y = stopPadDecode pfx := by
  have hshape : ∀ j : Fin i, (if j.val < (prog.stop y).val
      then Sum.inl (y ⟨j.val, by omega⟩) else Sum.inr ()) = pfx j := by
    intro j
    have h := congrFun ((clause17_stop_pad_prefix_shape prog hi y).symm) j
    rw [heq] at h
    exact h
  have hkey : ∀ j : Fin i, pfx j = Sum.inl (stopPadDecode pfx j) := by
    intro j
    obtain ⟨b, hb⟩ := hall j
    have h2 : stopPadDecode pfx j = b := by
      simp only [hb, stopPadDecode]
    rw [hb, h2]
  have hstop : i ≤ (prog.stop y).val := by
    by_cases hi0 : i = 0
    · omega
    · obtain ⟨b, hb⟩ := hall ⟨i - 1, by omega⟩
      have hj := hshape ⟨i - 1, by omega⟩
      rw [hkey ⟨i - 1, by omega⟩] at hj
      by_cases hlt : (i - 1 : ℕ) < (prog.stop y).val
      · simp only [if_pos hlt, Sum.inl.injEq] at hj
        omega
      · simp only [if_neg hlt] at hj
        simp at hj
  refine ⟨hstop, ?_⟩
  funext j
  have hj := hshape j
  rw [hkey j] at hj
  have hlt : j.val < (prog.stop y).val := by omega
  simp only [if_pos hlt, Sum.inl.injEq] at hj
  have e1 : tPrefix i hi y j = y ⟨j.val, by omega⟩ := rfl
  rw [e1]
  exact hj

/-- A padded transcript has a specified all-Boolean prefix exactly when it has not stopped
before that prefix ends and its original answer prefix equals the decoded prefix. -/
theorem clause17_stop_allinl_iff {n k : ℕ} (prog : BscStopProgram n k) {i : ℕ} (hi : i ≤ k)
    (pfx : Fin i → (Sum Bool Unit)) (hall : padAllInl pfx) (y : Fin k → Bool) :
    tPrefix i hi (stopPad prog y) = pfx
      ↔ (i ≤ (prog.stop y).val ∧ tPrefix i hi y = stopPadDecode pfx) := by
  constructor
  · intro h
    exact clause17_stop_allinl_shape prog hi pfx hall y h
  · intro h
    obtain ⟨hstop, hys⟩ := h
    have hkey : ∀ j : Fin i, pfx j = Sum.inl (stopPadDecode pfx j) := by
      intro j
      obtain ⟨b, hb⟩ := hall j
      have h2 : stopPadDecode pfx j = b := by
        simp only [hb, stopPadDecode]
      rw [hb, h2]
    funext j
    have hsh := congrFun (clause17_stop_pad_prefix_shape prog hi y) j
    have hlt : j.val < (prog.stop y).val := by omega
    rw [if_pos hlt] at hsh
    have h2 := congrFun hys j

    have e1 : tPrefix i hi y j = y ⟨j.val, by omega⟩ := rfl
    rw [e1] at h2
    rw [h2] at hsh
    rw [hsh, hkey j]

/-- Any transcript extending an alive answer prefix has stopping index strictly greater than the
prefix length. -/
theorem clause17_stop_gt_of_answer_prefix {n k : ℕ} (prog : BscStopProgram n k) {i : ℕ}
    (hi : i ≤ k) (w : Fin i → Bool) (y : Fin k → Bool) (hy : tPrefix i hi y = w)
    (halive : stopAlive prog i w) : (prog.stop y).val > i := by
  have h1 : stopPrefix i hi y = w := by
    have h2 : stopPrefix i hi y = tPrefix i hi y := by
      funext j
      apply congrArg y
      apply Fin.ext
      rfl
    rw [h2, hy]
  have h2 := clause17_stop_alive_of_transcript prog hi y
  rw [h1] at h2
  exact h2.mp halive

/-- Factors an extended binary joint weight into the prefix joint weight and the conditional
probability of the final answer. -/
theorem clause17_bsc_joint_split {n m : ℕ} (cuts : ∀ i : Fin (m + 1), (Fin i.val → Bool) → Fin n)
    (p : ℝ) (x : Fin n) (w : Fin m → Bool) (b : Bool) :
    bscJointCuts cuts p x (tExt w b)
      = bscJointCuts (fun j => cuts (j.castSucc)) p x w
        * bscProb p (truthBit x (cuts (Fin.last m) w)) b := by
  unfold bscJointCuts
  rw [bscLikPre_split cuts p x w b]
  simp only [bscStepCond]
  rw [mul_assoc]

/-- Removing the final cut from a cut prefix of length `i + 1` gives the cut prefix of length
`i`. -/
theorem clause17_cutsPrefix_pre {n k i : ℕ} (cuts : ∀ j : Fin k, (Fin j.val → Bool) → Fin n)
    (hi : i ≤ k) (hk1 : i + 1 ≤ k) :
    (fun j : Fin i => cutsPrefix (i + 1) cuts hk1 (j.castSucc)) = cutsPrefix i cuts hi := by
  funext j
  funext c
  change cuts ⟨j.val, by omega⟩ c = cuts ⟨j.val, by omega⟩ c
  rfl

/-- The last cut of a length-`i + 1` cut prefix equals the original cut at index `i`. -/
theorem clause17_cutsPrefix_last {n k i : ℕ} (cuts : ∀ j : Fin k, (Fin j.val → Bool) → Fin n)
    (hk1 : i + 1 ≤ k) (hik : i < k) (c : Fin i → Bool) :
    cutsPrefix (i + 1) cuts hk1 (Fin.last i) c = cuts ⟨i, hik⟩ c := by
  have h1 : (Fin.last i : Fin (i + 1)) = ⟨i, by omega⟩ := by
    apply Fin.ext
    rfl
  have h2 : cutsPrefix (i + 1) cuts hk1 (Fin.last i) c
      = cuts ⟨i, by omega⟩ c := by
    show cuts ⟨(Fin.last i : Fin (i + 1)).val, by omega⟩ c = cuts ⟨i, by omega⟩ c
    congr 1
  rw [h2]

/-- For an all-Boolean alive prefix, the used-prefix joint weight equals the binary joint weight
of its decoded answer prefix. -/
theorem clause17_stop_used_prefix_mass {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ) {i : ℕ} (hi : i ≤ k)
    (pfx : Fin i → (Sum Bool Unit)) (hall : padAllInl pfx)
    (halive : stopAlive prog i (stopPadDecode pfx)) (x : Fin n) :
    stopUsedPrefixLaw prog p i hi (x, pfx)
      = bscJointCuts (cutsPrefix i prog.cuts hi) p x (stopPadDecode pfx) := by
  unfold stopUsedPrefixLaw
  have hkey : ∀ y : Fin k → Bool,
      tPrefix i hi (stopPad prog y) = pfx ↔ tPrefix i hi y = stopPadDecode pfx := by
    intro y
    constructor
    · intro h
      obtain ⟨_, h2⟩ := (clause17_stop_allinl_iff prog hi pfx hall y).mp h
      exact h2
    · intro h
      have halt := clause17_stop_gt_of_answer_prefix prog hi (stopPadDecode pfx) y h halive
      exact (clause17_stop_allinl_iff prog hi pfx hall y).mpr ⟨by omega, h⟩
  calc (∑ y : Fin k → Bool, bscJointCuts prog.cuts p x y
        * (if tPrefix i hi (stopPad prog y) = pfx then 1 else 0))
      = ∑ y : Fin k → Bool, bscJointCuts prog.cuts p x y
        * (if tPrefix i hi y = stopPadDecode pfx then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro y _
          by_cases h1 : tPrefix i hi (stopPad prog y) = pfx
          · have h2 := (hkey y).mp h1
            simp [h1, h2]
          · have h2 : ¬ (tPrefix i hi y = stopPadDecode pfx) := fun hh => h1 ((hkey y).mpr hh)
            simp [h1, h2]
    _ = bscJointCuts (cutsPrefix i prog.cuts hi) p x (stopPadDecode pfx) :=
          clause17_bsc_joint_prefix_marginal prog.cuts p x (stopPadDecode pfx) hi

/-- After an alive padded prefix, appending a Boolean answer multiplies the used-prefix weight
by the binary channel probability at the next adaptive cut. -/
theorem clause17_stop_used_next_slot {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ) {i : ℕ} (hi : i ≤ k)
    (hk1 : i + 1 ≤ k) (hik : i < k) (pfx : Fin i → (Sum Bool Unit))
    (halive : padAlive prog pfx) (x : Fin n) (b : Bool) :
    stopUsedPrefixLaw prog p (i + 1) hk1 (x, tExt pfx (Sum.inl b))
      = stopUsedPrefixLaw prog p i hi (x, pfx)
        * bscProb p (truthBit x (prog.cuts ⟨i, hik⟩ (stopPadDecode pfx))) b := by
  obtain ⟨hall, halive'⟩ := halive
  unfold stopUsedPrefixLaw
  have hcond : ∀ y : Fin k → Bool,
      (tPrefix (i + 1) hk1 (stopPad prog y) = tExt pfx (Sum.inl b))
        ↔ (tPrefix (i + 1) hk1 y = tExt (stopPadDecode pfx) b) := by
    intro y
    have hsnocY : tPrefix (i + 1) hk1 y
        = tExt (tPrefix i hi y) (y ⟨i, hik⟩) := clause17_tPrefix_snoc hi hk1 y
    have hsnocP : tPrefix (i + 1) hk1 (stopPad prog y)
        = tExt (tPrefix i hi (stopPad prog y)) (stopPad prog y ⟨i, hik⟩) :=
      clause17_tPrefix_snoc hi hk1 (stopPad prog y)
    constructor
    · intro h
      have hinj := clause17_tExt_inj (tPrefix i hi (stopPad prog y)) pfx
        (stopPad prog y ⟨i, hik⟩) (Sum.inl b) (by rw [← hsnocP]; exact h)
      have hiff := clause17_stop_allinl_iff prog hi pfx hall y
      obtain ⟨hstop, hys⟩ := hiff.mp hinj.1
      have hpad : stopPad prog y ⟨i, hik⟩ = Sum.inl b := hinj.2
      obtain ⟨hlt, hpad'⟩ := clause17_stop_pad_inl prog y ⟨i, hik⟩ ⟨b, hpad⟩
      have hyi : y ⟨i, hik⟩ = b := by
        rw [hpad'] at hpad
        exact (Sum.inl.inj hpad)
      rw [hsnocY, hys, hyi]
    · intro h
      have hinj := clause17_tExt_inj (tPrefix i hi y) (stopPadDecode pfx) (y ⟨i, hik⟩) b
        (by rw [← hsnocY]; exact h)
      have hys : tPrefix i hi y = stopPadDecode pfx := hinj.1
      have hyi : y ⟨i, hik⟩ = b := hinj.2
      have halt := clause17_stop_gt_of_answer_prefix prog hi (stopPadDecode pfx) y hys halive'
      have hiff := clause17_stop_allinl_iff prog hi pfx hall y
      have henc := hiff.mpr ⟨by omega, hys⟩
      have hpad : stopPad prog y ⟨i, hik⟩ = Sum.inl (y ⟨i, hik⟩) :=
        (clause17_stop_pad_inl_iff prog y ⟨i, hik⟩).mpr halt
      rw [hsnocP, henc, hpad, hyi]
  have hmain : (∑ y : Fin k → Bool, bscJointCuts prog.cuts p x y
        * (if tPrefix (i + 1) hk1 (stopPad prog y) = tExt pfx (Sum.inl b) then 1 else 0))
      = ∑ y : Fin k → Bool, bscJointCuts prog.cuts p x y
        * (if tPrefix (i + 1) hk1 y = tExt (stopPadDecode pfx) b then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro y _
    by_cases h1 : tPrefix (i + 1) hk1 (stopPad prog y) = tExt pfx (Sum.inl b)
    · have h2 := (hcond y).mp h1
      simp [h1, h2]
    · have h2 : ¬ (tPrefix (i + 1) hk1 y = tExt (stopPadDecode pfx) b) :=
        fun hh => h1 ((hcond y).mpr hh)
      simp [h1, h2]
  rw [hmain]
  calc (∑ y : Fin k → Bool, bscJointCuts prog.cuts p x y
        * (if tPrefix (i + 1) hk1 y = tExt (stopPadDecode pfx) b then 1 else 0))
      = bscJointCuts (cutsPrefix (i + 1) prog.cuts hk1) p x (tExt (stopPadDecode pfx) b) :=
        clause17_bsc_joint_prefix_marginal prog.cuts p x (tExt (stopPadDecode pfx) b) hk1
    _ = bscJointCuts (cutsPrefix i prog.cuts hi) p x (stopPadDecode pfx)
        * bscProb p (truthBit x (prog.cuts ⟨i, hik⟩ (stopPadDecode pfx))) b := by
      have hsplit := clause17_bsc_joint_split (cuts := cutsPrefix (i + 1) prog.cuts hk1) p x
        (stopPadDecode pfx) b
      rw [clause17_cutsPrefix_pre prog.cuts hi hk1] at hsplit
      rw [clause17_cutsPrefix_last prog.cuts hk1 hik (stopPadDecode pfx)] at hsplit
      exact hsplit
    _ = stopUsedPrefixLaw prog p i hi (x, pfx)
        * bscProb p (truthBit x (prog.cuts ⟨i, hik⟩ (stopPadDecode pfx))) b := by
      rw [clause17_stop_used_prefix_mass prog p hi pfx hall halive' x]

/-- After a padded prefix that is not alive, extending it with a Boolean answer has zero
used-prefix weight. -/
theorem clause17_stop_used_next_slot_stopped {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ) {i : ℕ}
    (hi : i ≤ k) (hk1 : i + 1 ≤ k) (hik : i < k) (pfx : Fin i → (Sum Bool Unit))
    (hdead : ¬ padAlive prog pfx) (x : Fin n) (b : Bool) :
    stopUsedPrefixLaw prog p (i + 1) hk1 (x, tExt pfx (Sum.inl b)) = 0 := by
  unfold stopUsedPrefixLaw
  apply Finset.sum_eq_zero
  intro y _
  by_cases h1 : tPrefix (i + 1) hk1 (stopPad prog y) = tExt pfx (Sum.inl b)
  · have hsnocP : tPrefix (i + 1) hk1 (stopPad prog y)
        = tExt (tPrefix i hi (stopPad prog y)) (stopPad prog y ⟨i, hik⟩) :=
      clause17_tPrefix_snoc hi hk1 (stopPad prog y)
    have hinj := clause17_tExt_inj (tPrefix i hi (stopPad prog y)) pfx
      (stopPad prog y ⟨i, hik⟩) (Sum.inl b) (by rw [← hsnocP]; exact h1)
    have hpad : stopPad prog y ⟨i, hik⟩ = Sum.inl b := hinj.2
    obtain ⟨hlt0, hpad'⟩ := clause17_stop_pad_inl prog y ⟨i, hik⟩ ⟨b, hpad⟩
    have hlt : (i : ℕ) < (prog.stop y).val := hlt0
    have hall : padAllInl pfx := by
      intro j
      have hjlt : j.val < i := j.isLt
      have hsh := congrFun (clause17_stop_pad_prefix_shape prog hi y) j
      have hltj : j.val < (prog.stop y).val := lt_of_lt_of_le hjlt (le_of_lt hlt)
      rw [if_pos hltj] at hsh
      rw [hinj.1] at hsh
      exact ⟨y ⟨j.val, by omega⟩, hsh⟩
    have hiff := clause17_stop_allinl_iff prog hi pfx hall y
    obtain ⟨hstop, hys⟩ := hiff.mp hinj.1
    have h2 := clause17_stop_alive_of_transcript prog hi y
    have h2' : stopAlive prog i (stopPadDecode pfx) ↔ (prog.stop y).val > i := by
      have h3 : stopPrefix i hi y = stopPadDecode pfx := by
        have h4 : stopPrefix i hi y = tPrefix i hi y := by
          funext jj
          apply congrArg y
          apply Fin.ext
          rfl
        rw [h4, hys]
      rw [h3] at h2
      exact h2
    exact absurd ⟨hall, h2'.mpr hlt⟩ hdead
  · simp [h1]

/-- Summing indicators of all one-slot extensions of a prefix gives the indicator of the
original prefix. -/
theorem clause17_sum_ext {k i : ℕ} (hk : i ≤ k) (hk1 : i + 1 ≤ k)
    (e : Fin k → (Sum Bool Unit)) (pfx : Fin i → (Sum Bool Unit)) :
    (∑ b : Sum Bool Unit, if tPrefix (i + 1) hk1 e = tExt pfx b then (1 : ℝ) else 0)
      = (if tPrefix i hk e = pfx then (1 : ℝ) else 0) := by
  have hsnoc : tPrefix (i + 1) hk1 e = tExt (tPrefix i hk e) (e ⟨i, by omega⟩) :=
    clause17_tPrefix_snoc hk hk1 e
  by_cases h : tPrefix i hk e = pfx
  · have huniq : ∀ b : Sum Bool Unit,
        tPrefix (i + 1) hk1 e = tExt pfx b → b = e ⟨i, by omega⟩ := by
      intro b hb
      have hinj := clause17_tExt_inj (tPrefix i hk e) pfx (e ⟨i, by omega⟩) b (by
        rw [← hsnoc]; exact hb)
      exact hinj.2.symm
    have hcond : ∀ b : Sum Bool Unit,
        (tPrefix (i + 1) hk1 e = tExt pfx b) = (b = e ⟨i, by omega⟩) := by
      intro b
      apply propext
      constructor
      · intro hcon
        exact huniq b hcon
      · intro hcon
        subst hcon
        rw [hsnoc, h]
    have hsum : (∑ b : Sum Bool Unit,
          if tPrefix (i + 1) hk1 e = tExt pfx b then (1 : ℝ) else 0)
        = (if tPrefix (i + 1) hk1 e = tExt pfx (e ⟨i, by omega⟩) then (1 : ℝ) else 0) := by
      have hrew : (∑ b : Sum Bool Unit,
            if tPrefix (i + 1) hk1 e = tExt pfx b then (1 : ℝ) else 0)
          = ∑ b : Sum Bool Unit, if (b = e ⟨i, by omega⟩) then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro b _
        simp only [hcond b]
      rw [hrew]
      have heq : tPrefix (i + 1) hk1 e = tExt pfx (e ⟨i, by omega⟩) := by
        rw [hsnoc, h]
      simp [heq]
    rw [hsum]
    simp [hsnoc, h]
  · have hnone : ∀ b : Sum Bool Unit,
        ¬ (tPrefix (i + 1) hk1 e = tExt pfx b) := by
      intro b hcon
      have hinj := clause17_tExt_inj (tPrefix i hk e) pfx (e ⟨i, by omega⟩) b (by
        rw [← hsnoc]; exact hcon)
      exact h hinj.1
    have hsum : (∑ b : Sum Bool Unit,
          if tPrefix (i + 1) hk1 e = tExt pfx b then (1 : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      simp [hnone b]
    rw [hsum]
    simp [h]

/-- Summing the next used-prefix joint weight over Boolean answers and the stop marker recovers
the current prefix weight. -/
theorem clause17_stop_used_prefix_marg {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ) {i : ℕ}
    (hi : i ≤ k) (hk1 : i + 1 ≤ k) (x : Fin n) (pfx : Fin i → (Sum Bool Unit)) :
    stopUsedPrefixLaw prog p i hi (x, pfx)
      = ∑ b : Sum Bool Unit, stopUsedPrefixLaw prog p (i + 1) hk1 (x, tExt pfx b) := by
  unfold stopUsedPrefixLaw
  have hinner : ∀ y : Fin k → Bool,
      (∑ b : Sum Bool Unit,
          (if tPrefix (i + 1) hk1 (stopPad prog y) = tExt pfx b then (1 : ℝ) else 0))
        = (if tPrefix i hi (stopPad prog y) = pfx then (1 : ℝ) else 0) :=
    fun y => clause17_sum_ext hi hk1 (stopPad prog y) pfx
  calc (∑ y : Fin k → Bool, bscJointCuts prog.cuts p x y
        * (if tPrefix i hi (stopPad prog y) = pfx then 1 else 0))
      = ∑ y : Fin k → Bool, bscJointCuts prog.cuts p x y
        * (∑ b : Sum Bool Unit,
            (if tPrefix (i + 1) hk1 (stopPad prog y) = tExt pfx b then 1 else 0)) := by
          apply Finset.sum_congr rfl
          intro y _
          exact congrArg (fun z => bscJointCuts prog.cuts p x y * z) (hinner y).symm
    _ = ∑ y : Fin k → Bool, ∑ b : Sum Bool Unit, bscJointCuts prog.cuts p x y
        * (if tPrefix (i + 1) hk1 (stopPad prog y) = tExt pfx b then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro y _
          rw [Finset.mul_sum]
    _ = ∑ b : Sum Bool Unit, ∑ y : Fin k → Bool, bscJointCuts prog.cuts p x y
        * (if tPrefix (i + 1) hk1 (stopPad prog y) = tExt pfx b then 1 else 0) := by
          exact Finset.sum_comm
    _ = ∑ b : Sum Bool Unit, stopUsedPrefixLaw prog p (i + 1) hk1 (x, tExt pfx b) := by
          apply Finset.sum_congr rfl
          intro b _
          rfl

/-- Taking the full-length transcript prefix returns the original transcript. -/
theorem clause17_tPrefix_full {k : ℕ} (hk : k ≤ k) {α : Type} (y : Fin k → α) :
    tPrefix k hk y = y := by
  funext j
  apply congrArg y
  apply Fin.ext
  rfl

/-- Expands a sum over `Sum Bool Unit` into its false-answer, true-answer, and stop-marker
terms. -/
theorem clause17_sum_sum_bool_unit (f : Sum Bool Unit → ℝ) :
    (∑ b : Sum Bool Unit, f b)
      = f (Sum.inl false) + f (Sum.inl true) + f (Sum.inr ()) := by
  rw [Fintype.sum_sum_type]
  rw [Fintype.sum_bool]
  simp
  ring

/-- The empty used-prefix joint weight equals the uniform hidden-cell weight `1 / n`. -/
theorem clause17_stop_used_law_zero {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    (x : Fin n) (e : Fin 0 → (Sum Bool Unit)) :
    stopUsedPrefixLaw prog p 0 (Nat.zero_le k) (x, e) = 1 / (n : ℝ) := by
  unfold stopUsedPrefixLaw
  have hkey : ∀ y : Fin k → Bool, tPrefix 0 (Nat.zero_le k) (stopPad prog y) = e := by
    intro y
    funext j
    exfalso
    exact Fin.elim0 j
  calc (∑ y : Fin k → Bool, bscJointCuts prog.cuts p x y
        * (if tPrefix 0 (Nat.zero_le k) (stopPad prog y) = e then 1 else 0))
      = ∑ y : Fin k → Bool, bscJointCuts prog.cuts p x y := by
        apply Finset.sum_congr rfl
        intro y _
        rw [hkey y]
        simp
    _ = 1 / (n : ℝ) := by
        simpa only [bscJointLaw, margL] using! (bscJointLaw_margL prog.cuts p x)

/-- The full-length used-prefix law equals the used-transcript joint law. -/
theorem clause17_stop_used_law_full {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    (x : Fin n) (e : Fin k → (Sum Bool Unit)) :
    stopUsedPrefixLaw prog p k (Nat.le_refl k) (x, e) = stopUsedJointLaw prog p (x, e) := by
  unfold stopUsedPrefixLaw stopUsedJointLaw stopUsedJoint
  apply Finset.sum_congr rfl
  intro y _
  rw [clause17_tPrefix_full (Nat.le_refl k) (stopPad prog y)]

/-- After an alive padded prefix, extending it with a stop marker has zero used-prefix weight. -/
theorem clause17_stop_used_next_slot_marker {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    {i : ℕ} (hi : i ≤ k) (hk1 : i + 1 ≤ k) (hik : i < k)
    (pfx : Fin i → (Sum Bool Unit)) (halive : padAlive prog pfx) (x : Fin n) :
    stopUsedPrefixLaw prog p (i + 1) hk1 (x, tExt pfx (Sum.inr ())) = 0 := by
  unfold stopUsedPrefixLaw
  apply Finset.sum_eq_zero
  intro y _
  by_cases h1 : tPrefix (i + 1) hk1 (stopPad prog y) = tExt pfx (Sum.inr ())
  · have hsnoc : tPrefix (i + 1) hk1 (stopPad prog y)
        = tExt (tPrefix i hi (stopPad prog y)) (stopPad prog y ⟨i, hik⟩) :=
      clause17_tPrefix_snoc hi hk1 (stopPad prog y)
    have hinj := clause17_tExt_inj (tPrefix i hi (stopPad prog y)) pfx
      (stopPad prog y ⟨i, hik⟩) (Sum.inr ()) (by rw [← hsnoc]; exact h1)
    obtain ⟨hall, halive'⟩ := halive
    have hiff := clause17_stop_allinl_iff prog hi pfx hall y
    obtain ⟨hstop, hys⟩ := hiff.mp hinj.1
    have hsp : stopPrefix i hi y = stopPadDecode pfx := by
      have h2 : stopPrefix i hi y = tPrefix i hi y := by
        funext j
        apply congrArg y
        apply Fin.ext
        rfl
      rw [h2, hys]
    have hgt : (prog.stop y).val > i :=
      (clause17_stop_alive_of_transcript prog hi y).mp (by rw [hsp]; exact halive')
    have hpad : stopPad prog y ⟨i, hik⟩ = Sum.inl (y ⟨i, hik⟩) := by
      unfold stopPad
      rw [if_pos hgt]
    rw [hpad] at hinj
    exfalso
    exact Sum.inl_ne_inr hinj.2
  · simp [h1]

/-- After a padded prefix that is not alive, appending a stop marker preserves its used-prefix
weight. -/
theorem clause17_stop_used_next_slot_marker_dead {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    {i : ℕ} (hi : i ≤ k) (hk1 : i + 1 ≤ k) (hik : i < k)
    (pfx : Fin i → (Sum Bool Unit)) (hdead : ¬ padAlive prog pfx) (x : Fin n) :
    stopUsedPrefixLaw prog p (i + 1) hk1 (x, tExt pfx (Sum.inr ()))
      = stopUsedPrefixLaw prog p i hi (x, pfx) := by
  have h1 := clause17_stop_used_prefix_marg prog p hi hk1 x pfx
  have h2 := clause17_stop_used_next_slot_stopped prog p hi hk1 hik pfx hdead x (b := true)
  have h3 := clause17_stop_used_next_slot_stopped prog p hi hk1 hik pfx hdead x (b := false)
  calc stopUsedPrefixLaw prog p (i + 1) hk1 (x, tExt pfx (Sum.inr ()))
      = (∑ b : Sum Bool Unit, stopUsedPrefixLaw prog p (i + 1) hk1 (x, tExt pfx b))
          - stopUsedPrefixLaw prog p (i + 1) hk1 (x, tExt pfx (Sum.inl false))
          - stopUsedPrefixLaw prog p (i + 1) hk1 (x, tExt pfx (Sum.inl true)) := by
          rw [clause17_sum_sum_bool_unit]
          ring
      _ = stopUsedPrefixLaw prog p i hi (x, pfx) - 0 - 0 := by
          rw [h1]
          rw [clause17_sum_sum_bool_unit]
          rw [h2, h3]
      _ = stopUsedPrefixLaw prog p i hi (x, pfx) := by ring

/-- Any two functions on `Fin 0` are equal. -/
theorem clause17_fin_zero_subsingleton {α : Type} (a b : Fin 0 → α) : a = b := by
  funext j
  exact Fin.elim0 j

/-- Summing a constant over functions from `Fin 0` gives that constant. -/
theorem clause17_sum_fin_zero_const {α : Type} [Fintype α] (c : ℝ) :
    (∑ _e : Fin 0 → α, c) = c := by
  classical
  have h := Finset.sum_eq_single (Fin.elim0 : Fin 0 → α) (s := Finset.univ) (f := fun _ => c)
    (fun b _ hne => (hne (clause17_fin_zero_subsingleton b (Fin.elim0 : Fin 0 → α))).elim)
    (fun hm => absurd (Finset.mem_univ (Fin.elim0 : Fin 0 → α)) hm)
  exact h

/-- Weights taking only the values zero and one have entropy zero. -/
theorem entH_zero_one {α : Type} [Fintype α] (w : α → ℝ) (h : ∀ i, w i = 0 ∨ w i = 1) :
    entH w = 0 := by
  unfold entH
  have hx : ∀ i, xlog2 (w i) = 0 := by
    intro i
    rcases h i with h0 | h1
    · rw [h0]
      unfold xlog2
      simp
    · rw [h1]
      unfold xlog2
      simp
  rw [Finset.sum_eq_zero (fun i _ => hx i)]
  simp

/-- The empty used prefix has zero mutual information with the hidden cell when `n > 0`. -/
theorem clause17_stop_used_law_zero_mutInfo {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    (hn : 0 < n) :
    mutInfo (stopUsedPrefixLaw prog p 0 (Nat.zero_le k)) = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hlaw : ∀ (x : Fin n) (e : Fin 0 → (Sum Bool Unit)),
      stopUsedPrefixLaw prog p 0 (Nat.zero_le k) (x, e) = 1 / (n : ℝ) :=
    fun x e => clause17_stop_used_law_zero prog p x e
  have hd : ∀ (x : Fin n) (e : Fin 0 → (Sum Bool Unit)),
      0 ≤ stopUsedPrefixLaw prog p 0 (Nat.zero_le k) (x, e) := by
    intro x e
    rw [hlaw x e]
    positivity

  have hmargR : ∀ e : Fin 0 → (Sum Bool Unit),
      margR (stopUsedPrefixLaw prog p 0 (Nat.zero_le k)) e = 1 := by
    intro e
    simp only [margR]
    have h1 : (∑ x : Fin n, stopUsedPrefixLaw prog p 0 (Nat.zero_le k) (x, e))
        = ∑ _x : Fin n, (1 / (n : ℝ)) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [hlaw x e]
    rw [h1, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    field_simp

  have hcond : condEntH (stopUsedPrefixLaw prog p 0 (Nat.zero_le k)) = 0 := by
    rw [condEntH_eq_sum (stopUsedPrefixLaw prog p 0 (Nat.zero_le k)) hd]
    apply Finset.sum_eq_zero
    intro x _
    have hmass : margL (stopUsedPrefixLaw prog p 0 (Nat.zero_le k)) x = 1 / (n : ℝ) := by
      simp only [margL]
      calc (∑ e : Fin 0 → (Sum Bool Unit),
            stopUsedPrefixLaw prog p 0 (Nat.zero_le k) (x, e))
          = ∑ _e : Fin 0 → (Sum Bool Unit), (1 / (n : ℝ)) := by
            apply Finset.sum_congr rfl
            intro e _
            rw [hlaw x e]
        _ = 1 / (n : ℝ) :=
          clause17_sum_fin_zero_const (α := Sum Bool Unit) (1 / (n : ℝ))
    have hcw : ∀ e : Fin 0 → (Sum Bool Unit),
        condW (stopUsedPrefixLaw prog p 0 (Nat.zero_le k)) x e = 0 ∨
          condW (stopUsedPrefixLaw prog p 0 (Nat.zero_le k)) x e = 1 := by
      intro e
      by_cases hm : margL (stopUsedPrefixLaw prog p 0 (Nat.zero_le k)) x = 0
      · simp [condW, hm]
      · rw [condW, dif_neg hm, hmass, hlaw x e]
        exact Or.inr (by field_simp)
    rw [entH_zero_one (fun e => condW (stopUsedPrefixLaw prog p 0 (Nat.zero_le k)) x e) hcw]
    ring
  rw [mutInfo_eq_margR (stopUsedPrefixLaw prog p 0 (Nat.zero_le k)) hd]
  have hent : entH (margR (stopUsedPrefixLaw prog p 0 (Nat.zero_le k))) = 0 :=
    entH_zero_one (margR (stopUsedPrefixLaw prog p 0 (Nat.zero_le k)))
      (fun e => Or.inr (hmargR e))
  rw [hent, hcond]
  ring

/-- Used-prefix joint weights are nonnegative for `0 ≤ p ≤ 1` and `n > 0`. -/
theorem clause17_stop_used_prefix_law_nonneg {n k : ℕ} (prog : BscStopProgram n k) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n) {i : ℕ} (hi : i ≤ k)
    (x : Fin n) (e : Fin i → (Sum Bool Unit)) :
    0 ≤ stopUsedPrefixLaw prog p i hi (x, e) := by
  unfold stopUsedPrefixLaw
  apply Finset.sum_nonneg
  intro y _
  apply mul_nonneg
  · exact bscJointCuts_nonneg prog.cuts p hp0 hp1 hn x y
  · split <;> norm_num

/-- Expresses an in-range stopping-slot chain term as marginal conditional entropy minus
hidden-cell-conditioned entropy. -/
theorem stopSlotChainTerm_eq {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ) {i : ℕ}
    (hi : i + 1 ≤ k) :
    stopSlotChainTerm prog p i
      = condEntH (stopSlotMargLaw prog p hi) - condEntH (stopSlotPostLaw prog p hi) := by
  unfold stopSlotChainTerm
  rw [dif_pos hi]

/-- For `0 ≤ p ≤ 1` and `n > 0`, the mutual information in a used prefix equals the sum of its
stopping-slot chain terms. -/
theorem clause17_stop_used_chain {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n) :
    ∀ (i : ℕ) (hi : i ≤ k),
      mutInfo (stopUsedPrefixLaw prog p i hi)
        = ∑ x ∈ Finset.range i, stopSlotChainTerm prog p x := by
  intro i
  induction i with
  | zero =>
      intro hi
      rw [clause17_stop_used_law_zero_mutInfo prog p hn]
      simp [Finset.range_zero]
  | succ i ih =>
      intro hi
      have hi0 : i ≤ k := by omega
      have hsplit := mutInfo_split
        (d := stopUsedPrefixLaw prog p (i + 1) hi)
        (dPre := stopUsedPrefixLaw prog p i hi0)
        (dM := stopSlotMargLaw prog p hi)
        (dPost := stopSlotPostLaw prog p hi)
        (hd := fun x y => clause17_stop_used_prefix_law_nonneg prog hp0 hp1 hn hi x y)
        (hdPre := fun x pfx => clause17_stop_used_prefix_law_nonneg prog hp0 hp1 hn hi0 x pfx)
        (hdM := fun pfx b =>
          Finset.sum_nonneg fun x _ =>
            clause17_stop_used_prefix_law_nonneg prog hp0 hp1 hn hi x (tExt pfx b))
        (hdPost := fun z b =>
          clause17_stop_used_prefix_law_nonneg prog hp0 hp1 hn hi z.1 (tExt z.2 b))
        (hPre := fun x pfx => clause17_stop_used_prefix_marg prog p hi0 hi x pfx)
        (hM := fun pfx b => rfl)
        (hPost := fun x pfx b => rfl)
      calc mutInfo (stopUsedPrefixLaw prog p (i + 1) hi)
          = mutInfo (stopUsedPrefixLaw prog p i hi0)
            + (condEntH (stopSlotMargLaw prog p hi) - condEntH (stopSlotPostLaw prog p hi)) := by
            linarith [hsplit]
        _ = (∑ x ∈ Finset.range i, stopSlotChainTerm prog p x)
            + stopSlotChainTerm prog p i := by
            rw [ih hi0, ← stopSlotChainTerm_eq prog p hi]
        _ = ∑ x ∈ Finset.range (i + 1), stopSlotChainTerm prog p x := by
            rw [Finset.sum_range_succ]

/-- A bound `i + 1 ≤ k` implies `i ≤ k`. -/
theorem clause17_stop_prefix_le {i k : ℕ} (hi : i + 1 ≤ k) : i ≤ k :=
  Nat.le_trans (Nat.le_succ i) hi

/-- The left marginal of the stopping-slot marginal law is the used-prefix weight summed over
hidden cells. -/
theorem clause17_stop_slot_marg_total {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    {i : ℕ} (hi : i + 1 ≤ k) (pfx : Fin i → (Sum Bool Unit)) :
    margL (stopSlotMargLaw prog p hi) pfx
      = ∑ x, stopUsedPrefixLaw prog p i ((clause17_stop_prefix_le hi)) (x, pfx) := by
  simp only [margL, stopSlotMargLaw]
  calc (∑ b : Sum Bool Unit, ∑ x, stopUsedPrefixLaw prog p (i + 1) hi (x, tExt pfx b))
      = ∑ x, ∑ b : Sum Bool Unit, stopUsedPrefixLaw prog p (i + 1) hi (x, tExt pfx b) :=
        Finset.sum_comm
    _ = ∑ x, stopUsedPrefixLaw prog p i ((clause17_stop_prefix_le hi)) (x, pfx) := by
        apply Finset.sum_congr rfl
        intro x _
        exact (clause17_stop_used_prefix_marg prog p
          ((clause17_stop_prefix_le hi)) hi x pfx).symm

/-- The left marginal of the stopping-slot post law equals the joint weight of the hidden cell
and current used prefix. -/
theorem clause17_stop_slot_post_total {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    {i : ℕ} (hi : i + 1 ≤ k) (x : Fin n) (pfx : Fin i → (Sum Bool Unit)) :
    margL (stopSlotPostLaw prog p hi) (x, pfx)
      = stopUsedPrefixLaw prog p i ((clause17_stop_prefix_le hi)) (x, pfx) := by
  simp only [margL, stopSlotPostLaw]
  exact (clause17_stop_used_prefix_marg prog p
    ((clause17_stop_prefix_le hi)) hi x pfx).symm

/-- An alive padded prefix has zero stop-marker weight in the stopping-slot marginal law. -/
theorem clause17_stop_slot_marg_marker {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    {i : ℕ} (hi : i + 1 ≤ k) (hik : i < k) (pfx : Fin i → (Sum Bool Unit))
    (halive : padAlive prog pfx) :
    stopSlotMargLaw prog p hi (pfx, Sum.inr ()) = 0 := by
  unfold stopSlotMargLaw
  exact Finset.sum_eq_zero fun x _ =>
    clause17_stop_used_next_slot_marker prog p ((clause17_stop_prefix_le hi)) hi hik
      pfx halive x

/-- An alive padded prefix has zero stop-marker weight in the stopping-slot post law for every
hidden cell. -/
theorem clause17_stop_slot_post_marker {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    {i : ℕ} (hi : i + 1 ≤ k) (hik : i < k) (pfx : Fin i → (Sum Bool Unit))
    (halive : padAlive prog pfx) (x : Fin n) :
    stopSlotPostLaw prog p hi ((x, pfx), Sum.inr ()) = 0 :=
  clause17_stop_used_next_slot_marker prog p ((clause17_stop_prefix_le hi)) hi hik
    pfx halive x

/-- Adding a stop-marker entry of weight zero to Boolean weights preserves their entropy. -/
theorem entH_padded_eq (w : Sum Bool Unit → ℝ) (f : Bool → ℝ)
    (hz : w (Sum.inr ()) = 0) (hf : ∀ b, w (Sum.inl b) = f b) : entH w = entH f := by
  have hx : xlog2 (w (Sum.inr ())) = 0 := by
    rw [hz]
    unfold xlog2
    simp
  have h1 : ∀ b, xlog2 (w (Sum.inl b)) = xlog2 (f b) := by
    intro b
    rw [hf b]
  unfold entH
  rw [clause17_sum_sum_bool_unit (f := fun b => xlog2 (w b))]
  rw [Fintype.sum_bool (f := fun b : Bool => xlog2 (f b))]
  rw [hx]
  rw [h1 false, h1 true]
  ring

/-- For `0 ≤ p ≤ 1` and `n > 0`, the conditional next-slot entropy at an alive prefix is at most
one bit. -/
theorem clause17_stop_slot_marg_ent_le_one {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n)
    {i : ℕ} (hi : i + 1 ≤ k) (hik : i < k) (pfx : Fin i → (Sum Bool Unit))
    (halive : padAlive prog pfx) :
    entH (fun b => condW (stopSlotMargLaw prog p hi) pfx b) ≤ 1 := by
  have hdnonneg : ∀ a b, 0 ≤ stopSlotMargLaw prog p hi (a, b) := by
    intro a b
    unfold stopSlotMargLaw
    exact Finset.sum_nonneg fun x _ =>
      clause17_stop_used_prefix_law_nonneg prog hp0 hp1 hn hi x (tExt a b)
  have hz := clause17_stop_slot_marg_marker prog p hi hik pfx halive
  by_cases hm : margL (stopSlotMargLaw prog p hi) pfx = 0
  · have hcw : (fun b => condW (stopSlotMargLaw prog p hi) pfx b) = (fun _ => (0 : ℝ)) := by
      funext b
      simp [condW, hm]
    rw [hcw]
    have hent0 : entH (fun _ : Sum Bool Unit => (0 : ℝ)) = 0 := by
      unfold entH xlog2
      simp
    rw [hent0]
    norm_num
  · have hsum : (∑ b : Bool, condW (stopSlotMargLaw prog p hi) pfx (Sum.inl b)) = 1 := by
      have h := condW_sum (stopSlotMargLaw prog p hi) hdnonneg pfx hm
      rw [clause17_sum_sum_bool_unit] at h
      have hz' : condW (stopSlotMargLaw prog p hi) pfx (Sum.inr ()) = 0 := by
        rw [condW, dif_neg hm, hz]
        simp
      rw [hz'] at h
      rw [Fintype.sum_bool]
      linarith
    have hnonneg : ∀ b : Bool, 0 ≤ condW (stopSlotMargLaw prog p hi) pfx (Sum.inl b) :=
      fun b => condW_nonneg (stopSlotMargLaw prog p hi) hdnonneg pfx (Sum.inl b)
    have h1 := entH_le_log_card
      (fun b : Bool => condW (stopSlotMargLaw prog p hi) pfx (Sum.inl b)) hnonneg hsum
      (by norm_num : (0 : ℕ) < Fintype.card Bool)
    have hlog : Real.log (Fintype.card Bool : ℝ) / Real.log 2 = 1 := by
      simp [Fintype.card_bool]
      norm_num
    rw [hlog] at h1
    have heq : entH (fun b : Sum Bool Unit => condW (stopSlotMargLaw prog p hi) pfx b)
        = entH (fun b : Bool => condW (stopSlotMargLaw prog p hi) pfx (Sum.inl b)) := by
      refine entH_padded_eq (w := fun b => condW (stopSlotMargLaw prog p hi) pfx b)
        (f := fun b : Bool => condW (stopSlotMargLaw prog p hi) pfx (Sum.inl b)) ?_ (fun b => rfl)
      show condW (stopSlotMargLaw prog p hi) pfx (Sum.inr ()) = 0
      rw [condW, dif_neg hm, hz]
      simp
    rw [heq]
    exact h1

/-- For `0 ≤ p ≤ 1` and `n > 0`, the conditional next-slot entropy at a prefix that is not alive
is zero. -/
theorem clause17_stop_slot_marg_ent_zero {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n)
    {i : ℕ} (hi : i + 1 ≤ k) (hik : i < k) (pfx : Fin i → (Sum Bool Unit))
    (hdead : ¬ padAlive prog pfx) :
    entH (fun b => condW (stopSlotMargLaw prog p hi) pfx b) = 0 := by
  have hdnonneg : ∀ a b, 0 ≤ stopSlotMargLaw prog p hi (a, b) := by
    intro a b
    unfold stopSlotMargLaw
    exact Finset.sum_nonneg fun x _ =>
      clause17_stop_used_prefix_law_nonneg prog hp0 hp1 hn hi x (tExt a b)
  have hzero : ∀ b : Bool, stopSlotMargLaw prog p hi (pfx, Sum.inl b) = 0 := by
    intro b
    unfold stopSlotMargLaw
    exact Finset.sum_eq_zero fun x _ =>
      clause17_stop_used_next_slot_stopped prog p ((clause17_stop_prefix_le hi)) hi hik
        pfx hdead x b
  have hmarker : stopSlotMargLaw prog p hi (pfx, Sum.inr ())
      = margL (stopSlotMargLaw prog p hi) pfx := by
    simp only [margL, stopSlotMargLaw]
    calc (∑ x, stopUsedPrefixLaw prog p (i + 1) hi (x, tExt pfx (Sum.inr ())))
        = ∑ x, stopUsedPrefixLaw prog p i ((clause17_stop_prefix_le hi)) (x, pfx) := by
          apply Finset.sum_congr rfl
          intro x _
          exact clause17_stop_used_next_slot_marker_dead prog p
            ((clause17_stop_prefix_le hi)) hi hik pfx hdead x
      _ = ∑ x, ∑ b : Sum Bool Unit,
            stopUsedPrefixLaw prog p (i + 1) hi (x, tExt pfx b) := by
          apply Finset.sum_congr rfl
          intro x _
          exact clause17_stop_used_prefix_marg prog p
            ((clause17_stop_prefix_le hi)) hi x pfx
      _ = ∑ b : Sum Bool Unit, ∑ x,
            stopUsedPrefixLaw prog p (i + 1) hi (x, tExt pfx b) := Finset.sum_comm
  have hcw : ∀ b : Sum Bool Unit,
      condW (stopSlotMargLaw prog p hi) pfx b = 0 ∨
        condW (stopSlotMargLaw prog p hi) pfx b = 1 := by
    intro b
    by_cases hm : margL (stopSlotMargLaw prog p hi) pfx = 0
    · simp [condW, hm]
    · cases b with
        | inl b' =>
            rw [condW, dif_neg hm, hzero b']
            simp
        | inr u =>
            rw [condW, dif_neg hm, hmarker]
            have hne : margL (stopSlotMargLaw prog p hi) pfx ≠ 0 := hm
            simp [div_self hne]
  exact entH_zero_one (fun b => condW (stopSlotMargLaw prog p hi) pfx b) hcw

/-- At an alive prefix, the hidden-cell-conditioned next-slot entropy weighted by its marginal
equals the used-prefix joint weight times `binEntropy p`, for `0 ≤ p ≤ 1` and `n > 0`. -/
theorem clause17_stop_slot_post_ent {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n)
    {i : ℕ} (hi : i + 1 ≤ k) (hik : i < k) (pfx : Fin i → (Sum Bool Unit))
    (halive : padAlive prog pfx) (x : Fin n) :
    margL (stopSlotPostLaw prog p hi) (x, pfx)
        * entH (fun b : Sum Bool Unit => condW (stopSlotPostLaw prog p hi) (x, pfx) b)
      = stopUsedPrefixLaw prog p i ((clause17_stop_prefix_le hi)) (x, pfx) * binEntropy p := by
  have hmass := clause17_stop_slot_post_total prog p hi x pfx
  have hmarker := clause17_stop_slot_post_marker prog p hi hik pfx halive x
  have hstep :=
      clause17_stop_used_next_slot prog p ((clause17_stop_prefix_le hi)) hi hik pfx halive x
  by_cases hm : margL (stopSlotPostLaw prog p hi) (x, pfx) = 0
  · have hd0 : stopUsedPrefixLaw prog p i ((clause17_stop_prefix_le hi)) (x, pfx) = 0 := by
      rw [← hmass]
      exact hm
    have hcw : (fun b : Sum Bool Unit => condW (stopSlotPostLaw prog p hi) (x, pfx) b)
        = (fun _ => (0 : ℝ)) := by
      funext b
      simp [condW, hm]
    rw [hcw]
    have hent0 : entH (fun _ : Sum Bool Unit => (0 : ℝ)) = 0 := by
      unfold entH xlog2
      simp
    rw [hent0, hmass, hd0]
    simp
  · have hdne : stopUsedPrefixLaw prog p i ((clause17_stop_prefix_le hi)) (x, pfx) ≠ 0 := by
      rw [← hmass]
      exact hm
    have hpost : ∀ b : Bool,
        stopSlotPostLaw prog p hi ((x, pfx), Sum.inl b)
          = stopUsedPrefixLaw prog p i ((clause17_stop_prefix_le hi)) (x, pfx)
            * bscProb p (truthBit x (prog.cuts ⟨i, hik⟩ (stopPadDecode pfx))) b := by
      intro b
      exact hstep b
    have hcw : ∀ b : Bool,
        condW (stopSlotPostLaw prog p hi) (x, pfx) (Sum.inl b)
          = bscProb p (truthBit x (prog.cuts ⟨i, hik⟩ (stopPadDecode pfx))) b := by
      intro b
      rw [condW, dif_neg hm, hpost b, hmass]
      field_simp
    have hcwz : condW (stopSlotPostLaw prog p hi) (x, pfx) (Sum.inr ()) = 0 := by
      rw [condW, dif_neg hm, hmarker]
      simp
    have heq : entH (fun b : Sum Bool Unit => condW (stopSlotPostLaw prog p hi) (x, pfx) b)
        = entH (fun b : Bool => bscProb p (truthBit x (prog.cuts ⟨i, hik⟩ (stopPadDecode pfx))) b) := by
      refine entH_padded_eq
        (w := fun b : Sum Bool Unit => condW (stopSlotPostLaw prog p hi) (x, pfx) b)
        (f := fun b : Bool => bscProb p (truthBit x (prog.cuts ⟨i, hik⟩ (stopPadDecode pfx))) b) ?_ ?_
      · show condW (stopSlotPostLaw prog p hi) (x, pfx) (Sum.inr ()) = 0
        exact hcwz
      · intro b
        show condW (stopSlotPostLaw prog p hi) (x, pfx) (Sum.inl b)
          = bscProb p (truthBit x (prog.cuts ⟨i, hik⟩ (stopPadDecode pfx))) b
        exact hcw b
    have hent : entH (fun b : Bool =>
        bscProb p (truthBit x (prog.cuts ⟨i, hik⟩ (stopPadDecode pfx))) b) = binEntropy p :=
      entH_bscProb (truthBit x (prog.cuts ⟨i, hik⟩ (stopPadDecode pfx)))
    rw [heq, hent, hmass]

/-- At a prefix that is not alive, the marginal-weighted hidden-cell-conditioned next-slot
entropy is zero for `0 ≤ p ≤ 1` and `n > 0`. -/
theorem clause17_stop_slot_post_ent_zero {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n)
    {i : ℕ} (hi : i + 1 ≤ k) (hik : i < k) (pfx : Fin i → (Sum Bool Unit))
    (hdead : ¬ padAlive prog pfx) (x : Fin n) :
    margL (stopSlotPostLaw prog p hi) (x, pfx)
        * entH (fun b : Sum Bool Unit => condW (stopSlotPostLaw prog p hi) (x, pfx) b) = 0 := by
  have hmass := clause17_stop_slot_post_total prog p hi x pfx
  have hzero : ∀ b : Bool, stopSlotPostLaw prog p hi ((x, pfx), Sum.inl b) = 0 := by
    intro b
    exact clause17_stop_used_next_slot_stopped prog p
        ((clause17_stop_prefix_le hi)) hi hik pfx hdead x b
  have hmarker : stopSlotPostLaw prog p hi ((x, pfx), Sum.inr ())
      = margL (stopSlotPostLaw prog p hi) (x, pfx) := by
    simp only [stopSlotPostLaw]
    rw [clause17_stop_used_next_slot_marker_dead prog p ((clause17_stop_prefix_le hi)) hi hik pfx hdead x]
    exact hmass.symm
  have hcw : ∀ b : Sum Bool Unit,
      condW (stopSlotPostLaw prog p hi) (x, pfx) b = 0 ∨
        condW (stopSlotPostLaw prog p hi) (x, pfx) b = 1 := by
    intro b
    by_cases hm : margL (stopSlotPostLaw prog p hi) (x, pfx) = 0
    · simp [condW, hm]
    · cases b with
      | inl b' =>
          rw [condW, dif_neg hm, hzero b']
          simp
      | inr u =>
          rw [condW, dif_neg hm, hmarker]
          have hne : margL (stopSlotPostLaw prog p hi) (x, pfx) ≠ 0 := hm
          simp [div_self hne]
  have hent : entH (fun b : Sum Bool Unit => condW (stopSlotPostLaw prog p hi) (x, pfx) b) = 0 :=
    entH_zero_one (fun b : Sum Bool Unit => condW (stopSlotPostLaw prog p hi) (x, pfx) b) hcw
  rw [hent]
  simp

/-- For `0 ≤ p ≤ 1` and `n > 0`, the stopping-slot marginal conditional entropy is at most the
live prefix mass. -/
theorem clause17_stop_slot_marg_ent_le_live {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n)
    {i : ℕ} (hi : i + 1 ≤ k) (hik : i < k) :
    condEntH (stopSlotMargLaw prog p hi)
      ≤ stopLiveMass prog p ((clause17_stop_prefix_le hi)) := by
  have hdnonneg : ∀ a b, 0 ≤ stopSlotMargLaw prog p hi (a, b) := by
    intro a b
    unfold stopSlotMargLaw
    exact Finset.sum_nonneg fun x _ =>
      clause17_stop_used_prefix_law_nonneg prog hp0 hp1 hn hi x (tExt a b)
  rw [condEntH_eq_sum (stopSlotMargLaw prog p hi) hdnonneg]
  have hsplit : (∑ pfx : Fin i → (Sum Bool Unit),
        margL (stopSlotMargLaw prog p hi) pfx
          * entH (fun b : Sum Bool Unit => condW (stopSlotMargLaw prog p hi) pfx b))
      ≤ ∑ pfx : Fin i → (Sum Bool Unit),
        (if padAlive prog pfx then
            margL (stopSlotMargLaw prog p hi) pfx
          else 0) := by
    apply Finset.sum_le_sum
    intro pfx _
    by_cases halive : padAlive prog pfx
    · have h1 := clause17_stop_slot_marg_ent_le_one prog p hp0 hp1 hn hi hik pfx halive
      have hnonneg : 0 ≤ margL (stopSlotMargLaw prog p hi) pfx :=
        Finset.sum_nonneg fun a _ => hdnonneg pfx a
      rw [if_pos halive]
      exact (mul_le_mul_of_nonneg_left h1 hnonneg).trans (le_of_eq (mul_one _))
    · have h1 := clause17_stop_slot_marg_ent_zero prog p hp0 hp1 hn hi hik pfx halive
      rw [h1, if_neg halive]
      simp
  have hrepl : (∑ pfx : Fin i → (Sum Bool Unit),
        (if padAlive prog pfx then
            margL (stopSlotMargLaw prog p hi) pfx
          else 0))
      = ∑ pfx : Fin i → (Sum Bool Unit),
        (if padAlive prog pfx then
            (∑ x, stopUsedPrefixLaw prog p i ((clause17_stop_prefix_le hi)) (x, pfx))
          else 0) := by
    apply Finset.sum_congr rfl
    intro pfx _
    by_cases halive : padAlive prog pfx
    · rw [clause17_stop_slot_marg_total prog p hi pfx]
    · simp only [if_neg halive]
  calc (∑ pfx : Fin i → (Sum Bool Unit),
        margL (stopSlotMargLaw prog p hi) pfx
          * entH (fun b : Sum Bool Unit => condW (stopSlotMargLaw prog p hi) pfx b))
      ≤ ∑ pfx : Fin i → (Sum Bool Unit),
        (if padAlive prog pfx then
            margL (stopSlotMargLaw prog p hi) pfx
          else 0) := hsplit
    _ = ∑ pfx : Fin i → (Sum Bool Unit),
        (if padAlive prog pfx then
            (∑ x, stopUsedPrefixLaw prog p i ((clause17_stop_prefix_le hi)) (x, pfx))
          else 0) := hrepl
    _ = stopLiveMass prog p ((clause17_stop_prefix_le hi)) := rfl

/-- For `0 ≤ p ≤ 1` and `n > 0`, the stopping-slot post conditional entropy equals `binEntropy
p` times the live prefix mass. -/
theorem clause17_stop_slot_post_ent_live {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n)
    {i : ℕ} (hi : i + 1 ≤ k) (hik : i < k) :
    condEntH (stopSlotPostLaw prog p hi)
      = binEntropy p * stopLiveMass prog p ((clause17_stop_prefix_le hi)) := by
  have hdnonneg : ∀ z b, 0 ≤ stopSlotPostLaw prog p hi (z, b) := by
    intro z b
    unfold stopSlotPostLaw
    exact clause17_stop_used_prefix_law_nonneg prog hp0 hp1 hn hi z.1 (tExt z.2 b)
  rw [condEntH_eq_sum (stopSlotPostLaw prog p hi) hdnonneg]
  have hsplit : (∑ z : Fin n × (Fin i → (Sum Bool Unit)),
        margL (stopSlotPostLaw prog p hi) z
          * entH (fun b : Sum Bool Unit => condW (stopSlotPostLaw prog p hi) z b))
      = ∑ pfx : Fin i → (Sum Bool Unit),
        (if padAlive prog pfx then
            (∑ x, stopUsedPrefixLaw prog p i ((clause17_stop_prefix_le hi)) (x, pfx)) * binEntropy p
          else 0) := by
    calc (∑ z : Fin n × (Fin i → (Sum Bool Unit)),
          margL (stopSlotPostLaw prog p hi) z
            * entH (fun b : Sum Bool Unit => condW (stopSlotPostLaw prog p hi) z b))
        = ∑ x : Fin n, ∑ pfx : Fin i → (Sum Bool Unit),
            margL (stopSlotPostLaw prog p hi) (x, pfx)
              * entH (fun b : Sum Bool Unit => condW (stopSlotPostLaw prog p hi) (x, pfx) b) :=
          Fintype.sum_prod_type (fun z => margL (stopSlotPostLaw prog p hi) z
            * entH (fun b : Sum Bool Unit => condW (stopSlotPostLaw prog p hi) z b))
      _ = ∑ pfx : Fin i → (Sum Bool Unit), ∑ x : Fin n,
            margL (stopSlotPostLaw prog p hi) (x, pfx)
              * entH (fun b : Sum Bool Unit => condW (stopSlotPostLaw prog p hi) (x, pfx) b) :=
          Finset.sum_comm
      _ = ∑ pfx : Fin i → (Sum Bool Unit),
          (if padAlive prog pfx then
              (∑ x, stopUsedPrefixLaw prog p i ((clause17_stop_prefix_le hi)) (x, pfx)) * binEntropy p
            else 0) := by
          apply Finset.sum_congr rfl
          intro pfx _
          by_cases halive : padAlive prog pfx
          · rw [if_pos halive]
            calc (∑ x : Fin n, margL (stopSlotPostLaw prog p hi) (x, pfx)
                  * entH (fun b : Sum Bool Unit => condW (stopSlotPostLaw prog p hi) (x, pfx) b))
                = ∑ x : Fin n, (stopUsedPrefixLaw prog p i ((clause17_stop_prefix_le hi)) (x, pfx)
                    * binEntropy p) := by
                    apply Finset.sum_congr rfl
                    intro x _
                    exact clause17_stop_slot_post_ent prog p hp0 hp1 hn hi hik pfx halive x
              _ = (∑ x : Fin n, stopUsedPrefixLaw prog p i ((clause17_stop_prefix_le hi)) (x, pfx))
                  * binEntropy p := by
                    rw [Finset.sum_mul]
          · rw [if_neg halive]
            apply Finset.sum_eq_zero
            intro x _
            exact clause17_stop_slot_post_ent_zero prog p hp0 hp1 hn hi hik pfx halive x
  rw [hsplit]
  unfold stopLiveMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pfx _
  by_cases halive : padAlive prog pfx
  · rw [if_pos halive, if_pos halive]
    ring
  · rw [if_neg halive, if_neg halive]
    simp

/-- The used-prefix marginal equals the full-transcript marginal mass of transcripts whose
padded prefix matches the specified prefix. -/
theorem clause17_stop_used_prefix_marginal {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    {i : ℕ} (hi : i ≤ k) (pfx : Fin i → (Sum Bool Unit)) :
    (∑ x, stopUsedPrefixLaw prog p i hi (x, pfx))
      = ∑ y : Fin k → Bool, bscTransMarginal (stopToBscProg prog) p y
          * (if tPrefix i hi (stopPad prog y) = pfx then 1 else 0) := by
  unfold stopUsedPrefixLaw
  calc (∑ x, ∑ y : Fin k → Bool, bscJointCuts prog.cuts p x y
        * (if tPrefix i hi (stopPad prog y) = pfx then 1 else 0))
      = ∑ y : Fin k → Bool, ∑ x, bscJointCuts prog.cuts p x y
        * (if tPrefix i hi (stopPad prog y) = pfx then 1 else 0) := Finset.sum_comm
    _ = ∑ y : Fin k → Bool, (∑ x, bscJointCuts prog.cuts p x y)
        * (if tPrefix i hi (stopPad prog y) = pfx then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro y _
          rw [Finset.sum_mul]
    _ = ∑ y : Fin k → Bool, bscTransMarginal (stopToBscProg prog) p y
        * (if tPrefix i hi (stopPad prog y) = pfx then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro y _
          rfl

/-- If a padded transcript prefix is alive, then its original Boolean answer prefix is alive. -/
theorem clause17_pad_alive_of_stop_alive {n k : ℕ} (prog : BscStopProgram n k) {i : ℕ} (hi : i ≤ k)
    (y : Fin k → Bool) (halive : padAlive prog (tPrefix i hi (stopPad prog y))) :
    stopAlive prog i (stopPrefix i hi y) := by
  obtain ⟨hall, halive'⟩ := halive
  have hself : tPrefix i hi (stopPad prog y) = tPrefix i hi (stopPad prog y) := rfl
  obtain ⟨hstop, hys⟩ :=
    (clause17_stop_allinl_iff prog hi (tPrefix i hi (stopPad prog y)) hall y).mp hself
  have hdec : stopPadDecode (tPrefix i hi (stopPad prog y)) = stopPrefix i hi y := by
    funext j
    have hj : j.val < i := j.isLt
    have hjl : j.val < (prog.stop y).val := lt_of_lt_of_le hj hstop
    have h1 : tPrefix i hi (stopPad prog y) j = Sum.inl (y ⟨j.val, by omega⟩) := by
      show (if (⟨j.val, by omega⟩ : Fin k).val < (prog.stop y).val
        then Sum.inl (y ⟨j.val, by omega⟩) else Sum.inr ()) = _
      rw [if_pos hjl]
    simp only [stopPadDecode]
    rw [h1]
    rfl
  rw [← hdec]
  exact halive'

/-- Distributes a fixed-condition indicator across a finite sum. -/
theorem clause17_ite_sum {α : Type} [Fintype α] (c : Prop) [Decidable c] (g : α → ℝ) :
    (if c then (∑ y, g y) else 0) = ∑ y, (if c then g y else 0) := by
  by_cases h : c
  · simp [h]
  · simp [h]

/-- For `0 ≤ p ≤ 1` and `n > 0`, the live used-prefix mass is at most the corresponding alive
probability. -/
theorem clause17_stop_live_mass_le_alive_prob {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n) {i : ℕ} (hi : i ≤ k) :
    stopLiveMass prog p hi ≤ stopAliveProb prog p i hi := by
  have hnonneg : ∀ y : Fin k → Bool, 0 ≤ bscTransMarginal (stopToBscProg prog) p y := by
    intro y
    unfold bscTransMarginal
    exact Finset.sum_nonneg fun x _ =>
      bscJointCuts_nonneg prog.cuts p hp0 hp1 hn x y
  have htrans := clause17_stop_used_prefix_marginal prog p hi
  have hfib : ∀ (y : Fin k → Bool),
      (∑ pfx : Fin i → (Sum Bool Unit),
          (if padAlive prog pfx then
              (if tPrefix i hi (stopPad prog y) = pfx then (1 : ℝ) else 0)
            else 0))
        = (if padAlive prog (tPrefix i hi (stopPad prog y)) then (1 : ℝ) else 0) := by
    intro y
    classical
    have hswap : (∑ pfx : Fin i → (Sum Bool Unit),
          (if padAlive prog pfx then
              (if tPrefix i hi (stopPad prog y) = pfx then (1 : ℝ) else 0)
            else 0))
        = ∑ pfx : Fin i → (Sum Bool Unit),
          (if tPrefix i hi (stopPad prog y) = pfx then
              (if padAlive prog pfx then (1 : ℝ) else 0)
            else 0) := by
      apply Finset.sum_congr rfl
      intro pfx _
      by_cases hb : padAlive prog pfx
      · by_cases hc : tPrefix i hi (stopPad prog y) = pfx <;> simp [hb, hc]
      · by_cases hc : tPrefix i hi (stopPad prog y) = pfx <;> simp [hb, hc]
    rw [hswap]
    have hsingle := Finset.sum_eq_single (tPrefix i hi (stopPad prog y)) (s := Finset.univ)
      (f := fun pfx => if tPrefix i hi (stopPad prog y) = pfx then
          (if padAlive prog pfx then (1 : ℝ) else 0) else 0)
      (fun b _ hne => by
        show (if tPrefix i hi (stopPad prog y) = b then
            (if padAlive prog b then (1 : ℝ) else 0) else 0) = 0
        rw [if_neg (Ne.symm hne)])
      (fun hmem => absurd (Finset.mem_univ (tPrefix i hi (stopPad prog y))) hmem)
    simpa using! hsingle
  unfold stopLiveMass stopAliveProb
  calc (∑ pfx : Fin i → (Sum Bool Unit),
        (if padAlive prog pfx then (∑ x, stopUsedPrefixLaw prog p i hi (x, pfx)) else 0))
      = ∑ pfx : Fin i → (Sum Bool Unit),
        (if padAlive prog pfx then
            (∑ y : Fin k → Bool, bscTransMarginal (stopToBscProg prog) p y
              * (if tPrefix i hi (stopPad prog y) = pfx then 1 else 0))
          else 0) := by
          apply Finset.sum_congr rfl
          intro pfx _
          by_cases h : padAlive prog pfx
          · simp only [if_pos h]
            rw [htrans pfx]
          · simp only [if_neg h]
    _ = ∑ pfx : Fin i → (Sum Bool Unit), ∑ y : Fin k → Bool,
          (if padAlive prog pfx then
              bscTransMarginal (stopToBscProg prog) p y
                * (if tPrefix i hi (stopPad prog y) = pfx then 1 else 0)
            else 0) := by
          apply Finset.sum_congr rfl
          intro pfx _
          rw [clause17_ite_sum]
    _ = ∑ y : Fin k → Bool, ∑ pfx : Fin i → (Sum Bool Unit),
          (if padAlive prog pfx then
              bscTransMarginal (stopToBscProg prog) p y
                * (if tPrefix i hi (stopPad prog y) = pfx then 1 else 0)
            else 0) := Finset.sum_comm
    _ = ∑ y : Fin k → Bool, bscTransMarginal (stopToBscProg prog) p y
        * (∑ pfx : Fin i → (Sum Bool Unit),
            (if padAlive prog pfx then
                (if tPrefix i hi (stopPad prog y) = pfx then 1 else 0)
              else 0)) := by
          apply Finset.sum_congr rfl
          intro y _
          have hshift : (∑ pfx : Fin i → (Sum Bool Unit),
                (if padAlive prog pfx then
                    bscTransMarginal (stopToBscProg prog) p y
                      * (if tPrefix i hi (stopPad prog y) = pfx then 1 else 0)
                  else 0))
              = ∑ pfx : Fin i → (Sum Bool Unit),
                bscTransMarginal (stopToBscProg prog) p y
                  * (if padAlive prog pfx then
                      (if tPrefix i hi (stopPad prog y) = pfx then 1 else 0)
                    else 0) := by
            apply Finset.sum_congr rfl
            intro pfx _
            by_cases h : padAlive prog pfx
            · simp only [if_pos h]
            · simp only [if_neg h]
              ring
          rw [hshift, Finset.mul_sum]
    _ = ∑ y : Fin k → Bool, bscTransMarginal (stopToBscProg prog) p y
        * (if padAlive prog (tPrefix i hi (stopPad prog y)) then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro y _
          rw [hfib y]
    _ ≤ ∑ y : Fin k → Bool, bscTransMarginal (stopToBscProg prog) p y
        * (if stopAlive prog i (stopPrefix i hi y) then 1 else 0) := by
          apply Finset.sum_le_sum
          intro y _
          have hle : (if padAlive prog (tPrefix i hi (stopPad prog y)) then (1 : ℝ) else 0)
              ≤ (if stopAlive prog i (stopPrefix i hi y) then (1 : ℝ) else 0) := by
            by_cases h : padAlive prog (tPrefix i hi (stopPad prog y))
            · simp [h, clause17_pad_alive_of_stop_alive prog hi y h]
            · simp [h]
              split <;> norm_num
          exact mul_le_mul_of_nonneg_left hle (hnonneg y)
    _ = stopAliveProb prog p i hi := rfl

/-- The alive probability at the full transcript length is zero. -/
theorem clause17_stop_alive_prob_zero {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ) :
    stopAliveProb prog p k (Nat.le_refl k) = 0 := by
  have hnot : ∀ y : Fin k → Bool, ¬ stopAlive prog k (stopPrefix k (Nat.le_refl k) y) := by
    intro y h
    have h1 := (clause17_stop_alive_of_transcript prog (Nat.le_refl k) y).mp h
    have hlt : (prog.stop y).val < k + 1 := prog.stop y |>.isLt
    exact absurd h1 (by omega)
  unfold stopAliveProb
  apply Finset.sum_eq_zero
  intro y _
  simp [hnot y]

/-- The sum of alive probabilities over query indices equals the expected stopping cost. -/
theorem clause17_stop_survival_sum {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ) :
    (∑ x : Fin k, stopAliveProb prog p x.val (Nat.le_of_lt x.isLt)) = expectedStopCost prog p := by
  have hz := clause17_stop_alive_prob_zero prog p
  let g : ℕ → ℝ := fun i => if hi : i ≤ k then stopAliveProb prog p i hi else 0
  have hmain : (∑ i : Fin (k + 1), stopSurvivalProfile prog p i)
      = ∑ x : Fin k, stopAliveProb prog p x.val (Nat.le_of_lt x.isLt) := by
    have h1 : (∑ i : Fin (k + 1), stopSurvivalProfile prog p i)
        = ∑ i : Fin (k + 1), g i.val := by
      apply Finset.sum_congr rfl
      intro i _
      have hi : i.val ≤ k := by omega
      unfold g
      rw [dif_pos hi]
      rfl
    have h2 : (∑ i ∈ Finset.range k, g i)
        = ∑ x : Fin k, stopAliveProb prog p x.val (Nat.le_of_lt x.isLt) := by
      rw [Finset.sum_range (f := g)]
      apply Finset.sum_congr rfl
      intro x _
      have hx : g x.val = stopAliveProb prog p x.val (Nat.le_of_lt x.isLt) := by
        unfold g
        rw [dif_pos (by omega : x.val ≤ k)]
      rw [hx]
    rw [h1]
    rw [← Finset.sum_range (f := g)]
    rw [Finset.sum_range_succ]
    have hgk : g k = 0 := by
      have hk : k ≤ k := by omega
      simp only [g, dif_pos hk]
      exact hz
    rw [hgk, h2, add_zero]
  rw [← hmain]
  exact (clause17_expected_stop_cost_eq_survival prog p).symm

/-- For `1 / 2 < p ≤ 1` and `n > 0`, used-transcript mutual information is at most expected
stopping cost times `queryInfo p`. -/
theorem clause17_stop_used_mut_info_le {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    (hp : 1 / 2 < p) (hp1 : p ≤ 1) (hn : 0 < n) :
    stopUsedMutInfo prog p ≤ expectedStopCost prog p * queryInfo p := by
  have hp0 : 0 ≤ p := by linarith
  have hqi : 0 ≤ queryInfo p := le_of_lt (clause17_queryInfo_pos_of hp hp1)
  have hchain := clause17_stop_used_chain prog p hp0 hp1 hn k (Nat.le_refl k)
  have hslot : ∀ x : Fin k,
      stopSlotChainTerm prog p x.val
        ≤ queryInfo p
          * stopLiveMass prog p (clause17_stop_prefix_le (Nat.succ_le_of_lt x.isLt)) := by
    intro x
    have hbound : x.val + 1 ≤ k := Nat.succ_le_of_lt x.isLt
    have hΔ := stopSlotChainTerm_eq prog p hbound
    have h1 :=
        clause17_stop_slot_marg_ent_le_live prog p hp0 hp1 hn hbound (Nat.lt_of_succ_le hbound)
    have h2 := clause17_stop_slot_post_ent_live prog p hp0 hp1 hn hbound (Nat.lt_of_succ_le hbound)
    rw [hΔ]
    have h3 : condEntH (stopSlotMargLaw prog p hbound)
        - condEntH (stopSlotPostLaw prog p hbound)
          ≤ stopLiveMass prog p (clause17_stop_prefix_le hbound)
            - binEntropy p * stopLiveMass prog p (clause17_stop_prefix_le hbound) := by
      rw [h2]
      exact sub_le_sub_right h1 _
    calc condEntH (stopSlotMargLaw prog p hbound)
          - condEntH (stopSlotPostLaw prog p hbound)
        ≤ stopLiveMass prog p (clause17_stop_prefix_le hbound)
            - binEntropy p * stopLiveMass prog p (clause17_stop_prefix_le hbound) := h3
      _ = queryInfo p * stopLiveMass prog p (clause17_stop_prefix_le hbound) := by
          have hq : queryInfo p = 1 - binEntropy p := rfl
          rw [hq]
          ring
  have hlive : (∑ x : Fin k,
        stopLiveMass prog p (clause17_stop_prefix_le (Nat.succ_le_of_lt x.isLt)))
      ≤ expectedStopCost prog p := by
    calc (∑ x : Fin k,
        stopLiveMass prog p (clause17_stop_prefix_le (Nat.succ_le_of_lt x.isLt)))
        ≤ ∑ x : Fin k, stopAliveProb prog p x.val (by omega) := by
          apply Finset.sum_le_sum
          intro x _
          exact clause17_stop_live_mass_le_alive_prob prog p hp0 hp1 hn (Nat.le_of_lt x.isLt)
      _ = expectedStopCost prog p := clause17_stop_survival_sum prog p
  have hmut : mutInfo (stopUsedPrefixLaw prog p k (Nat.le_refl k))
      = ∑ x : Fin k, stopSlotChainTerm prog p x.val := by
    rw [hchain]
    rw [Finset.sum_range]
  have hlaw : stopUsedJointLaw prog p = stopUsedPrefixLaw prog p k (Nat.le_refl k) := by
    funext z
    exact (clause17_stop_used_law_full prog p z.1 z.2).symm
  have hmutInfo : stopUsedMutInfo prog p = mutInfo (stopUsedPrefixLaw prog p k (Nat.le_refl k)) := by
    unfold stopUsedMutInfo
    rw [hlaw]
  rw [hmutInfo, hmut]
  calc (∑ x : Fin k, stopSlotChainTerm prog p x.val)
      ≤ ∑ x : Fin k, (queryInfo p
          * stopLiveMass prog p (clause17_stop_prefix_le (Nat.succ_le_of_lt x.isLt))) := by
        apply Finset.sum_le_sum
        intro x _
        exact hslot x
    _ = queryInfo p * (∑ x : Fin k,
          stopLiveMass prog p (clause17_stop_prefix_le (Nat.succ_le_of_lt x.isLt))) := by
        rw [Finset.mul_sum]
    _ ≤ queryInfo p * expectedStopCost prog p :=
        mul_le_mul_of_nonneg_left hlive hqi
    _ = expectedStopCost prog p * queryInfo p := by ring

/-- A stopping program on at least two hidden cells whose guess depends only on used answers and
whose error is at most `0 ≤ δ ≤ 1 / 2` has expected cost at least `fanoCapacityBound n p δ`
when `1 / 2 < p ≤ 1` [BenOrHassidim2007]. -/
theorem clause17_stop_expected_cost_lower_bound {n k : ℕ} (hn : 2 ≤ n) (prog : BscStopProgram n k)
    {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1) (hguess : StopGuessFromUsed prog)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) (herr : stopErrorProb prog p ≤ δ) :
    expectedStopCost prog p ≥ fanoCapacityBound n p δ := by
  have hp0 : 0 ≤ p := by linarith
  have hfano := clause17_stop_used_fano hn prog hp0 hp1 hguess hδ0 hδ1 herr
  have hmi := clause17_stop_used_mut_info_le prog p hp hp1 (by omega)
  have hqi : 0 < queryInfo p := clause17_queryInfo_pos_of hp hp1
  have hkey : fanoNumerator n δ ≤ expectedStopCost prog p * queryInfo p := le_trans hfano hmi
  calc fanoCapacityBound n p δ
      = fanoNumerator n δ / queryInfo p := rfl
    _ ≤ (expectedStopCost prog p * queryInfo p) / queryInfo p :=
        div_le_div_of_nonneg_right hkey hqi.le
    _ = expectedStopCost prog p := by field_simp

/-- For query weights satisfying `RecQueryProb`, the total weight of true comparisons lies in
`[0, 1]`. -/
theorem clause17_rec_true_mass_range {n : ℕ} (μ : Fin n → ℝ) (hμ : RecQueryProb μ) (x : Fin n) :
    0 ≤ recTrueMass μ x ∧ recTrueMass μ x ≤ 1 := by
  constructor
  · unfold recTrueMass
    apply Finset.sum_nonneg
    intro c _
    exact mul_nonneg (hμ.1 c) (by split <;> norm_num)
  · calc (∑ c, μ c * (if truthBit x c then 1 else 0)) ≤ ∑ c, μ c * 1 := by
          apply Finset.sum_le_sum
          intro c _
          by_cases h : truthBit x c
          · simp [h]
          · simp [h]
            exact hμ.1 c
      _ = ∑ c, μ c := by simp
      _ = 1 := hμ.2

/-- The mixed recursive query answer weights sum to one when the query weights satisfy
`RecQueryProb`. -/
theorem clause17_rec_mix_law_total {n : ℕ} (μ : Fin n → ℝ) (hμ : RecQueryProb μ) (p : ℝ)
    (x : Fin n) : (∑ b, recMixProb μ p x b) = 1 := by
  unfold recMixProb
  calc (∑ b, ∑ c, μ c * bscProb p (truthBit x c) b)
      = ∑ c, ∑ b, μ c * bscProb p (truthBit x c) b := Finset.sum_comm
    _ = ∑ c, μ c * (∑ b, bscProb p (truthBit x c) b) := by
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.mul_sum]
    _ = ∑ c, μ c * 1 := by
        apply Finset.sum_congr rfl
        intro c _
        rw [bscProb_sum]
    _ = 1 := by
        rw [← Finset.sum_mul, hμ.2]
        simp

/-- Expresses the true-answer binary channel weight as `1 - p` plus `2 * p - 1` when the
comparison truth bit is true. -/
theorem clause17_rec_bsc_prob_eq {n : ℕ} (p : ℝ) (x c : Fin n) :
    bscProb p (truthBit x c) true
      = (1 - p) + (if truthBit x c then 2 * p - 1 else 0) := by
  by_cases h : truthBit x c
  · simp [bscProb, h]
    ring
  · simp [bscProb, h]

/-- The mixed true-answer weight equals `1 - p` plus the true-comparison mass times `2 * p - 1`
for query weights satisfying `RecQueryProb`. -/
theorem clause17_rec_mix_true_eq {n : ℕ} (μ : Fin n → ℝ) (hμ : RecQueryProb μ) (p : ℝ) (x : Fin n) :
    recMixTrue μ p x = (1 - p) + recTrueMass μ x * (2 * p - 1) := by
  have hpoint : ∀ c : Fin n,
      μ c * bscProb p (truthBit x c) true
        = μ c * (1 - p) + μ c * (if truthBit x c then 2 * p - 1 else 0) := by
    intro c
    rw [clause17_rec_bsc_prob_eq p x c]
    ring
  have hsum : (∑ c, μ c * bscProb p (truthBit x c) true)
      = (∑ c, μ c * (1 - p)) + ∑ c, μ c * (if truthBit x c then 2 * p - 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    rw [hpoint c]
  have hsum2 : (∑ c, μ c * (1 - p)) = (1 - p) * (∑ c, μ c) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring
  have hsum3 : (∑ c, μ c * (if truthBit x c then 2 * p - 1 else 0))
      = (2 * p - 1) * (∑ c, μ c * (if truthBit x c then 1 else 0)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    by_cases h : truthBit x c
    · simp [h]
      ring
    · simp [h]
  calc recMixTrue μ p x
      = ∑ c, μ c * bscProb p (truthBit x c) true := rfl
    _ = (∑ c, μ c * (1 - p)) + ∑ c, μ c * (if truthBit x c then 2 * p - 1 else 0) := hsum
    _ = (1 - p) * (∑ c, μ c)
          + (2 * p - 1) * (∑ c, μ c * (if truthBit x c then 1 else 0)) := by
        rw [hsum2, hsum3]
    _ = (1 - p) + (2 * p - 1) * recTrueMass μ x := by
        rw [hμ.2, mul_one]
        rfl
    _ = (1 - p) + recTrueMass μ x * (2 * p - 1) := by ring

/-- For query weights satisfying `RecQueryProb` and `p ≥ 1 / 2`, the mixed true-answer weight
lies between `1 - p` and `p`. -/
theorem clause17_rec_mix_true_range {n : ℕ} (μ : Fin n → ℝ) (hμ : RecQueryProb μ) {p : ℝ}
    (hp : 1 / 2 ≤ p) (x : Fin n) :
    1 - p ≤ recMixTrue μ p x ∧ recMixTrue μ p x ≤ p := by
  have htm := clause17_rec_true_mass_range μ hμ x
  rw [clause17_rec_mix_true_eq μ hμ p x]
  constructor
  · have hnonneg : 0 ≤ recTrueMass μ x * (2 * p - 1) :=
      mul_nonneg htm.1 (by linarith)
    linarith
  · have hle : recTrueMass μ x * (2 * p - 1) ≤ 1 * (2 * p - 1) :=
      mul_le_mul_of_nonneg_right htm.2 (by linarith)
    linarith

/-- For query weights satisfying `RecQueryProb` and `1 / 2 < p ≤ 1`, the mixed-query conditional
entropy is at least `binEntropy p`. -/
theorem clause17_rec_post_ent_ge {n : ℕ} (μ : Fin n → ℝ) (hμ : RecQueryProb μ) {p : ℝ}
    (hp : 1 / 2 < p) (hp1 : p ≤ 1) (x : Fin n) :
    recPostEnt μ p x ≥ binEntropy p := by
  have hrng := clause17_rec_mix_true_range μ hμ (show 1 / 2 ≤ p by linarith) x
  have hlo : 1 - p ≤ recMixTrue μ p x := hrng.1
  have hhi : recMixTrue μ p x ≤ p := hrng.2
  have h1p0 : 0 ≤ 1 - p := by linarith
  have h1p1 : 1 - p ≤ 1 / 2 := by linarith
  unfold recPostEnt
  by_cases hc : recMixTrue μ p x ≤ 1 / 2
  · have hmono := clause17_binEntropy_mono h1p0 h1p1 (by linarith) hc hlo
    calc binEntropy p = binEntropy (1 - p) := clause17_binEntropy_symmetry p
      _ ≤ binEntropy (recMixTrue μ p x) := hmono
  · have hhalf : 1 / 2 ≤ recMixTrue μ p x := by linarith
    have h1s0 : 0 ≤ 1 - recMixTrue μ p x := by linarith
    have h1s1 : 1 - recMixTrue μ p x ≤ 1 / 2 := by linarith
    have h1s : 1 - p ≤ 1 - recMixTrue μ p x := by linarith
    have hmono := clause17_binEntropy_mono h1p0 h1p1 h1s0 h1s1 h1s
    calc binEntropy p = binEntropy (1 - p) := clause17_binEntropy_symmetry p
      _ ≤ binEntropy (1 - recMixTrue μ p x) := hmono
      _ = binEntropy (recMixTrue μ p x) := (clause17_binEntropy_symmetry (recMixTrue μ p x)).symm

/-- For query weights satisfying `RecQueryProb` and `1 / 2 < p ≤ 1`, the recursive slot
information is at most `queryInfo p`. -/
theorem clause17_rec_slot_info_le {n : ℕ} (μ : Fin n → ℝ) (hμ : RecQueryProb μ) {p : ℝ}
    (hp : 1 / 2 < p) (hp1 : p ≤ 1) (x : Fin n) :
    recSlotInfo μ p x ≤ queryInfo p := by
  have h := clause17_rec_post_ent_ge μ hμ hp hp1 x
  unfold recSlotInfo queryInfo
  linarith

/-- A finite sum selecting one index by equality equals the selected constant. -/
theorem clause17_sum_ite_eq {α : Type} [Fintype α] [DecidableEq α] (c : α) (X : ℝ) :
    (∑ d : α, if d = c then X else 0) = X := by
  have h1 : (∑ d ∈ (Finset.univ : Finset α).erase c, (if d = c then X else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    have hne : d ≠ c := (Finset.mem_erase.mp hd).1
    simp [hne]
  have h2 := Finset.sum_erase_add (Finset.univ : Finset α)
    (fun d => if d = c then X else 0) (Finset.mem_univ c)
  have h3 : (∑ d ∈ (Finset.univ : Finset α), (if d = c then X else 0))
      = ∑ d : α, (if d = c then X else 0) := rfl
  rw [h3] at h2
  rw [h1, zero_add] at h2
  have h2' : (if c = c then X else 0) = ∑ d : α, (if d = c then X else 0) := h2
  rw [if_pos rfl] at h2'
  exact h2'.symm

/-- The point mass at a cut satisfies `RecQueryProb`. -/
theorem clause17_rec_point_mass_prob {n : ℕ} (c : Fin n) : RecQueryProb (recPointMass c) := by
  constructor
  · intro d
    by_cases h : d = c
    · simp [h, recPointMass]
    · simp [h, recPointMass]
  · have h := clause17_sum_ite_eq (α := Fin n) c 1
    have h' : (∑ d : Fin n, recPointMass c d) = 1 := by
      calc (∑ d : Fin n, recPointMass c d) = ∑ d : Fin n, if d = c then 1 else 0 := rfl
        _ = 1 := h
    exact h'

/-- A point-mass query has conditional entropy `binEntropy p` and slot information `queryInfo
p`. -/
theorem clause17_rec_point_mass_eq {n : ℕ} {p : ℝ} (c x : Fin n) :
    recPostEnt (recPointMass c) p x = binEntropy p ∧
      recSlotInfo (recPointMass c) p x = queryInfo p := by
  have hμ : RecQueryProb (recPointMass c) := clause17_rec_point_mass_prob c
  have htm : recTrueMass (recPointMass c) x = (if truthBit x c then 1 else 0) := by
    unfold recTrueMass
    have hmain : ∀ d : Fin n,
        (recPointMass c d) * (if truthBit x d then 1 else 0)
          = (if d = c then (if truthBit x c then 1 else 0) else 0) := by
      intro d
      by_cases hdc : d = c
      · rw [hdc]
        simp [recPointMass]
      · simp [hdc, recPointMass]
    rw [Finset.sum_congr rfl (fun d _ => hmain d)]
    exact clause17_sum_ite_eq c (if truthBit x c then 1 else 0)
  have hmix : recMixTrue (recPointMass c) p x = (if truthBit x c then p else 1 - p) := by
    rw [clause17_rec_mix_true_eq (recPointMass c) hμ p x, htm]
    by_cases h : truthBit x c
    · simp [h]
      ring
    · simp [h]
  have hent : recPostEnt (recPointMass c) p x = binEntropy p := by
    unfold recPostEnt
    rw [hmix]
    by_cases h : truthBit x c
    · simp [h]
    · simp [h]
      exact (clause17_binEntropy_symmetry p).symm
  refine ⟨hent, ?_⟩
  unfold recSlotInfo queryInfo
  rw [hent]

/-- For query weights satisfying `RecQueryProb`, `1 / 2 < p ≤ 1`, and true-comparison mass
strictly between zero and one, the conditional entropy exceeds `binEntropy p` and the slot
information is less than `queryInfo p`. -/
theorem clause17_rec_nondegenerate_gt {n : ℕ} (μ : Fin n → ℝ) (hμ : RecQueryProb μ) {p : ℝ}
    (hp : 1 / 2 < p) (hp1 : p ≤ 1) (x : Fin n)
    (h0 : 0 < recTrueMass μ x) (h1 : recTrueMass μ x < 1) :
    recPostEnt μ p x > binEntropy p ∧ recSlotInfo μ p x < queryInfo p := by
  have htm := clause17_rec_mix_true_eq μ hμ p x
  have h2p1 : 0 < 2 * p - 1 := by linarith
  have hlo : 1 - p < recMixTrue μ p x := by
    have hnonneg : 0 < recTrueMass μ x * (2 * p - 1) := mul_pos h0 h2p1
    linarith
  have hhi : recMixTrue μ p x < p := by
    have hle : recTrueMass μ x * (2 * p - 1) < 1 * (2 * p - 1) :=
      mul_lt_mul_of_pos_right h1 h2p1
    linarith
  have h1p0 : 0 ≤ 1 - p := by linarith
  have h1p1 : 1 - p ≤ 1 / 2 := by linarith
  have hpost : recPostEnt μ p x > binEntropy p := by
    unfold recPostEnt
    by_cases hc : recMixTrue μ p x ≤ 1 / 2
    · have hmono := clause17_binEntropy_mono_strict h1p0 h1p1 (by linarith) hc hlo
      calc binEntropy p = binEntropy (1 - p) := clause17_binEntropy_symmetry p
        _ < binEntropy (recMixTrue μ p x) := hmono
    · have hhalf : 1 / 2 ≤ recMixTrue μ p x := by linarith
      have h1s0 : 0 ≤ 1 - recMixTrue μ p x := by linarith
      have h1s1 : 1 - recMixTrue μ p x ≤ 1 / 2 := by linarith
      have h1s : 1 - p < 1 - recMixTrue μ p x := by linarith
      have hmono := clause17_binEntropy_mono_strict h1p0 h1p1 h1s0 h1s1 h1s
      calc binEntropy p = binEntropy (1 - p) := clause17_binEntropy_symmetry p
        _ < binEntropy (1 - recMixTrue μ p x) := hmono
        _ = binEntropy (recMixTrue μ p x) := (clause17_binEntropy_symmetry (recMixTrue μ p x)).symm
  refine ⟨hpost, ?_⟩
  unfold recSlotInfo queryInfo
  linarith

/-- Binary entropy at `1 / 2` equals one bit. -/
theorem clause17_binEntropy_half : binEntropy (1 / 2 : ℝ) = 1 := by
  rw [clause17_binEntropy_eq_mathlib]
  have h1 : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
  rw [h1, Real.binEntropy_two_inv]
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  field_simp

/-- For query weights satisfying `RecQueryProb` with true-comparison mass `1 / 2`, the
conditional entropy equals one and the slot information equals zero. -/
theorem clause17_rec_uniform_query_is_uninformative {n : ℕ} (μ : Fin n → ℝ) (hμ : RecQueryProb μ)
    {p : ℝ} (x : Fin n) (hhalf : recTrueMass μ x = 1 / 2) :
    recPostEnt μ p x = 1 ∧ recSlotInfo μ p x = 0 := by
  have hmix : recMixTrue μ p x = 1 / 2 := by
    rw [clause17_rec_mix_true_eq μ hμ p x, hhalf]
    ring
  have hent : recPostEnt μ p x = 1 := by
    unfold recPostEnt
    rw [hmix]
    exact clause17_binEntropy_half
  refine ⟨hent, ?_⟩
  unfold recSlotInfo
  rw [hent]
  ring

/-- When `1 / 2 < p ≤ 1` and the recursive slot information is positive, the recursive capacity
expression equals the ordinary Fano capacity expression times `queryInfo p / recSlotInfo μ p
x`. -/
theorem clause17_rec_fano_capacity_bound_eq {n : ℕ} (μ : Fin n → ℝ) {p : ℝ}
    (hp : 1 / 2 < p) (hp1 : p ≤ 1) (x : Fin n) {δ : ℝ}
    (hrec : 0 < recSlotInfo μ p x) :
    recFanoCapacityBound μ p x δ
      = fanoCapacityBound n p δ * (queryInfo p / recSlotInfo μ p x) := by
  have hqi : 0 < queryInfo p := clause17_queryInfo_pos_of hp hp1
  have hqi0 : queryInfo p ≠ 0 := ne_of_gt hqi
  have hrec0 : recSlotInfo μ p x ≠ 0 := ne_of_gt hrec
  unfold recFanoCapacityBound fanoCapacityBound
  field_simp

/-- For query weights satisfying `RecQueryProb`, `1 / 2 < p ≤ 1`, and positive recursive slot
information, the ratio of ordinary query information to slot information is at least one. -/
theorem clause17_rec_fano_factor_ge_one {n : ℕ} (μ : Fin n → ℝ) (hμ : RecQueryProb μ) {p : ℝ}
    (hp : 1 / 2 < p) (hp1 : p ≤ 1) (x : Fin n) (hrec : 0 < recSlotInfo μ p x) :
    1 ≤ queryInfo p / recSlotInfo μ p x := by
  have hqi : 0 < queryInfo p := clause17_queryInfo_pos_of hp hp1
  have hrate := clause17_rec_slot_info_le μ hμ hp hp1 x
  have hle : (1 : ℝ) * recSlotInfo μ p x ≤ queryInfo p := by linarith
  exact (le_div_iff₀ hrec).2 hle

/-- Every level of a recursive binary program uses the shared stopping function. -/
theorem clause17_rec_shared_stop_eq {n k : ℕ} (prog : RecBscProgram n k) (L : ℕ) :
    (prog.levelProg L).stop = recSharedStop prog :=
  prog.sharedStop L 0

/-- The stopping cost at any recursive level equals the value of the shared stopping index on
that transcript. -/
theorem clause17_rec_level_cost_eq {n k : ℕ} (prog : RecBscProgram n k) (L : ℕ)
    (y : Fin k → Bool) :
    stopCost (prog.levelProg L) y = (recSharedStop prog y).val := by
  unfold stopCost
  rw [clause17_rec_shared_stop_eq prog L]

/-- Every recursive level has nonnegative expected stopping cost for `0 ≤ p ≤ 1` and `n > 0`. -/
theorem clause17_rec_level_cost_nonneg {n k : ℕ} (prog : RecBscProgram n k) (L : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n) :
    0 ≤ expectedStopCost (prog.levelProg L) p := by
  unfold expectedStopCost
  apply Finset.sum_nonneg
  intro y _
  exact mul_nonneg
    (clause17_transcript_marginal_nonneg (stopToBscProg (prog.levelProg L)) p hp0 hp1 hn y)
    (clause17_stop_cost_nonneg (prog.levelProg L) y)

/-- For a recursive program with a positive number of levels, `0 ≤ p ≤ 1`, and `n > 0`, the last
level's expected cost is at most the total expected cost. -/
theorem clause17_rec_expected_cost_ge_last {n k : ℕ} (prog : RecBscProgram n k)
    (hlev : 0 < prog.levels) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n) :
    expectedStopCost (prog.levelProg (recLastLevel prog)) p ≤ recExpectedCost prog p := by
  have hmem : recLastLevel prog ∈ Finset.range prog.levels := by
    unfold recLastLevel
    simp only [Finset.mem_range]
    omega
  have hnonneg : 0 ≤ expectedStopCost (prog.levelProg (recLastLevel prog)) p :=
    clause17_rec_level_cost_nonneg prog (recLastLevel prog) hp0 hp1 hn
  unfold recExpectedCost
  exact Finset.single_le_sum (s := Finset.range prog.levels)
    (f := fun L => expectedStopCost (prog.levelProg L) p)
    (fun L _ => clause17_rec_level_cost_nonneg prog L hp0 hp1 hn) hmem

/-- A recursive program with a positive number of levels, at least two hidden cells, and
last-level error at most `0 ≤ δ ≤ 1 / 2` has total expected cost at least `fanoCapacityBound
n p δ` for `1 / 2 < p ≤ 1` [BenOrHassidim2007]. -/
theorem clause17_rec_expected_cost_lower_bound {n k : ℕ} (hn : 2 ≤ n)
    (prog : RecBscProgram n k) (hlev : 0 < prog.levels)
    {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2)
    (herr : recErrorProb prog hlev p ≤ δ) :
    recExpectedCost prog p ≥ fanoCapacityBound n p δ := by
  have hlast := clause17_rec_expected_cost_ge_last prog hlev
    (show 0 ≤ p by linarith) hp1 (by omega)
  have herr' : stopErrorProb (prog.levelProg (recLastLevel prog)) p ≤ δ := herr
  have hfb := clause17_stop_expected_cost_lower_bound hn (prog.levelProg (recLastLevel prog))
    hp hp1 (prog.guessFromUsed (recLastLevel prog)) hδ0 hδ1 herr'
  exact le_trans hfb hlast

/-- If every recursive level equals the same stopping program, total expected cost is the number
of levels times that program's expected cost. -/
theorem clause17_rec_expected_cost_eq_levels {n k : ℕ} (prog : RecBscProgram n k)
    (base : BscStopProgram n k) (hsame : ∀ L, prog.levelProg L = base) (p : ℝ) :
    recExpectedCost prog p = (prog.levels : ℝ) * expectedStopCost base p := by
  unfold recExpectedCost
  have hcongr : ∀ L ∈ Finset.range prog.levels,
      expectedStopCost (prog.levelProg L) p = expectedStopCost base p := by
    intro L _
    rw [hsame L]
  rw [Finset.sum_congr rfl hcongr]
  rw [Finset.sum_const, Finset.card_range]
  simp

/-- For identical recursive levels, a positive level count, at least two hidden cells, `1 / 2 <
p ≤ 1`, and last-level error at most `0 ≤ δ ≤ 1 / 2`, total expected cost is at least the
level count times the Fano capacity bound. -/
theorem clause17_rec_expected_cost_lower_bound_levels {n k : ℕ} (hn : 2 ≤ n)
    (prog : RecBscProgram n k) (hlev : 0 < prog.levels)
    (base : BscStopProgram n k) (hsame : ∀ L, prog.levelProg L = base)
    {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2)
    (herr : recErrorProb prog hlev p ≤ δ) :
    recExpectedCost prog p ≥ (prog.levels : ℝ) * fanoCapacityBound n p δ := by
  have hlast : stopErrorProb base p ≤ δ := by
    have h1 : recErrorProb prog hlev p = stopErrorProb base p := by
      unfold recErrorProb recLastLevel
      rw [hsame]
    rw [← h1]
    exact herr
  have hguess : StopGuessFromUsed base := by
    rw [← hsame (recLastLevel prog)]
    exact prog.guessFromUsed (recLastLevel prog)
  have hfb := clause17_stop_expected_cost_lower_bound hn base hp hp1
    hguess hδ0 hδ1 hlast
  have hcost : recExpectedCost prog p = (prog.levels : ℝ) * expectedStopCost base p :=
    clause17_rec_expected_cost_eq_levels prog base hsame p
  have hmul : (prog.levels : ℝ) * fanoCapacityBound n p δ
      ≤ (prog.levels : ℝ) * expectedStopCost base p :=
    mul_le_mul_of_nonneg_left hfb (by positivity)
  rw [hcost]
  exact hmul

/-- Regroups the difference of two double finite sums as the double sum of pointwise
differences. -/
theorem sum_sub_regroup3 {α β : Type} [Fintype α] [Fintype β]
    (f g : α × β → ℝ) :
    (∑ i, ∑ j, f (i, j)) - (∑ i, ∑ j, g (i, j))
      = ∑ i, ∑ j, (f (i, j) - g (i, j)) := by
  simp only [← Finset.sum_sub_distrib]

/-- For normalized nonnegative joint weights, expresses mutual information as the sum of joint
weights times the base-two log ratio to the product of the marginals, using a difference of
logarithms. -/
theorem mutInfo_eq_kl {α β : Type} [Fintype α] [Fintype β] (d : α × β → ℝ)
    (hd : ∀ i j, 0 ≤ d (i, j)) (_htot : ∑ i, ∑ j, d (i, j) = 1) :
    mutInfo d = ∑ i, ∑ j, d (i, j) *
      ((Real.log (d (i, j)) - Real.log (margL d i) - Real.log (margR d j))
        / Real.log 2) := by
  have hchain : entH d = entH (margL d) + condEntH d := entH_chain_rule d hd
  have hmut : mutInfo d = entH (margR d) - condEntH d := mutInfo_eq_margR d hd
  have hdecomp : mutInfo d = entH (margL d) + entH (margR d) - entH d := by
    linarith
  have hL : entH (margL d)
      = -∑ i, ∑ j, d (i, j) * (Real.log (margL d i) / Real.log 2) := by
    have h1 : entH (margL d) = -∑ i, margL d i * (Real.log (margL d i) / Real.log 2) := by
      simp only [entH, xlog2]
    have h2 : (∑ i, margL d i * (Real.log (margL d i) / Real.log 2))
        = ∑ i, ∑ j, d (i, j) * (Real.log (margL d i) / Real.log 2) := by
      calc
        (∑ i, margL d i * (Real.log (margL d i) / Real.log 2))
            = ∑ i, (∑ j, d (i, j)) * (Real.log (margL d i) / Real.log 2) := by
              congr 1
        _ = ∑ i, ∑ j, d (i, j) * (Real.log (margL d i) / Real.log 2) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.sum_mul]
    rw [h1, h2]
  have hR : entH (margR d)
      = -∑ i, ∑ j, d (i, j) * (Real.log (margR d j) / Real.log 2) := by
    have h1 : entH (margR d) = -∑ j, margR d j * (Real.log (margR d j) / Real.log 2) := by
      simp only [entH, xlog2]
    have h2 : (∑ j, margR d j * (Real.log (margR d j) / Real.log 2))
        = ∑ i, ∑ j, d (i, j) * (Real.log (margR d j) / Real.log 2) := by
      calc
        (∑ j, margR d j * (Real.log (margR d j) / Real.log 2))
            = ∑ j, (∑ i, d (i, j)) * (Real.log (margR d j) / Real.log 2) := by
              congr 1
        _ = ∑ j, ∑ i, d (i, j) * (Real.log (margR d j) / Real.log 2) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [Finset.sum_mul]
        _ = ∑ i, ∑ j, d (i, j) * (Real.log (margR d j) / Real.log 2) := by
              rw [Finset.sum_comm]
    rw [h1, h2]
  have hD : entH d
      = -∑ i, ∑ j, d (i, j) * (Real.log (d (i, j)) / Real.log 2) := by
    have h1 : entH d = -∑ z : α × β, xlog2 (d z) := by
      simp only [entH]
    have h2 : (∑ z : α × β, xlog2 (d z))
        = ∑ i, ∑ j, d (i, j) * (Real.log (d (i, j)) / Real.log 2) := by
      rw [Fintype.sum_prod_type]
      simp only [xlog2]
    rw [h1, h2]
  have hregroup : (∑ i, ∑ j, d (i, j) * (Real.log (d (i, j)) / Real.log 2))
        - (∑ i, ∑ j, d (i, j) * (Real.log (margL d i) / Real.log 2))
        - (∑ i, ∑ j, d (i, j) * (Real.log (margR d j) / Real.log 2))
      = ∑ i, ∑ j, d (i, j) *
          ((Real.log (d (i, j)) - Real.log (margL d i) - Real.log (margR d j))
            / Real.log 2) := by
    have h1 : (∑ i, ∑ j, d (i, j) * (Real.log (d (i, j)) / Real.log 2))
          - (∑ i, ∑ j, d (i, j) * (Real.log (margL d i) / Real.log 2))
        = ∑ i, ∑ j, (d (i, j) * (Real.log (d (i, j)) / Real.log 2)
            - d (i, j) * (Real.log (margL d i) / Real.log 2)) :=
      sum_sub_regroup3 (f := fun z => d z * (Real.log (d z) / Real.log 2))
        (g := fun z => d z * (Real.log (margL d z.1) / Real.log 2))
    have h2 : (∑ i, ∑ j, (d (i, j) * (Real.log (d (i, j)) / Real.log 2)
            - d (i, j) * (Real.log (margL d i) / Real.log 2)))
          - (∑ i, ∑ j, d (i, j) * (Real.log (margR d j) / Real.log 2))
        = ∑ i, ∑ j, ((d (i, j) * (Real.log (d (i, j)) / Real.log 2)
            - d (i, j) * (Real.log (margL d i) / Real.log 2))
            - d (i, j) * (Real.log (margR d j) / Real.log 2)) :=
      sum_sub_regroup3
        (f := fun z => d z * (Real.log (d z) / Real.log 2)
          - d z * (Real.log (margL d z.1) / Real.log 2))
        (g := fun z => d z * (Real.log (margR d z.2) / Real.log 2))
    rw [show (∑ i, ∑ j, d (i, j) * (Real.log (d (i, j)) / Real.log 2))
          - (∑ i, ∑ j, d (i, j) * (Real.log (margL d i) / Real.log 2))
          - (∑ i, ∑ j, d (i, j) * (Real.log (margR d j) / Real.log 2))
        = ((∑ i, ∑ j, d (i, j) * (Real.log (d (i, j)) / Real.log 2))
          - (∑ i, ∑ j, d (i, j) * (Real.log (margL d i) / Real.log 2)))
          - (∑ i, ∑ j, d (i, j) * (Real.log (margR d j) / Real.log 2)) by ring,
      h1, h2]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  calc
    mutInfo d = (-∑ i, ∑ j, d (i, j) * (Real.log (margL d i) / Real.log 2))
        + (-∑ i, ∑ j, d (i, j) * (Real.log (margR d j) / Real.log 2))
        - (-∑ i, ∑ j, d (i, j) * (Real.log (d (i, j)) / Real.log 2)) := by
          rw [hdecomp, hL, hR, hD]
    _ = (∑ i, ∑ j, d (i, j) * (Real.log (d (i, j)) / Real.log 2))
        - (∑ i, ∑ j, d (i, j) * (Real.log (margL d i) / Real.log 2))
        - (∑ i, ∑ j, d (i, j) * (Real.log (margR d j) / Real.log 2)) := by ring
    _ = ∑ i, ∑ j, d (i, j) *
        ((Real.log (d (i, j)) - Real.log (margL d i) - Real.log (margR d j))
          / Real.log 2) := hregroup

/-- For nonnegative joint weights, a cell's natural-log information contribution is at least its
joint weight minus the product of its marginal weights. -/
theorem kl_cell_ge {α β : Type} [Fintype α] [Fintype β] (d : α × β → ℝ)
    (hd : ∀ i j, 0 ≤ d (i, j)) (i : α) (j : β) :
    d (i, j) * (Real.log (d (i, j)) - Real.log (margL d i) - Real.log (margR d j))
      ≥ d (i, j) - margL d i * margR d j := by
  by_cases h0 : d (i, j) = 0
  · have hnm : 0 ≤ margL d i * margR d j := by
      have h1 : 0 ≤ margL d i := Finset.sum_nonneg fun j _ => hd i j
      have h2 : 0 ≤ margR d j := Finset.sum_nonneg fun i _ => hd i j
      exact mul_nonneg h1 h2
    simp [h0]
    linarith
  · have hdpos : 0 < d (i, j) := lt_of_le_of_ne (hd i j) (Ne.symm h0)
    have hLpos : 0 < margL d i := by
      have hle : d (i, j) ≤ margL d i := by
        unfold margL
        exact Finset.single_le_sum (f := fun j => d (i, j)) (fun j _ => hd i j)
          (Finset.mem_univ j)
      linarith
    have hRpos : 0 < margR d j := by
      have hle : d (i, j) ≤ margR d j := by
        unfold margR
        exact Finset.single_le_sum (f := fun i => d (i, j)) (fun i _ => hd i j)
          (Finset.mem_univ i)
      linarith
    have hu : 0 < margL d i * margR d j / d (i, j) := by positivity
    have hlogdiv : Real.log (margL d i * margR d j / d (i, j))
        = Real.log (margL d i) + Real.log (margR d j) - Real.log (d (i, j)) := by
      rw [Real.log_div (by positivity) (ne_of_gt hdpos)]
      rw [Real.log_mul (ne_of_gt hLpos) (ne_of_gt hRpos)]
    have hle := Real.log_le_sub_one_of_pos hu
    rw [hlogdiv] at hle
    have hcore : Real.log (d (i, j)) - Real.log (margL d i) - Real.log (margR d j)
        ≥ 1 - margL d i * margR d j / d (i, j) := by linarith
    have hmul0 := mul_le_mul_of_nonneg_left hcore (le_of_lt hdpos)
    have hsimpl : d (i, j) * (1 - margL d i * margR d j / d (i, j))
        = d (i, j) - margL d i * margR d j := by
      field_simp
    rw [hsimpl] at hmul0
    exact hmul0

/-- Mutual information is nonnegative for normalized nonnegative finite joint weights. -/
theorem mutInfo_nonneg {α β : Type} [Fintype α] [Fintype β] (d : α × β → ℝ)
    (hd : ∀ i j, 0 ≤ d (i, j)) (htot : ∑ i, ∑ j, d (i, j) = 1) :
    0 ≤ mutInfo d := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hkl := mutInfo_eq_kl d hd htot
  rw [hkl]
  have hcell : ∀ i : α, ∀ j : β,
      d (i, j) * ((Real.log (d (i, j)) - Real.log (margL d i)
        - Real.log (margR d j)) / Real.log 2)
        ≥ (d (i, j) - margL d i * margR d j) / Real.log 2 := by
    intro i j
    have h := kl_cell_ge d hd i j
    simpa [mul_div_assoc] using! (div_le_div_iff_of_pos_right hlog2).2 h
  have hsum : (∑ i, ∑ j, (d (i, j) - margL d i * margR d j) / Real.log 2) = 0 := by
    have hinner : ∀ i : α,
        (∑ j, (d (i, j) - margL d i * margR d j) / Real.log 2)
          = (∑ j, (d (i, j) - margL d i * margR d j)) / Real.log 2 := by
      intro i
      rw [Finset.sum_div]
    rw [Finset.sum_congr rfl (fun i _ => hinner i), ← Finset.sum_div]
    have hmassL : ∑ i, margL d i = 1 := by
      simpa only [margL] using! htot
    have hmassR : ∑ j, margR d j = 1 := by
      have h1 : (∑ j, ∑ i, d (i, j)) = 1 := by
        have h := htot
        rw [Finset.sum_comm] at h
        exact h
      simpa only [margR] using! h1
    have hsplit : (∑ i, ∑ j, (d (i, j) - margL d i * margR d j))
        = (∑ i, ∑ j, d (i, j)) - (∑ i, ∑ j, margL d i * margR d j) := by
      calc
        (∑ i, ∑ j, (d (i, j) - margL d i * margR d j))
            = ∑ i, ((∑ j, d (i, j)) - (∑ j, margL d i * margR d j)) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.sum_sub_distrib]
        _ = (∑ i, ∑ j, d (i, j)) - (∑ i, ∑ j, margL d i * margR d j) := by
              rw [Finset.sum_sub_distrib]
    rw [hsplit]
    have hcross : (∑ i, ∑ j, margL d i * margR d j)
        = (∑ i, margL d i) * (∑ j, margR d j) := by
      calc
        (∑ i, ∑ j, margL d i * margR d j)
            = ∑ i, margL d i * (∑ j, margR d j) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.mul_sum]
        _ = (∑ i, margL d i) * (∑ j, margR d j) := by rw [← Finset.sum_mul]
    rw [hcross, hmassL, hmassR, htot]
    simp
  have hsumle : (∑ i, ∑ j, (d (i, j) - margL d i * margR d j) / Real.log 2)
      ≤ ∑ i, ∑ j, d (i, j) *
        ((Real.log (d (i, j)) - Real.log (margL d i) - Real.log (margR d j))
          / Real.log 2) := by
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hcell i j
  rw [hsum] at hsumle
  linarith

/-- For normalized nonnegative finite joint weights, conditional entropy is at most the entropy
of the right marginal. -/
theorem condEntH_le_entH_margR {α β : Type} [Fintype α] [Fintype β] (d : α × β → ℝ)
    (hd : ∀ i j, 0 ≤ d (i, j)) (htot : ∑ i, ∑ j, d (i, j) = 1) :
    condEntH d ≤ entH (margR d) := by
  have hmut := mutInfo_eq_margR d hd
  have hnonneg := mutInfo_nonneg d hd htot
  linarith

/-- Under the stated nonnegativity and marginal identities, splits information about a pair of
transcript blocks into first-block information plus the difference of two second-block
conditional entropies. -/
theorem mutInfo_split_block {n : ℕ} {α β : Type} [Fintype α] [Fintype β]
    (d : Fin n × (α × β) → ℝ)
    (dPre : Fin n × α → ℝ)
    (dM : α × β → ℝ)
    (dPost : (Fin n × α) × β → ℝ)
    (hd : ∀ x a b, 0 ≤ d (x, (a, b)))
    (hdPre : ∀ x a, 0 ≤ dPre (x, a))
    (hdM : ∀ a b, 0 ≤ dM (a, b))
    (hdPost : ∀ z b, 0 ≤ dPost (z, b))
    (hPre : ∀ x a, dPre (x, a) = ∑ b, d (x, (a, b)))
    (hM : ∀ a b, dM (a, b) = ∑ x, d (x, (a, b)))
    (hPost : ∀ x a b, dPost ((x, a), b) = d (x, (a, b))) :
    mutInfo d = mutInfo dPre + condEntH dM - condEntH dPost := by
  have hmargrank : margL d = margL dPre := by
    funext x
    simp only [margL]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_congr rfl (fun a _ => hPre x a)]
  have hM' : ∀ (a : α) (b : β), margR d (a, b) = dM (a, b) := by
    intro a b
    rw [hM a b]
    rfl
  have hmargr : entH (margR d) = entH dM := by
    unfold entH
    congr 1
    exact Finset.sum_congr rfl (fun z _ => congrArg xlog2 (hM' z.1 z.2))
  have hpost : entH d = entH dPost := by
    have h := Fintype.sum_equiv ((Equiv.prodAssoc (Fin n) α β).symm)
      (fun z => xlog2 (d z))
      (fun z : (Fin n × α) × β => xlog2 (dPost z)) (by
        intro z
        have hz : ((Equiv.prodAssoc (Fin n) α β).symm) z = ((z.1, z.2.1), z.2.2) := rfl
        rw [hz]
        show xlog2 (d (z.1, (z.2.1, z.2.2))) = xlog2 (dPost ((z.1, z.2.1), z.2.2))
        rw [hPost z.1 z.2.1 z.2.2])
    rw [Fintype.sum_prod_type] at h
    unfold entH
    rw [Fintype.sum_prod_type]
    exact congrArg Neg.neg h
  have hmargLPost : margL dPost = dPre := by
    funext z
    simp only [margL]
    rw [Finset.sum_congr rfl (fun b _ => hPost z.1 z.2 b)]
    exact (hPre z.1 z.2).symm
  have hmargLM : margL dM = margR dPre := by
    funext a
    simp only [margL, margR]
    have h1 : (∑ b, dM (a, b)) = ∑ b, ∑ x, d (x, (a, b)) :=
      Finset.sum_congr rfl (fun b _ => hM a b)
    have h2 : (∑ x, dPre (x, a)) = ∑ x, ∑ b, d (x, (a, b)) :=
      Finset.sum_congr rfl (fun x _ => hPre x a)
    rw [h1, h2]
    exact Finset.sum_comm
  have hchainPost : entH dPost = entH dPre + condEntH dPost := by
    have hh := entH_chain_rule dPost hdPost
    rw [hmargLPost] at hh
    exact hh
  have hchainM : entH dM = entH (margR dPre) + condEntH dM := by
    have hh := entH_chain_rule dM hdM
    rw [hmargLM] at hh
    exact hh
  have hchainPre : entH dPre = entH (margL dPre) + condEntH dPre := by
    have hh := entH_chain_rule dPre hdPre
    exact hh
  have hchainCond : condEntH d = condEntH dPre + condEntH dPost := by
    have h1 := entH_chain_rule d (fun i j => hd i j.1 j.2)
    have h2 := hchainPost
    have h3 := hchainPre
    have h4 : entH (margL d) = entH (margL dPre) := by rw [hmargrank]
    have h5 : entH d = entH dPost := hpost
    linarith
  have hmutPre : mutInfo dPre = entH (margR dPre) - condEntH dPre :=
    mutInfo_eq_margR dPre hdPre
  have hmutD : mutInfo d = entH (margR d) - condEntH d :=
    mutInfo_eq_margR d (fun i j => hd i j.1 j.2)
  rw [hmutD, hmutPre]
  rw [hmargr]
  linarith

/-- The factorization identity `d (x, (a, b)) * margL dX x = dX (x, b) * dPre (x, a)` for all
cells and block values, expressing conditional independence when the weights form the
corresponding joint laws. -/
def CondIndepRight {n : ℕ} {α β : Type} [Fintype α] [Fintype β]
    (d : Fin n × (α × β) → ℝ) (dX : Fin n × β → ℝ) (dPre : Fin n × α → ℝ) : Prop :=
  ∀ x a b, d (x, (a, b)) * margL dX x = dX (x, b) * dPre (x, a)

/-- Under the stated nonnegativity, marginal, and `CondIndepRight` hypotheses, conditioning the
right block on both the hidden cell and the first block gives the same conditional entropy
as conditioning on the hidden cell alone. -/
theorem condEntH_eq_under_cond_indep {n : ℕ} {α β : Type} [Fintype α] [Fintype β]
    (d : Fin n × (α × β) → ℝ) (dX : Fin n × β → ℝ) (dPre : Fin n × α → ℝ)
    (dPost : (Fin n × α) × β → ℝ)
    (_hd : ∀ x a b, 0 ≤ d (x, (a, b)))
    (hdX : ∀ x b, 0 ≤ dX (x, b))
    (hdPre : ∀ x a, 0 ≤ dPre (x, a))
    (hdPost : ∀ z b, 0 ≤ dPost (z, b))
    (hPre : ∀ x a, dPre (x, a) = ∑ b, d (x, (a, b)))
    (hX : ∀ x b, dX (x, b) = ∑ a, d (x, (a, b)))
    (hPost : ∀ x a b, dPost ((x, a), b) = d (x, (a, b)))
    (hci : CondIndepRight d dX dPre) :
    condEntH dPost = condEntH dX := by
  have hmargPre : ∀ x a, margL dPost (x, a) = dPre (x, a) := by
    intro x a
    simp only [margL]
    rw [Finset.sum_congr rfl (fun b _ => hPost x a b)]
    exact (hPre x a).symm
  have hmargX : ∀ x, margL dX x = ∑ a, dPre (x, a) := by
    intro x
    simp only [margL]
    rw [Finset.sum_congr rfl (fun b _ => hX x b)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun a _ => hPre x a)]
  have hslot : ∀ x : Fin n, ∀ a : α,
      dPre (x, a) * entH (fun b => condW dPost (x, a) b)
        = dPre (x, a) * entH (fun b => condW dX x b) := by
    intro x a
    by_cases hz : dPre (x, a) = 0
    · simp [hz]
    · have hmX : margL dX x ≠ 0 := by
        have h1 : margL dX x = ∑ a, dPre (x, a) := hmargX x
        have h2 : 0 < dPre (x, a) := lt_of_le_of_ne (hdPre x a) (Ne.symm hz)
        have h3 : 0 < ∑ a, dPre (x, a) :=
          Finset.sum_pos' (fun a _ => hdPre x a) ⟨a, Finset.mem_univ a, h2⟩
        have h3' : margL dX x ≠ 0 := by
          rw [h1]
          exact h3.ne'
        exact h3'
      have hnePre : margL dPost (x, a) ≠ 0 := by
        rw [hmargPre x a]
        exact hz
      have hcw : condW dPost (x, a) = condW dX x := by
        funext b
        simp only [condW, dif_neg hnePre, dif_neg hmX]
        rw [hmargPre x a, hPost x a b]
        have hden1 : dPre (x, a) ≠ 0 := hz
        have hden2 : margL dX x ≠ 0 := hmX
        apply (div_eq_iff hden1).2
        rw [div_mul_eq_mul_div]
        apply (eq_div_iff hden2).2
        exact hci x a b
      rw [hcw]
  have h1 := condEntH_eq_sum dPost hdPost
  have h2 := condEntH_eq_sum dX hdX
  rw [h1, h2]
  have hcell : ∀ x : Fin n,
      (∑ a, margL dPost (x, a) * entH (fun b => condW dPost (x, a) b))
        = margL dX x * entH (fun b => condW dX x b) := by
    intro x
    calc
      (∑ a, margL dPost (x, a) * entH (fun b => condW dPost (x, a) b))
          = ∑ a, dPre (x, a) * entH (fun b => condW dPost (x, a) b) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [hmargPre x a]
      _ = ∑ a, dPre (x, a) * entH (fun b => condW dX x b) := by
            apply Finset.sum_congr rfl
            intro a ha
            exact hslot x a
      _ = (∑ a, dPre (x, a)) * entH (fun b => condW dX x b) := by
            rw [Finset.sum_mul]
      _ = margL dX x * entH (fun b => condW dX x b) := by
            rw [hmargX x]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl (fun x _ => hcell x)]

/-- For the stated nonnegative joint and marginal weights with the required normalization and
conditional independence, information about both blocks is at most the sum of the separate
block informations. -/
theorem mutInfo_le_sum_blocks {n : ℕ} {α β : Type} [Fintype α] [Fintype β]
    (d : Fin n × (α × β) → ℝ) (dPre : Fin n × α → ℝ) (dM : α × β → ℝ)
    (dPost : (Fin n × α) × β → ℝ) (dX : Fin n × β → ℝ)
    (hd : ∀ x a b, 0 ≤ d (x, (a, b)))
    (hdPre : ∀ x a, 0 ≤ dPre (x, a))
    (hdM : ∀ a b, 0 ≤ dM (a, b))
    (hdPost : ∀ z b, 0 ≤ dPost (z, b))
    (hdX : ∀ x b, 0 ≤ dX (x, b))
    (hPre : ∀ x a, dPre (x, a) = ∑ b, d (x, (a, b)))
    (hM : ∀ a b, dM (a, b) = ∑ x, d (x, (a, b)))
    (hPost : ∀ x a b, dPost ((x, a), b) = d (x, (a, b)))
    (hX : ∀ x b, dX (x, b) = ∑ a, d (x, (a, b)))
    (_htot : ∑ x, ∑ y : α × β, d (x, y) = 1)
    (htotM : ∑ y : α × β, dM y = 1)
    (hci : CondIndepRight d dX dPre) :
    mutInfo d ≤ mutInfo dPre + mutInfo dX := by
  have hchain := mutInfo_split_block d dPre dM dPost hd hdPre hdM hdPost hPre hM hPost
  have hci' := condEntH_eq_under_cond_indep d dX dPre dPost hd hdX hdPre hdPost hPre hX
    hPost hci
  have htotM' : (∑ a, ∑ b, dM (a, b)) = 1 := by
    rw [← Fintype.sum_prod_type]
    exact htotM
  have hle := condEntH_le_entH_margR dM hdM htotM'
  have hmutX : mutInfo dX = entH (margR dX) - condEntH dX :=
    mutInfo_eq_margR dX hdX
  have hmargR : margR dM = margR dX := by
    funext b
    simp only [margR]
    have h1 : (∑ a, dM (a, b)) = ∑ a, ∑ x, d (x, (a, b)) :=
      Finset.sum_congr rfl (fun a _ => hM a b)
    have h2 : (∑ x, dX (x, b)) = ∑ x, ∑ a, d (x, (a, b)) :=
      Finset.sum_congr rfl (fun x _ => hX x b)
    rw [h1, h2]
    exact Finset.sum_comm
  rw [hchain, hci']
  rw [hmutX]
  have hle' : condEntH dM ≤ entH (margR dX) := by
    rw [← hmargR]
    exact hle
  linarith

/-- The joint weights of a uniform hidden cell and two binary transcripts, formed as `1 / n`
times the product of their conditional likelihoods. -/
noncomputable def twoLevelJointLaw {n k₁ k₂ : ℕ} (prog₁ : BscProgram n k₁)
    (prog₂ : BscProgram n k₂) (p : ℝ) : Fin n × ((Fin k₁ → Bool) × (Fin k₂ → Bool)) → ℝ :=
  fun z => (1 / (n : ℝ)) * bscLikPre prog₁.cuts p z.1 z.2.1 * bscLikPre prog₂.cuts p z.1 z.2.2

/-- The joint law of the hidden cell and the first binary program's transcript, using the
uniform prior. -/
noncomputable def twoLevelMargL {n k₁ k₂ : ℕ} (prog₁ : BscProgram n k₁)
    (_prog₂ : BscProgram n k₂) (p : ℝ) : Fin n × (Fin k₁ → Bool) → ℝ :=
  bscJointLaw prog₁.cuts p

/-- The joint law of the hidden cell and the second binary program's transcript, using the
uniform prior. -/
noncomputable def twoLevelMargR {n k₁ k₂ : ℕ} (_prog₁ : BscProgram n k₁)
    (prog₂ : BscProgram n k₂) (p : ℝ) : Fin n × (Fin k₂ → Bool) → ℝ :=
  bscJointLaw prog₂.cuts p

/-- For `0 ≤ p ≤ 1` and `n > 0`, the two-level transcript joint law satisfies the
conditional-independence factorization with its two hidden-cell transcript laws. -/
theorem clause17_two_level_cond_indep {n k₁ k₂ : ℕ} (prog₁ : BscProgram n k₁)
    (prog₂ : BscProgram n k₂) (p : ℝ) (_hp0 : 0 ≤ p) (_hp1 : p ≤ 1) (hn : 0 < n)
    (x : Fin n) (y₁ : Fin k₁ → Bool) (y₂ : Fin k₂ → Bool) :
    twoLevelJointLaw prog₁ prog₂ p (x, (y₁, y₂)) * margL (twoLevelMargR prog₁ prog₂ p) x
      = twoLevelMargR prog₁ prog₂ p (x, y₂) * twoLevelMargL prog₁ prog₂ p (x, y₁) := by
  have hsum : ∑ y₂, bscLikPre prog₂.cuts p x y₂ = 1 := bscLikPre_sum_one prog₂.cuts p x
  have hmarg : margL (twoLevelMargR prog₁ prog₂ p) x = 1 / (n : ℝ) := by
    simp only [twoLevelMargR, bscJointLaw, bscJointCuts, margL]
    have h1 : (∑ y₂, (1 / (n : ℝ)) * bscLikPre prog₂.cuts p x y₂)
        = (1 / (n : ℝ)) * (∑ y₂, bscLikPre prog₂.cuts p x y₂) := by
      rw [← Finset.mul_sum]
    rw [h1, hsum]
    field_simp
  rw [hmarg]
  simp only [twoLevelJointLaw, twoLevelMargL, twoLevelMargR, bscJointLaw, bscJointCuts]
  ring

open scoped BigOperators Classical ENNReal NNReal
open Qatlib
open Qatlib.Concepts.OrderedBayes.BayesRatioCore
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels.OrderedSearch2007

/-- A unit-valued right variable has zero mutual information under normalized nonnegative joint
weights. -/
theorem clause17_mutInfo_unit_right {n : ℕ} (d : Fin n × Unit → ℝ) (hd : ∀ x, 0 ≤ d (x, ()))
    (ht : (∑ x, d (x, ())) = 1) :
    mutInfo d = 0 := by
  have hml : ∀ x, margL d x = d (x, ()) := by
    intro x
    show (∑ j : Unit, d (x, j)) = d (x, ())
    rw [Fintype.sum_unique]
  have hcw : ∀ x, condW d x () = if d (x, ()) = 0 then 0 else 1 := by
    intro x
    rw [condW, hml x]
    by_cases h : d (x, ()) = 0
    · simp [h]
    · simp [h]
  have hent : ∀ x, entH (fun j => condW d x j) = 0 := by
    intro x
    by_cases h : d (x, ()) = 0
    · simp [entH, xlog2, hcw x, h]
    · simp [entH, xlog2, hcw x, h]
  have hcond : condEntH d = 0 := by
    rw [condEntH_eq_sum d (fun i _ => hd i)]
    simp only [hent]
    simp
  have hmr : margR d () = 1 := by
    simp only [margR]
    rw [ht]
  have hentR : entH (margR d) = 0 := by
    simp [entH, xlog2, hmr]
  rw [mutInfo_eq_margR d (fun i _ => hd i), hentR, hcond]
  ring

/-- The used-transcript joint weight factors as the uniform hidden-cell weight `1 / n` times its
conditional used-transcript weight. -/
theorem clause17_stop_used_cond_eq {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ) (x : Fin n)
    (e : Fin k → (Sum Bool Unit)) :
    stopUsedJoint prog p x e = (1 / (n : ℝ)) * stopUsedCond prog p x e := by
  unfold stopUsedJoint stopUsedCond bscJointCuts stopPadEq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- For `0 ≤ p ≤ 1` and `n > 0`, the conditional used-transcript weights sum to one for each
hidden cell. -/
theorem clause17_stop_used_cond_sum_one {n k : ℕ} (prog : BscStopProgram n k) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n) (x : Fin n) :
    (∑ e : Fin k → (Sum Bool Unit), stopUsedCond prog p x e) = 1 := by
  have h1 : (∑ e : Fin k → (Sum Bool Unit), stopUsedJoint prog p x e)
      = (1 / (n : ℝ)) * (∑ e : Fin k → (Sum Bool Unit), stopUsedCond prog p x e) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [clause17_stop_used_cond_eq]
  have h2 := clause17_stop_used_joint_margL prog hp0 hp1 hn x
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hne : (1 / (n : ℝ)) ≠ 0 := by
    exact div_ne_zero (by norm_num) hn0
  have h3 : (∑ e : Fin k → (Sum Bool Unit), stopUsedCond prog p x e) * (1 / (n : ℝ))
      = 1 * (1 / (n : ℝ)) := by
    have h4 : (1 / (n : ℝ)) * (∑ e : Fin k → (Sum Bool Unit), stopUsedCond prog p x e)
        = 1 / (n : ℝ) := by
      rw [← h1, h2]
    calc (∑ e : Fin k → (Sum Bool Unit), stopUsedCond prog p x e) * (1 / (n : ℝ))
        = (1 / (n : ℝ)) * (∑ e : Fin k → (Sum Bool Unit), stopUsedCond prog p x e) := mul_comm _ _
      _ = 1 / (n : ℝ) := h4
      _ = 1 * (1 / (n : ℝ)) := (one_mul _).symm
  exact (mul_right_cancel₀ hne h3)

/-- The likelihood mass of a used-transcript tower extended by one level factors into its
previous tower likelihood and the new level's conditional used-transcript weight. -/
theorem clause17_rec_lik_fibre_succ {n k : ℕ} (prog : RecBscProgram n k) (p : ℝ) (L : ℕ)
    (x : Fin n) (e : RecTower n k L) (b : Fin k → (Sum Bool Unit)) :
    recLikFibre prog p (L + 1) x (e, b)
      = recLikFibre prog p L x e * stopUsedCond (prog.levelProg L) p x b := by
  have hpad : ∀ (y1 : RecRawTower n k L) (y2 : Fin k → Bool),
      recPadTower prog (L + 1) (y1, y2)
        = (recPadTower prog L y1, stopPad (prog.levelProg L) y2) := by
    intro y1 y2
    rfl
  have hlik : ∀ (y1 : RecRawTower n k L) (y2 : Fin k → Bool),
      recLikTower prog p (L + 1) x (y1, y2)
        = recLikTower prog p L x y1 * bscLikPre (prog.levelProg L).cuts p x y2 := by
    intro y1 y2
    rfl
  have hpoint : ∀ (y1 : RecRawTower n k L) (y2 : Fin k → Bool),
      recLikTower prog p (L + 1) x (y1, y2) * recPadEq prog (L + 1) (y1, y2) (e, b)
        = (recLikTower prog p L x y1 * recPadEq prog L y1 e)
          * (bscLikPre (prog.levelProg L).cuts p x y2
            * stopPadEq (prog.levelProg L) y2 b) := by
    intro y1 y2
    rw [hlik]
    simp only [recPadEq, stopPadEq]
    rw [hpad y1 y2]
    by_cases h : (recPadTower prog L y1, stopPad (prog.levelProg L) y2) = (e, b)
    · have h1 : recPadTower prog L y1 = e := (Prod.ext_iff.mp h).1
      have h2 : stopPad (prog.levelProg L) y2 = b := (Prod.ext_iff.mp h).2
      simp [h1, h2]
    · by_cases hA : recPadTower prog L y1 = e
      · have hB : stopPad (prog.levelProg L) y2 ≠ b := by
          intro hB
          exact h (Prod.ext_iff.mpr ⟨hA, hB⟩)
        have hpair : (e, stopPad (prog.levelProg L) y2) ≠ (e, b) := by
          intro hcon
          exact hB (Prod.ext_iff.mp hcon).2
        simp [hA, hB, hpair]
      · simp [h, hA]
  unfold recLikFibre
  rw [Fintype.sum_prod_type]
  calc (∑ x_1 : RecRawTower n k L, ∑ x_2 : Fin k → Bool,
        recLikTower prog p (L + 1) x (x_1, x_2) * recPadEq prog (L + 1) (x_1, x_2) (e, b))
      = ∑ x_1 : RecRawTower n k L, ∑ x_2 : Fin k → Bool,
        (recLikTower prog p L x x_1 * recPadEq prog L x_1 e)
          * (bscLikPre (prog.levelProg L).cuts p x x_2 * stopPadEq (prog.levelProg L) x_2 b) := by
        simp_rw [hpoint]
    _ = ∑ x_1 : RecRawTower n k L,
        (recLikTower prog p L x x_1 * recPadEq prog L x_1 e)
          * (∑ x_2 : Fin k → Bool,
            bscLikPre (prog.levelProg L).cuts p x x_2 * stopPadEq (prog.levelProg L) x_2 b) := by
        apply Finset.sum_congr rfl
        intro x_1 _
        rw [Finset.mul_sum]
    _ = (∑ x_1 : RecRawTower n k L, recLikTower prog p L x x_1 * recPadEq prog L x_1 e)
        * (∑ x_2 : Fin k → Bool,
          bscLikPre (prog.levelProg L).cuts p x x_2 * stopPadEq (prog.levelProg L) x_2 b) := by
        rw [Finset.sum_mul]
    _ = recLikFibre prog p L x e * stopUsedCond (prog.levelProg L) p x b := by
      unfold recLikFibre stopUsedCond
      have e1 : (∑ x_1 : RecRawTower n k L,
            recLikTower prog p L x x_1 * recPadEq prog L x_1 e)
          = (∑ y : RecRawTower n k L,
            recLikTower prog p L x y * recPadEq prog L y e) := rfl
      have e2 : (∑ x_2 : Fin k → Bool,
            bscLikPre (prog.levelProg L).cuts p x x_2 * stopPadEq (prog.levelProg L) x_2 b)
          = (∑ y : Fin k → Bool,
            bscLikPre (prog.levelProg L).cuts p x y * stopPadEq (prog.levelProg L) y b) := rfl
      rw [e1, e2]

/-- The recursive likelihood fibre equals the product of the conditional used-transcript weights
across levels. -/
theorem clause17_rec_lik_fibre_eq_prod {n k : ℕ} (prog : RecBscProgram n k) (p : ℝ) (L : ℕ)
    (x : Fin n) (e : RecTower n k L) :
    recLikFibre prog p L x e = recUsedTowerProd prog p L x e := by
  induction L with
  | zero =>
    have he : e = () := Subsingleton.elim e ()
    subst he
    simp [recLikFibre, recLikTower, recPadTower, recUsedTowerProd, recPadEq]
  | succ L ih =>
    obtain ⟨e1, e2⟩ := e
    rw [clause17_rec_lik_fibre_succ, ih]
    rfl

/-- The recursive used-transcript joint weight equals `1 / n` times its likelihood fibre. -/
theorem clause17_rec_used_joint_law_eq_fibre {n k : ℕ} (prog : RecBscProgram n k) (p : ℝ) (L : ℕ)
    (x : Fin n) (e : RecTower n k L) :
    recUsedJointLaw prog p L (x, e) = (1 / (n : ℝ)) * recLikFibre prog p L x e := by
  unfold recUsedJointLaw recRawJointLaw recLikFibre
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- The recursive used-transcript joint weight equals `1 / n` times the product of its levelwise
conditional weights. -/
theorem clause17_rec_used_joint_law_eq_prod {n k : ℕ} (prog : RecBscProgram n k) (p : ℝ) (L : ℕ)
    (x : Fin n) (e : RecTower n k L) :
    recUsedJointLaw prog p L (x, e) = (1 / (n : ℝ)) * recUsedTowerProd prog p L x e := by
  rw [clause17_rec_used_joint_law_eq_fibre, clause17_rec_lik_fibre_eq_prod]

/-- Conditional used-transcript weights are nonnegative when `0 ≤ p ≤ 1`. -/
theorem clause17_stop_used_cond_nonneg {n k : ℕ} (prog : BscStopProgram n k) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : Fin n) (e : Fin k → (Sum Bool Unit)) :
    0 ≤ stopUsedCond prog p x e := by
  unfold stopUsedCond
  apply Finset.sum_nonneg
  intro y _
  apply mul_nonneg
  · exact bscLikPre_nonneg prog.cuts p hp0 hp1 x y
  · unfold stopPadEq
    split <;> norm_num

/-- Products of conditional used-transcript weights over recursive levels are nonnegative when
`0 ≤ p ≤ 1`. -/
theorem clause17_rec_used_tower_prod_nonneg {n k : ℕ} (prog : RecBscProgram n k) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ (L : ℕ) (x : Fin n) (e : RecTower n k L), 0 ≤ recUsedTowerProd prog p L x e := by
  intro L
  induction L with
  | zero =>
    intro x e
    simp [recUsedTowerProd]
  | succ L ih =>
    intro x e
    obtain ⟨e1, e2⟩ := e
    simp only [recUsedTowerProd]
    exact mul_nonneg (ih x e1) (clause17_stop_used_cond_nonneg (prog.levelProg L) hp0 hp1 x e2)

/-- Recursive used-transcript joint weights are nonnegative for `0 ≤ p ≤ 1` and `n > 0`. -/
theorem clause17_rec_used_joint_nonneg {n k : ℕ} (prog : RecBscProgram n k) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n) (L : ℕ) (x : Fin n) (e : RecTower n k L) :
    0 ≤ recUsedJointLaw prog p L (x, e) := by
  have h := clause17_rec_used_joint_law_eq_prod prog p L x e
  rw [h]
  exact mul_nonneg (by positivity) (clause17_rec_used_tower_prod_nonneg prog hp0 hp1 L x e)

/-- For `0 ≤ p ≤ 1` and `n > 0`, the products of conditional level weights sum to one over all
used-transcript towers for each hidden cell. -/
theorem clause17_rec_used_tower_prod_sum_one {n k : ℕ} (prog : RecBscProgram n k) (p : ℝ) (L : ℕ)
    (x : Fin n) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n) :
    (∑ e : RecTower n k L, recUsedTowerProd prog p L x e) = 1 := by
  induction L with
  | zero =>
    simp [recUsedTowerProd]
  | succ L ih =>
    rw [Fintype.sum_prod_type]
    calc (∑ e : RecTower n k L, ∑ b : Fin k → (Sum Bool Unit),
        recUsedTowerProd prog p (L + 1) x (e, b))
        = ∑ e : RecTower n k L,
            recUsedTowerProd prog p L x e
              * (∑ b : Fin k → (Sum Bool Unit), stopUsedCond (prog.levelProg L) p x b) := by
          apply Finset.sum_congr rfl
          intro e _
          simp only [recUsedTowerProd]
          rw [Finset.mul_sum]
      _ = (∑ e : RecTower n k L, recUsedTowerProd prog p L x e)
          * (∑ b : Fin k → (Sum Bool Unit), stopUsedCond (prog.levelProg L) p x b) := by
          rw [Finset.sum_mul]
      _ = 1 := by
          rw [ih, clause17_stop_used_cond_sum_one (prog.levelProg L) hp0 hp1 hn x]
          simp

/-- For `0 ≤ p ≤ 1` and `n > 0`, summing the recursive joint law over the last level's used
transcript recovers the previous tower joint law. -/
theorem clause17_rec_used_marg_last {n k : ℕ} (prog : RecBscProgram n k) (p : ℝ) (L : ℕ)
    (x : Fin n) (e : RecTower n k L) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n) :
    (∑ b : Fin k → (Sum Bool Unit), recUsedJointLaw prog p (L + 1) (x, (e, b)))
      = recUsedJointLaw prog p L (x, e) := by
  have h1 : (∑ b : Fin k → (Sum Bool Unit), recUsedJointLaw prog p (L + 1) (x, (e, b)))
      = ∑ b : Fin k → (Sum Bool Unit),
        (1 / (n : ℝ)) * recUsedTowerProd prog p L x e * stopUsedCond (prog.levelProg L) p x b := by
    apply Finset.sum_congr rfl
    intro b _
    have h := clause17_rec_used_joint_law_eq_prod prog p (L + 1) x (e, b)
    rw [h]
    simp only [recUsedTowerProd]
    ring
  rw [h1]
  rw [← Finset.mul_sum]
  rw [clause17_stop_used_cond_sum_one (prog.levelProg L) hp0 hp1 hn x]
  have h := clause17_rec_used_joint_law_eq_prod prog p L x e
  rw [← h]
  ring

/-- For `0 ≤ p ≤ 1` and `n > 0`, summing out all preceding tower levels gives the joint law of
the hidden cell and the last level's used transcript. -/
theorem clause17_rec_used_marg_head {n k : ℕ} (prog : RecBscProgram n k) (p : ℝ) (L : ℕ)
    (x : Fin n) (b : Fin k → (Sum Bool Unit)) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n) :
    (∑ a : RecTower n k L, recUsedJointLaw prog p (L + 1) (x, (a, b)))
      = stopUsedJoint (prog.levelProg L) p x b := by
  have h1 : (∑ a : RecTower n k L, recUsedJointLaw prog p (L + 1) (x, (a, b)))
      = ∑ a : RecTower n k L,
        (1 / (n : ℝ)) * stopUsedCond (prog.levelProg L) p x b * recUsedTowerProd prog p L x a := by
    apply Finset.sum_congr rfl
    intro a _
    have h := clause17_rec_used_joint_law_eq_prod prog p (L + 1) x (a, b)
    rw [h]
    simp only [recUsedTowerProd]
    ring
  rw [h1]
  rw [← Finset.mul_sum]
  rw [clause17_rec_used_tower_prod_sum_one prog p L x hp0 hp1 hn]
  have h := clause17_stop_used_cond_eq (prog.levelProg L) p x b
  rw [h]
  ring

/-- For `0 ≤ p ≤ 1` and `n > 0`, the hidden-cell marginal of the recursive used-transcript law
equals `1 / n`. -/
theorem clause17_rec_used_margL {n k : ℕ} (prog : RecBscProgram n k) (p : ℝ) (L : ℕ)
    (x : Fin n) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n) :
    (∑ e : RecTower n k L, recUsedJointLaw prog p L (x, e)) = 1 / (n : ℝ) := by
  have h1 : (∑ e : RecTower n k L, recUsedJointLaw prog p L (x, e))
      = ∑ e : RecTower n k L, (1 / (n : ℝ)) * recUsedTowerProd prog p L x e := by
    apply Finset.sum_congr rfl
    intro e _
    exact clause17_rec_used_joint_law_eq_prod prog p L x e
  rw [h1]
  rw [← Finset.mul_sum]
  rw [clause17_rec_used_tower_prod_sum_one prog p L x hp0 hp1 hn]
  ring

/-- Recursive used-transcript joint weights sum to one for `0 ≤ p ≤ 1` and `n > 0`. -/
theorem clause17_rec_used_total {n k : ℕ} (prog : RecBscProgram n k) (p : ℝ) (L : ℕ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n) :
    (∑ x : Fin n, ∑ e : RecTower n k L, recUsedJointLaw prog p L (x, e)) = 1 := by
  calc (∑ x : Fin n, ∑ e : RecTower n k L, recUsedJointLaw prog p L (x, e))
      = ∑ x : Fin n, 1 / (n : ℝ) := by
        apply Finset.sum_congr rfl
        intro x _
        exact clause17_rec_used_margL prog p L x hp0 hp1 hn
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        simp
        field_simp

/-- For `0 ≤ p ≤ 1` and `n > 0`, the previous used-transcript tower and the next level's used
transcript satisfy `CondIndepRight` given the hidden cell. -/
theorem clause17_rec_cond_indep {n k : ℕ} (prog : RecBscProgram n k) (p : ℝ) (L : ℕ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n) :
    @CondIndepRight n (RecTower n k L) (Fin k → (Sum Bool Unit))
      (inferInstanceAs (Fintype (RecTower n k L)))
      (inferInstanceAs (Fintype (Fin k → (Sum Bool Unit))))
      (recUsedJointLaw prog p (L + 1)) (stopUsedJointLaw (prog.levelProg L) p)
      (recUsedJointLaw prog p L) := by
  intro x a b
  have h1 := clause17_rec_used_joint_law_eq_prod prog p (L + 1) x (a, b)
  have h2 := clause17_stop_used_cond_eq (prog.levelProg L) p x b
  have h3 := clause17_rec_used_joint_law_eq_prod prog p L x a
  have h4 := clause17_stop_used_joint_margL (prog.levelProg L) hp0 hp1 hn x
  simp only [recUsedTowerProd] at h1
  simp only [stopUsedJointLaw, margL]
  rw [h1, h2, h3, h4]
  ring

/-- For `0 ≤ p ≤ 1` and `n > 0`, extending a tower by one level increases mutual information by
at most that level's used-transcript information. -/
theorem clause17_rec_used_mut_info_step {n k : ℕ} (prog : RecBscProgram n k) (p : ℝ) (L : ℕ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n) :
    recUsedMutInfo prog p (L + 1)
      ≤ recUsedMutInfo prog p L + stopUsedMutInfo (prog.levelProg L) p := by
  have hd : ∀ (x : Fin n) (a : RecTower n k L) (b : Fin k → (Sum Bool Unit)),
      0 ≤ recUsedJointLaw prog p (L + 1) (x, (a, b)) :=
    fun x a b => clause17_rec_used_joint_nonneg prog hp0 hp1 hn (L + 1) x (a, b)
  have hdPre : ∀ (x : Fin n) (a : RecTower n k L),
      0 ≤ recUsedJointLaw prog p L (x, a) :=
    fun x a => clause17_rec_used_joint_nonneg prog hp0 hp1 hn L x a
  have hdX : ∀ (x : Fin n) (b : Fin k → (Sum Bool Unit)),
      0 ≤ stopUsedJoint (prog.levelProg L) p x b :=
    fun x b => clause17_stop_used_joint_nonneg (prog.levelProg L) hp0 hp1 hn x b
  have hPre : ∀ (x : Fin n) (a : RecTower n k L),
      recUsedJointLaw prog p L (x, a)
        = ∑ b : Fin k → (Sum Bool Unit), recUsedJointLaw prog p (L + 1) (x, (a, b)) := by
    intro x a
    exact (clause17_rec_used_marg_last prog p L x a hp0 hp1 hn).symm
  have hX : ∀ (x : Fin n) (b : Fin k → (Sum Bool Unit)),
      stopUsedJoint (prog.levelProg L) p x b
        = ∑ a : RecTower n k L, recUsedJointLaw prog p (L + 1) (x, (a, b)) := by
    intro x b
    exact (clause17_rec_used_marg_head prog p L x b hp0 hp1 hn).symm
  have htot : (∑ x : Fin n, ∑ y : RecTower n k L × (Fin k → (Sum Bool Unit)),
      recUsedJointLaw prog p (L + 1) (x, y)) = 1 := by
    calc (∑ x : Fin n, ∑ y : RecTower n k L × (Fin k → (Sum Bool Unit)),
        recUsedJointLaw prog p (L + 1) (x, y))
        = ∑ x : Fin n, ∑ a : RecTower n k L,
            ∑ b : Fin k → (Sum Bool Unit), recUsedJointLaw prog p (L + 1) (x, (a, b)) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Fintype.sum_prod_type (f := fun z => recUsedJointLaw prog p (L + 1) (x, z))]
      _ = ∑ x : Fin n, ∑ a : RecTower n k L, recUsedJointLaw prog p L (x, a) := by
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro a _
          exact clause17_rec_used_marg_last prog p L x a hp0 hp1 hn
      _ = ∑ x : Fin n, 1 / (n : ℝ) := by
          apply Finset.sum_congr rfl
          intro x _
          exact clause17_rec_used_margL prog p L x hp0 hp1 hn
      _ = 1 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          simp
          field_simp
  have htotM : (∑ y : RecTower n k L × (Fin k → (Sum Bool Unit)),
      (∑ x : Fin n, recUsedJointLaw prog p (L + 1) (x, y))) = 1 := by
    calc (∑ y : RecTower n k L × (Fin k → (Sum Bool Unit)),
        (∑ x : Fin n, recUsedJointLaw prog p (L + 1) (x, y)))
        = ∑ x : Fin n, ∑ y : RecTower n k L × (Fin k → (Sum Bool Unit)),
            recUsedJointLaw prog p (L + 1) (x, y) := by
          rw [Finset.sum_comm]
      _ = 1 := htot
  have h := mutInfo_le_sum_blocks (α := RecTower n k L) (β := Fin k → (Sum Bool Unit))
    (recUsedJointLaw prog p (L + 1))
    (recUsedJointLaw prog p L)
    (fun z => ∑ x : Fin n, recUsedJointLaw prog p (L + 1) (x, z))
    (fun z : (Fin n × RecTower n k L) × (Fin k → (Sum Bool Unit)) =>
      recUsedJointLaw prog p (L + 1)
        (Prod.fst (Prod.fst z), (Prod.snd (Prod.fst z), Prod.snd z)))
    (stopUsedJointLaw (prog.levelProg L) p)
    (fun x a b => hd x a b) hdPre
    (fun a b => Finset.sum_nonneg fun x _ => hd x a b)
    (fun z b => hd (Prod.fst z) (Prod.snd z) b) hdX hPre
    (fun a b => rfl)
    (fun x a b => rfl) hX htot htotM
    (clause17_rec_cond_indep prog p L hp0 hp1 hn)
  exact h

/-- For `0 ≤ p ≤ 1` and `n > 0`, the recursive used-transcript information is at most the sum of
the individual levels' used-transcript informations. -/
theorem clause17_rec_used_mut_info_le_sum_levels {n k : ℕ} (prog : RecBscProgram n k) (p : ℝ) (L : ℕ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 0 < n) :
    recUsedMutInfo prog p L ≤ ∑ L' ∈ Finset.range L, stopUsedMutInfo (prog.levelProg L') p := by
  induction L with
  | zero =>
    have h0 : recUsedMutInfo prog p 0 = 0 := by
      unfold recUsedMutInfo
      refine clause17_mutInfo_unit_right (fun z => recUsedJointLaw prog p 0 (z.1, z.2)) ?_ ?_
      · intro x
        exact clause17_rec_used_joint_nonneg prog hp0 hp1 hn 0 x ()
      · have h := clause17_rec_used_total prog p 0 hp0 hp1 hn
        simpa using! h
    rw [h0]
    simp
  | succ L ih =>
    have hstep := clause17_rec_used_mut_info_step prog p L hp0 hp1 hn
    calc recUsedMutInfo prog p (L + 1)
        ≤ recUsedMutInfo prog p L + stopUsedMutInfo (prog.levelProg L) p := hstep
      _ ≤ (∑ L' ∈ Finset.range L, stopUsedMutInfo (prog.levelProg L') p)
          + stopUsedMutInfo (prog.levelProg L) p := add_le_add_left ih _
      _ = ∑ L' ∈ Finset.range (L + 1), stopUsedMutInfo (prog.levelProg L') p := by
          rw [Finset.sum_range_succ]

/-- For `1 / 2 < p ≤ 1` and `n > 0`, recursive used-transcript information is at most the sum of
levelwise expected stopping costs times `queryInfo p`. -/
theorem clause17_rec_used_mut_info_le_total_cost {n k : ℕ} (prog : RecBscProgram n k) (p : ℝ) (L : ℕ)
    (hp : 1 / 2 < p) (hp1 : p ≤ 1) (hn : 0 < n) :
    recUsedMutInfo prog p L
      ≤ (∑ L' ∈ Finset.range L, expectedStopCost (prog.levelProg L') p) * queryInfo p := by
  have hp0 : 0 ≤ p := by linarith
  have h1 := clause17_rec_used_mut_info_le_sum_levels prog p L hp0 hp1 hn
  have h2 : ∀ L' ∈ Finset.range L,
      stopUsedMutInfo (prog.levelProg L') p
        ≤ expectedStopCost (prog.levelProg L') p * queryInfo p :=
    fun L' _ => clause17_stop_used_mut_info_le (prog.levelProg L') p hp hp1 hn
  have hqi : 0 ≤ queryInfo p := le_of_lt (clause17_queryInfo_pos_of hp hp1)
  calc recUsedMutInfo prog p L
      ≤ ∑ L' ∈ Finset.range L, stopUsedMutInfo (prog.levelProg L') p := h1
    _ ≤ ∑ L' ∈ Finset.range L,
        (expectedStopCost (prog.levelProg L') p * queryInfo p) := by
        apply Finset.sum_le_sum
        intro L' hL'
        exact h2 L' hL'
    _ = (∑ L' ∈ Finset.range L, expectedStopCost (prog.levelProg L') p) * queryInfo p := by
        rw [Finset.sum_mul]

/-- For at least two hidden cells and `1 / 2 < p ≤ 1`, a decoder of the combined used-transcript
tower with error at most `0 ≤ δ ≤ 1 / 2` forces the sum of levelwise expected costs to be at
least `fanoCapacityBound n p δ` [BenOrHassidim2007]. -/
theorem clause17_rec_capacity_bound {n k : ℕ} (hn : 2 ≤ n) (prog : RecBscProgram n k) (L : ℕ)
    {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1)
    (g : RecTower n k L → Fin n) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2)
    (herr : recCombinedErrorProb prog p L g ≤ δ) :
    (∑ L' ∈ Finset.range L, expectedStopCost (prog.levelProg L') p)
      ≥ fanoCapacityBound n p δ := by
  have hn0 : 0 < n := by omega
  have hp0 : 0 ≤ p := by linarith
  have hd : ∀ (x : Fin n) (e : RecTower n k L), 0 ≤ recUsedJointLaw prog p L (x, e) :=
    fun x e => clause17_rec_used_joint_nonneg prog hp0 hp1 hn0 L x e
  have ht : (∑ x : Fin n, ∑ e : RecTower n k L, recUsedJointLaw prog p L (x, e)) = 1 :=
    clause17_rec_used_total prog p L hp0 hp1 hn0
  have hmarg : ∀ x : Fin n,
      (∑ e : RecTower n k L, recUsedJointLaw prog p L (x, e)) = 1 / (n : ℝ) :=
    fun x => clause17_rec_used_margL prog p L x hp0 hp1 hn0
  have hε : recCombinedErrorProb prog p L g
      = ∑ e : RecTower n k L, ∑ x : Fin n,
        recUsedJointLaw prog p L (x, e) * (if g e = x then 0 else 1) := by
    unfold recCombinedErrorProb
    rw [Finset.sum_comm]
  have hε0 : 0 ≤ recCombinedErrorProb prog p L g := by
    unfold recCombinedErrorProb
    apply Finset.sum_nonneg
    intro x _
    apply Finset.sum_nonneg
    intro e _
    apply mul_nonneg
    · exact clause17_rec_used_joint_nonneg prog hp0 hp1 hn0 L x e
    · split <;> norm_num
  have hε1 : recCombinedErrorProb prog p L g ≤ 1 / 2 := le_trans herr hδ1
  have hfano := fano_capacity_arith hn (recUsedJointLaw prog p L) hd ht hmarg g
    (recCombinedErrorProb prog p L g) hε hε0 hε1
  have hbin : binEntropy (recCombinedErrorProb prog p L g) ≤ binEntropy δ :=
    clause17_binEntropy_mono hε0 hε1 hδ0 hδ1 herr
  have hlogL : (0 : ℝ) ≤ Real.log ((n - 1 : ℕ) : ℝ) / Real.log 2 := by
    have h1 : (1 : ℕ) ≤ n - 1 := by omega
    have h2 : (0 : ℝ) ≤ Real.log ((n - 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast h1)
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    exact div_nonneg h2 (le_of_lt hlog2)
  have hmul : recCombinedErrorProb prog p L g * (Real.log ((n - 1 : ℕ) : ℝ) / Real.log 2)
      ≤ δ * (Real.log ((n - 1 : ℕ) : ℝ) / Real.log 2) :=
    mul_le_mul_of_nonneg_right herr hlogL
  have hmi := clause17_rec_used_mut_info_le_total_cost prog p L hp hp1 hn0
  unfold recUsedMutInfo at hmi
  have hkey : fanoNumerator n δ
      ≤ (∑ L' ∈ Finset.range L, expectedStopCost (prog.levelProg L') p) * queryInfo p := by
    unfold fanoNumerator at *
    linarith [hbin, hmul]
  have hqi : 0 < queryInfo p := clause17_queryInfo_pos_of hp hp1
  calc fanoCapacityBound n p δ
      = fanoNumerator n δ / queryInfo p := rfl
    _ ≤ ((∑ L' ∈ Finset.range L, expectedStopCost (prog.levelProg L') p) * queryInfo p)
          / queryInfo p := div_le_div_of_nonneg_right hkey hqi.le
    _ = (∑ L' ∈ Finset.range L, expectedStopCost (prog.levelProg L') p) := by
        field_simp

/-- For a recursive program with positive level count, at least two hidden cells, and `1 / 2 < p
≤ 1`, any combined-transcript decoder with error at most `0 ≤ δ ≤ 1 / 2` forces total
expected cost to be at least `fanoCapacityBound n p δ` [BenOrHassidim2007]. -/
theorem clause17_rec_total_cost_capacity_bound {n k : ℕ} (hn : 2 ≤ n) (prog : RecBscProgram n k)
    (hlev : 0 < prog.levels) {p : ℝ} (hp : 1 / 2 < p) (hp1 : p ≤ 1)
    (g : RecTower n k (recLastLevel prog + 1) → Fin n) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2)
    (herr : recCombinedErrorProb prog p (recLastLevel prog + 1) g ≤ δ) :
    recExpectedCost prog p ≥ fanoCapacityBound n p δ := by
  have hlevels : recLastLevel prog + 1 = prog.levels := by
    unfold recLastLevel
    omega
  have h := clause17_rec_capacity_bound hn prog (recLastLevel prog + 1) hp hp1 g hδ0 hδ1 herr
  calc fanoCapacityBound n p δ
      ≤ (∑ L' ∈ Finset.range (recLastLevel prog + 1),
          expectedStopCost (prog.levelProg L') p) := h
    _ = recExpectedCost prog p := by
        unfold recExpectedCost
        rw [hlevels]

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
