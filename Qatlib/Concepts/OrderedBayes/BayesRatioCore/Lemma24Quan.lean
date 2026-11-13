/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma24Stat
import Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma23Quan
import Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma21RestrictedQuan
import Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma22Quan

/-!
# Expected stage bound for the Bayesian learner

This module proves the uniform-prior learner stage bound from the ordered search analysis of
[BenOrHassidim2007]. It combines posterior invariants and entropy drift with
`zoo_bayes_survival_drift_budget`, which bounds the sum of survival probabilities by an initial
potential.

The proof also handles immediate termination when a cell already reaches the threshold. The
resulting stage count includes the transition that detects termination.

## Main statements

* `zoo_bayes_immediate_halt_stages`: an initially heavy cell gives exactly one expected stage.
* `zoo_bayes_survival_drift_budget`: a general potential bound for discrete stopping processes.
* `zoo_bayes_learner_expected_stages`: the bound log₂(n)/`queryInfo p` + 2/(3 `queryInfo p`).

## References

* [Ben-Or and Hassidim, Lemma 2.4][BenOrHassidim2007]
-/

open Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma23Quan
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

open scoped ENNReal NNReal BigOperators

/-- If some prior mass is at least ε, `learnerNext` is the point mass at the halted output
selected by `haltCut`. -/
theorem zoo_bayes_immediate_halt {n : ℕ} (hn : 0 < n) (p ε : ℝ) (a : Fin n → ℝ)
    (ha : ∃ i, ε ≤ a i) : learnerNext hn p ε a = PMF.pure (Sum.inl (haltCut hn a ε)) := by
  simp [learnerNext, ha]

/-- If some initial prior mass is at least ε, the learner's expected number of stages is exactly
one. -/
theorem zoo_bayes_immediate_halt_stages {n : ℕ} (hn : 0 < n) (p ε : ℝ) (a : Fin n → ℝ)
    (ha : ∃ i, ε ≤ a i) : learnerExpectedStages hn p ε a = 1 := by
  have hstep := zoo_bayes_immediate_halt hn p ε a ha
  have hs (t : ℕ) : finiteSurvival (learnerNext hn p ε) (t + 1) (Sum.inr a) = 0 := by
    rw [finiteSurvival_succ_running, hstep,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure, finiteSurvival_halted]
  unfold learnerExpectedStages
  rw [tsum_eq_single 0 (fun t ht => by
    cases t with
    | zero => exact (ht rfl).elim
    | succ t => exact hs t)]
  exact finiteSurvival_zero_running _ _

/-- For the uniform prior on n > 0 cells and ε ≤ 1/n, the learner's expected number of stages is
exactly one. -/
theorem zoo_bayes_uniform_immediate_stages {n : ℕ} (hn : 0 < n) (p ε : ℝ)
    (hε : ε ≤ 1 / (n : ℝ)) :
    learnerExpectedStages hn p ε (uniformPosterior (n := n)) = 1 := by
  apply zoo_bayes_immediate_halt_stages
  exact ⟨⟨0, hn⟩, hε⟩

/-- If running transitions preserve P and decrease a nonnegative extended-real potential by at
least δ in expectation, then δ times the sum of survival probabilities from a state
satisfying P is at most its initial potential. -/
theorem zoo_bayes_survival_drift_budget {S A : Type}
    (next : S → PMF (RandomizedExecution.Configuration S A))
    (P : S → Prop) (V : S → ℝ≥0∞) (δ : ℝ≥0∞)
    (hpres : ∀ s, P s → ∀ s', next s (Sum.inr s') ≠ 0 → P s')
    (hdrift : ∀ s, P s → δ + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (next s) (Sum.elim (fun _ => 0) V) ≤ V s)
    (s : S) (hs : P s) :
    δ * (∑' t : ℕ, finiteSurvival next t (Sum.inr s)) ≤ V s := by
  have hpref (fuel : ℕ) : ∀ s, P s →
      δ * (∑ t ∈ Finset.range fuel, finiteSurvival next t (Sum.inr s)) ≤ V s := by
    induction fuel with
    | zero => intro s _hs; simp
    | succ fuel ih =>
      intro s hs
      have hnext : δ * (∑ t ∈ Finset.range (fuel + 1), finiteSurvival next t (Sum.inr s)) =
          δ + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (next s)
            (fun cfg => δ * (∑ t ∈ Finset.range fuel, finiteSurvival next t cfg)) := by
        rw [Finset.sum_range_succ', finiteSurvival_zero_running]
        simp_rw [finiteSurvival_succ_running]
        rw [mul_add, mul_one,
            ← Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_sum, ← Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_const_mul]
        ac_rfl
      have hbound : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (next s)
          (fun cfg => δ * (∑ t ∈ Finset.range fuel, finiteSurvival next t cfg)) ≤
            Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (next s) (Sum.elim (fun _ => 0) V) := by
        unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
        apply ENNReal.tsum_le_tsum
        intro cfg
        cases cfg with
        | inl out => simp [finiteSurvival_halted]
        | inr state =>
          by_cases hzero : next s (Sum.inr state) = 0
          · simp [hzero]
          · exact mul_le_mul' le_rfl (ih state (hpres s hs state hzero))
      rw [hnext]
      exact (add_le_add_right hbound δ).trans (hdrift s hs)
  rw [← ENNReal.tsum_mul_left, ENNReal.tsum_eq_iSup_nat]
  apply iSup_le
  intro fuel
  rw [← Finset.mul_sum]
  exact hpref fuel s hs

/-- For 1/2 < p < 1, the query information `queryInfo p` is at most one. -/
theorem zoo_bayes_queryInfo_le_one (p : ℝ) (hp : 1 / 2 < p) (hp1 : p < 1) : queryInfo p ≤ 1 := by
  rw [zoo_bayes_queryInfo_natural]
  have hb := Real.binEntropy_nonneg (show 0 ≤ p by linarith) hp1.le
  have hq : 0 ≤ Real.binEntropy p / Real.log 2 := div_nonneg hb (Real.log_pos (by norm_num)).le
  linarith

/-- For n ≥ 2, 1/2 < p < 1, positive `queryInfo p`, and ε ≤ 1/n, the uniform-prior learner
satisfies the expected-stage bound log₂(n)/`queryInfo p` + 2/(3 `queryInfo p`). -/
theorem zoo_bayes_initially_heavy_bound (n : ℕ) (p ε : ℝ) (hn2 : 2 ≤ n)
    (hp : 1 / 2 < p) (hp1 : p < 1) (hI : 0 < queryInfo p) (hε : ε ≤ 1 / (n : ℝ)) :
    learnerExpectedStages (lt_of_lt_of_le zero_lt_two hn2) p ε (uniformPosterior (n := n)) ≤
      ENNReal.ofReal ((Real.log n / Real.log 2) / queryInfo p + 2 / (3 * queryInfo p)) := by
  rw [zoo_bayes_uniform_immediate_stages _ p ε hε]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 1 ≤ Real.log n / Real.log 2 :=
    (one_le_div hlog).2 (Real.log_le_log (by norm_num) (by exact_mod_cast hn2))
  have hI1 := zoo_bayes_queryInfo_le_one p hp hp1
  have hLI : 1 ≤ (Real.log n / Real.log 2) / queryInfo p :=
    (one_le_div hI).2 (hI1.trans hL)
  have hextra : 0 ≤ 2 / (3 * queryInfo p) := by positivity
  have hb : 1 ≤ (Real.log n / Real.log 2) / queryInfo p + 2 / (3 * queryInfo p) := by linarith
  simpa using ENNReal.ofReal_le_ofReal hb

/-- The property that a finite real prior has nonnegative weights summing to one, with each
weight at most 1/2. -/
private def validPosterior {n : ℕ} (a : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ a i) ∧ (∑ i, a i) = 1 ∧ (∀ i, a i ≤ 1 / 2)

/-- A prior satisfying `validPosterior` has base-two entropy at least one. -/
private theorem valid_entropy_one {n : ℕ} (a : Fin n → ℝ) (ha : validPosterior a) : 1 ≤ entropy a := by
  have h : (∑ i : Fin n, a i * (Real.log (a i) / Real.log 2)) ≤
      ∑ i : Fin n, a i * (Real.log (1 / 2) / Real.log 2) := Finset.sum_le_sum fun (i : Fin n) _ =>
    zoo_bayes_weighted_log_le (a i) (1 / 2) (ha.1 i) (by norm_num) (ha.2.2 i)
  rw [← Finset.sum_mul, ha.2.1, one_mul] at h
  have hl : Real.log (1 / 2 : ℝ) / Real.log 2 = -1 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
    field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
    ring
  rw [hl] at h
  unfold entropy
  linarith

/-- The uniform prior on n ≥ 2 cells satisfies `validPosterior`. -/
private theorem valid_uniform (n : ℕ) (hn2 : 2 ≤ n) : validPosterior (uniformPosterior (n := n)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le zero_lt_two hn2
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  refine ⟨fun _ => by dsimp [uniformPosterior]; positivity, ?_, ?_⟩
  · simp only [uniformPosterior, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, one_div]
    exact mul_inv_cancel₀ hn0.ne'
  · intro i
    dsimp [uniformPosterior]
    apply (div_le_iff₀ hn0).2
    nlinarith

/-- The base-two entropy of the uniform prior on n > 0 cells is log₂ n. -/
private theorem uniform_entropy (n : ℕ) (hn : 0 < n) :
    entropy (uniformPosterior (n := n)) = Real.log n / Real.log 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [entropy, uniformPosterior, hn0]
  field_simp

/-- For a valid prior with every weight below ε and 0 < ε ≤ 1/2, the prefix mass at
`stageTwoCut` lies in [1/2 - ε, 1/2). -/
private theorem selected_cut_band {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ε : ℝ)
    (ha : validPosterior a) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hsmall : ∀ i, a i < ε) :
    1 / 2 - ε ≤ prefixMass a (stageTwoCut hn a ε) ∧
      prefixMass a (stageTwoCut hn a ε) < 1 / 2 := by
  obtain ⟨k, hk0, hkn, hklo, hkhi⟩ :=
      zoo_bayes_prefix_mass_threshold n a ε hε hεhalf ha.1 ha.2.1 hsmall
  let i : Fin n := ⟨k - 1, by omega⟩
  have heq : prefixMass a i = ∑ j : Fin n, if j.val < k then a j else 0 := by
    apply Finset.sum_congr rfl
    intro j _hj
    have hc : j.val ≤ k - 1 ↔ j.val < k := by omega
    simp [i, hc]
  have hne : (cutSet a ε).Nonempty := by
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [heq]
    exact ⟨hklo, hkhi⟩
  have hmem : stageTwoCut hn a ε ∈ cutSet a ε := by
    unfold stageTwoCut
    rw [dif_pos hne]
    exact Finset.min'_mem _ _
  exact (Finset.mem_filter.mp hmem).2

/-- If a valid prior has every weight below ε ≤ 1/6 and the cut's prefix mass lies in [1/2 - ε,
1/2), then both posterior updates satisfy `validPosterior` for 1/2 < p < 1. -/
private theorem bounded_posteriors {n : ℕ} (a : Fin n → ℝ) (i : Fin n) (p ε : ℝ)
    (ha : validPosterior a) (hp : 1 / 2 < p) (hp1 : p < 1) (hε : ε ≤ 1 / 6)
    (hsmall : ∀ j, a j < ε)
    (hband : 1 / 2 - ε ≤ prefixMass a i ∧ prefixMass a i < 1 / 2) :
    validPosterior (updateFalse a i p) ∧ validPosterior (updateTrue a i p) := by
  obtain ⟨hF, hT, hFT⟩ := zoo_bayes_answer_probabilities a i p ha.1 ha.2.1 hp hp1
  obtain ⟨haF, hsF, haT, hsT⟩ := zoo_bayes_posterior_invariants a i p ha.1 ha.2.1 hp hp1
  have hFac : 0 ≤ 2 * p - 1 := by linarith
  have hm := mul_le_mul_of_nonneg_right (show 2 * p - 1 ≤ 1 by linarith)
    (show 0 ≤ 1 / 2 - prefixMass a i by linarith [hband.2])
  have hnm := mul_nonneg hFac (show 0 ≤ 1 / 2 - prefixMass a i by linarith [hband.2])
  have hFlo : 2 * ε ≤ normFalse a i p := by dsimp [normFalse]; nlinarith [hband.1]
  have hThi : normFalse a i p ≤ 1 / 2 := by dsimp [normFalse]; nlinarith
  have hTlo : 2 * ε ≤ normTrue a i p := by nlinarith
  have hnum (j : Fin n) : p * a j ≤ ε ∧ (1 - p) * a j ≤ ε := by
    have hp0 : 0 ≤ p := by linarith
    have hpc1 : 1 - p ≤ 1 := by linarith
    have hm1 := mul_le_mul_of_nonneg_right hp1.le (ha.1 j)
    have hm2 := mul_le_mul_of_nonneg_right hpc1 (ha.1 j)
    constructor <;> nlinarith [hsmall j]
  refine ⟨⟨haF, hsF, ?_⟩, ⟨haT, hsT, ?_⟩⟩
  · intro j
    apply (div_le_iff₀ hF).2
    split_ifs <;> nlinarith [(hnum j).1, (hnum j).2]
  · intro j
    apply (div_le_iff₀ hT).2
    split_ifs <;> nlinarith [(hnum j).1, (hnum j).2]

/-- For 1/2 < p < 1 and 0 < ε ≤ 1/6, every running successor with nonzero transition probability
from a valid prior is again a valid prior. -/
private theorem learner_preserves_valid {n : ℕ} (hn : 0 < n) (p ε : ℝ)
    (hp : 1 / 2 < p) (hp1 : p < 1) (hε : 0 < ε) (hε6 : ε ≤ 1 / 6) :
    ∀ a, validPosterior a → ∀ a', learnerNext hn p ε a (Sum.inr a') ≠ 0 → validPosterior a' := by
  classical
  intro a ha a' hprob
  by_cases hheavy : ∃ i, ε ≤ a i
  · rw [zoo_bayes_immediate_halt hn p ε a hheavy] at hprob
    simp at hprob
  · have hsmall : ∀ i, a i < ε := by
      intro i
      by_contra! h
      exact hheavy ⟨i, h⟩
    have hband := selected_cut_band hn a ε ha hε (by linarith) hsmall
    have hupdates := bounded_posteriors a (stageTwoCut hn a ε) p ε ha hp hp1 hε6 hsmall hband
    have hnext : learnerNext hn p ε a =
        (PMF.bernoulli (clampProb (normTrue a (stageTwoCut hn a ε) p)) (clampProb_le _)).map
          (fun bit => Sum.inr (if bit then updateTrue a (stageTwoCut hn a ε) p
            else updateFalse a (stageTwoCut hn a ε) p)) := by
      unfold learnerNext
      rw [dif_neg hheavy]
      rfl
    have hsupp := (PMF.mem_support_iff _ _).2 hprob
    rw [hnext] at hsupp
    obtain ⟨bit, _hbit, heq⟩ := (PMF.mem_support_map_iff _ _ _).1 hsupp
    have hvalid : validPosterior (if bit then updateTrue a (stageTwoCut hn a ε) p
        else updateFalse a (stageTwoCut hn a ε) p) := by
      cases bit
      · exact hupdates.1
      · exact hupdates.2
    exact (Sum.inr.inj heq) ▸ hvalid

/-- For a valid prior with no weight reaching ε and 1/2 < p < 1, the expected successor entropy,
assigning zero to halted outputs, equals the answer-probability-weighted sum of the two
updated entropies, embedded in `ENNReal`. -/
private theorem learner_entropy_expectation {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (p ε : ℝ)
    (ha : validPosterior a) (hp : 1 / 2 < p) (hp1 : p < 1) (hheavy : ¬∃ i, ε ≤ a i) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (learnerNext hn p ε a)
      (Sum.elim (fun _ => 0) (fun state => ENNReal.ofReal (entropy state))) =
      ENNReal.ofReal (normFalse a (stageTwoCut hn a ε) p * entropy (updateFalse a (stageTwoCut hn a ε) p) +
        normTrue a (stageTwoCut hn a ε) p * entropy (updateTrue a (stageTwoCut hn a ε) p)) := by
  classical
  let i := stageTwoCut hn a ε
  obtain ⟨hF, hT, _hFT⟩ := zoo_bayes_answer_probabilities a i p ha.1 ha.2.1 hp hp1
  obtain ⟨haF, hsF, haT, hsT⟩ := zoo_bayes_posterior_invariants a i p ha.1 ha.2.1 hp hp1
  have hEF := zoo_bayes_entropy_nonnegative (updateFalse a i p) haF hsF
  have hET := zoo_bayes_entropy_nonnegative (updateTrue a i p) haT hsT
  have hcoin : ((clampProb (normTrue a i p) : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (normTrue a i p) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    exact zoo_bayes_answer_clamp a i p ha.1 ha.2.1 hp hp1
  have hcoinF : (((1 : ℝ≥0) - clampProb (normTrue a i p)) : ℝ≥0∞) =
      ENNReal.ofReal (normFalse a i p) := by
    rw [ENNReal.coe_one, hcoin, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub 1 hT.le]
    congr 1
    unfold normTrue
    ring
  unfold learnerNext
  rw [dif_neg hheavy, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
  simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure, Sum.elim_inr]
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
  rw [tsum_fintype, Fintype.sum_bool]
  simp only [PMF.bernoulli_apply, Bool.cond_true, Bool.cond_false, ↓reduceIte, ENNReal.coe_sub]
  change ((clampProb (normTrue a i p) : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (entropy (updateTrue a i p)) +
    (((1 : ℝ≥0) - clampProb (normTrue a i p)) : ℝ≥0∞) * ENNReal.ofReal (entropy (updateFalse a i p)) = _
  rw [hcoinF, hcoin, ← ENNReal.ofReal_mul hT.le, ← ENNReal.ofReal_mul hF.le,
    ← ENNReal.ofReal_add (mul_nonneg hT.le hET) (mul_nonneg hF.le hEF)]
  congr 1
  ring

/-- Under the stated dimension, noise, and threshold bounds with positive `queryInfo p`, the
expected successor entropy with halted outputs valued at zero, plus `queryInfo p` times 1 -
1/(3 log₂ n), is at most the current entropy of a valid prior, as an `ENNReal` inequality. -/
private theorem learner_entropy_drift (n : ℕ) (p ε : ℝ) (hn2 : 2 ≤ n)
    (hp : 1 / 2 < p) (hp1 : p < 1) (hε : 0 < ε)
    (hcap : ε ≤ Real.sqrt (1 / (24 * (Real.log n / Real.log 2)))) (hI : 0 < queryInfo p) :
    ∀ a, validPosterior a →
      ENNReal.ofReal (queryInfo p * (1 - 1 / (3 * (Real.log n / Real.log 2)))) +
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (learnerNext (lt_of_lt_of_le zero_lt_two hn2) p ε a)
          (Sum.elim (fun _ => 0) (fun state => ENNReal.ofReal (entropy state))) ≤ ENNReal.ofReal (entropy a) := by
  classical
  let δ := queryInfo p * (1 - 1 / (3 * (Real.log n / Real.log 2)))
  have hL : 1 ≤ Real.log n / Real.log 2 := (one_le_div (Real.log_pos (by norm_num))).2
    (Real.log_le_log (by norm_num) (by exact_mod_cast hn2))
  have hfac0 : 0 ≤ 1 - 1 / (3 * (Real.log n / Real.log 2)) := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ (by positivity : 0 < 3 * (Real.log n / Real.log 2))).2
    nlinarith
  have hδ0 : 0 ≤ δ := mul_nonneg hI.le hfac0
  have hδ1 : δ ≤ 1 := by
    have hfac1 : 1 - 1 / (3 * (Real.log n / Real.log 2)) ≤ 1 := by
      have hh : 0 ≤ 1 / (3 * (Real.log n / Real.log 2)) := by positivity
      linarith
    have hh := mul_le_mul_of_nonneg_left hfac1 hI.le
    dsimp [δ]
    nlinarith [zoo_bayes_queryInfo_le_one p hp hp1]
  intro a ha
  by_cases hheavy : ∃ i, ε ≤ a i
  · rw [zoo_bayes_immediate_halt _ p ε a hheavy, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure]
    simp only [Sum.elim_inl, add_zero]
    exact ENNReal.ofReal_le_ofReal (hδ1.trans (valid_entropy_one a ha))
  · let i := stageTwoCut (lt_of_lt_of_le zero_lt_two hn2) a ε
    have hsmall : ∀ j, a j < ε := by intro j; by_contra! h; exact hheavy ⟨j, h⟩
    have hεhalf : ε ≤ 1 / 2 := by
      have hs := Real.sq_sqrt (by positivity : 0 ≤ 1 / (24 * (Real.log n / Real.log 2)))
      have hle : 1 / (24 * (Real.log n / Real.log 2)) ≤ (1 / 24 : ℝ) := by
        apply (div_le_iff₀ (by positivity : 0 < 24 * (Real.log n / Real.log 2))).2
        nlinarith
      nlinarith [Real.sqrt_nonneg (1 / (24 * (Real.log n / Real.log 2)))]
    have hband := selected_cut_band (lt_of_lt_of_le zero_lt_two hn2) a ε ha hε hεhalf hsmall
    have hrise :=
        zoo_bayes_expected_info_rise n a i p ε hn2 hp hp1 hε hcap ha.1 ha.2.1 hband.1 hband.2
    change δ ≤ _ at hrise
    have hreal : δ + normFalse a i p * entropy (updateFalse a i p) +
        normTrue a i p * entropy (updateTrue a i p) ≤ entropy a := by
      unfold postInfo at hrise
      rw [show normTrue a i p = 1 - normFalse a i p from rfl] at hrise ⊢
      nlinarith
    obtain ⟨hF, hT, _⟩ := zoo_bayes_answer_probabilities a i p ha.1 ha.2.1 hp hp1
    obtain ⟨haF, hsF, haT, hsT⟩ := zoo_bayes_posterior_invariants a i p ha.1 ha.2.1 hp hp1
    have hmean : 0 ≤ normFalse a i p * entropy (updateFalse a i p) +
        normTrue a i p * entropy (updateTrue a i p) :=
      add_nonneg (mul_nonneg hF.le (zoo_bayes_entropy_nonnegative _ haF hsF))
        (mul_nonneg hT.le (zoo_bayes_entropy_nonnegative _ haT hsT))
    rw [learner_entropy_expectation _ a p ε ha hp hp1 hheavy, ← ENNReal.ofReal_add hδ0 hmean]
    exact ENNReal.ofReal_le_ofReal (by simpa [add_assoc] using hreal)

/-- If n ≥ 2 and 1/6 < ε ≤ √(1/(24 log₂ n)), then n = 2. -/
private theorem large_threshold_two (n : ℕ) (ε : ℝ) (hn2 : 2 ≤ n) (hε : 0 < ε)
    (hcap : ε ≤ Real.sqrt (1 / (24 * (Real.log n / Real.log 2))))
    (hlarge : 1 / 6 < ε) : n = 2 := by
  by_contra hn
  have hn3 : 3 ≤ n := by omega
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 8)
    (show (8 : ℝ) ≤ (n : ℝ)^2 by nlinarith)
  rw [show (8 : ℝ) = 2^3 by norm_num, Real.log_pow, Real.log_pow] at hlog
  norm_num at hlog
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : (3 / 2 : ℝ) ≤ Real.log n / Real.log 2 := (le_div_iff₀ hlog2).2 (by nlinarith)
  have hL0 : 0 < Real.log n / Real.log 2 := by linarith
  have hbound : 1 / (24 * (Real.log n / Real.log 2)) ≤ (1 / 36 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 24 * (Real.log n / Real.log 2))).2
    nlinarith
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 1 / (24 * (Real.log n / Real.log 2)))
  nlinarith [Real.sqrt_nonneg (1 / (24 * (Real.log n / Real.log 2)))]

/-- Proves `Lemma2_4`: under its dimension, noise, and threshold hypotheses, the uniform-prior
learner has expected stage count at most log₂(n)/`queryInfo p` + 2/(3 `queryInfo p`) [Ben-Or
and Hassidim, Lemma 2.4][BenOrHassidim2007]. -/
theorem zoo_bayes_learner_expected_stages : Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma2_4 := by
  intro n p ε hn2 hp hp1 hε hcap hI
  by_cases hε6 : ε ≤ 1 / 6
  · let hn : 0 < n := lt_of_lt_of_le zero_lt_two hn2
    let L : ℝ := Real.log n / Real.log 2
    let δ : ℝ := queryInfo p * (1 - 1 / (3 * L))
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hL : 1 ≤ L := (one_le_div hlog2).2
      (Real.log_le_log (by norm_num) (by exact_mod_cast hn2))
    have hL0 : 0 < L := by linarith
    have hden : 0 < 3 * L - 1 := by linarith
    have hfac : 0 < 1 - 1 / (3 * L) := by
      apply sub_pos.mpr
      apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 3 * L)).2
      nlinarith
    have hδ : 0 < δ := mul_pos hI hfac
    have hbudget := zoo_bayes_survival_drift_budget (learnerNext hn p ε)
      validPosterior (fun a => ENNReal.ofReal (entropy a)) (ENNReal.ofReal δ)
      (learner_preserves_valid hn p ε hp hp1 hε hε6)
      (learner_entropy_drift n p ε hn2 hp hp1 hε hcap hI)
      (uniformPosterior (n := n)) (valid_uniform n hn2)
    change ENNReal.ofReal δ * learnerExpectedStages hn p ε (uniformPosterior (n := n)) ≤
      ENNReal.ofReal (entropy (uniformPosterior (n := n))) at hbudget
    rw [uniform_entropy n hn] at hbudget
    have hquot : learnerExpectedStages hn p ε (uniformPosterior (n := n)) ≤
        ENNReal.ofReal L / ENNReal.ofReal δ := by
      apply (ENNReal.le_div_iff_mul_le
        (Or.inl (ne_of_gt (ENNReal.ofReal_pos.mpr hδ))) (Or.inl ENNReal.ofReal_ne_top)).2
      simpa only [mul_comm] using hbudget
    rw [← ENNReal.ofReal_div_of_pos hδ] at hquot
    have hrepr : L / δ = (L * (3 * L) / (3 * L - 1)) / queryInfo p := by
      dsimp [δ]
      field_simp [hL0.ne', hI.ne', hfac.ne', hden.ne']
    have hscalar : L * (3 * L) / (3 * L - 1) ≤ L + 2 / 3 :=
      (div_le_iff₀ hden).2 (by nlinarith)
    have hratio : L / δ ≤ L / queryInfo p + 2 / (3 * queryInfo p) := by
      rw [hrepr]
      calc
        _ ≤ (L + 2 / 3) / queryInfo p := div_le_div_of_nonneg_right hscalar hI.le
        _ = _ := by field_simp [hI.ne']
    exact hquot.trans (ENNReal.ofReal_le_ofReal hratio)
  · have hn : n = 2 := large_threshold_two n ε hn2 hε hcap (by linarith)
    have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
    have hεhalf : ε ≤ 1 / (n : ℝ) := by
      rw [hn]
      rw [hn] at hcap
      norm_num [div_self hlog2] at hcap ⊢
      have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 24)
      have hr : 0 < Real.sqrt 24 := Real.sqrt_pos.mpr (by norm_num)
      have hi : (Real.sqrt 24)⁻¹ ≤ (1 / 2 : ℝ) := by
        rw [← one_div]
        apply (div_le_iff₀ hr).2
        nlinarith [Real.sqrt_nonneg 24]
      exact hcap.trans hi
    exact zoo_bayes_initially_heavy_bound n p ε hn2 hp hp1 hI hεhalf

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
