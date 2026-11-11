/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.BayesTruthRatioCrossingRightQuan
import Qatlib.Concepts.OrderedBayes.BayesRatioCore.BayesTruthRatioCrossingLeftQuan
import Qatlib.Concepts.OrderedBayes.BayesRatioCore.RankBayesEqualCellCorrection

/-!
# Adaptive cut ratio and window union bounds

Posterior ratio potentials yield finite run bounds for truth driven ordered search, both for the
learner kernel and for a kernel that absorbs at a crossing in a finite pair set. Summing initial
ratio weights gives `cutUnionBound`, and odds ratio powers calibrate this bound to any positive
target, extending the adaptive learning analysis of [BenOrHassidim2007].

Window counting finds a light cell before a heavy cell, reducing far heavy posterior events and
selected halting events to pairwise ratio events. The results require the stated positive prior
and total mass bounds, and apply at every finite fuel value.

## Main statements

* `cut_union_event_bound` and `learner_cut_union_event_bound`: bound finite unions of ratio
  events.
* `learner_far_heavy_window_bound`: bounds the probability of a heavy cell beyond the window.
* `learner_haltCut_far_bound`: bounds a far selected halting cut.
* `frontier1` and `frontier2`: collect the absorbing and learner estimates.

## References

* [Ben-Or and Hassidim, 2007][BenOrHassidim2007]
-/

set_option warningAsError false
open Qatlib.Concepts.OrderedBayes.BayesRatioCore
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels.OrderedSearch2007

set_option autoImplicit false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution


namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore.AdaptiveCutUnionBound

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Qatlib.Concepts.OrderedBayes.BayesRatioCore
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels.OrderedSearch2007
open scoped ENNReal BigOperators Classical

/-- The ordering condition `j < v < u` or `u < v < j` on the truth index and an ordered pair. -/
def crossSide {n : ℕ} (j u v : Fin n) : Prop :=
  ((j : ℕ) < (v : ℕ) ∧ (v : ℕ) < (u : ℕ)) ∨ ((u : ℕ) < (v : ℕ) ∧ (v : ℕ) < (j : ℕ))

/-- The learner transition that first halts with the current posterior if any pair in `S`
satisfies `R * a v ≤ a u`, and otherwise takes a truth driven learner step. -/
noncomputable def unionAbsorbNext {n : ℕ} (hn : 0 < n) (j : Fin n) (p ε R : ℝ)
    (S : Finset (Fin n × Fin n)) :
    (Fin n → ℝ) → PMF (Configuration (Fin n → ℝ) (Fin n → ℝ)) :=
  fun a =>
    if ∃ pr ∈ S, R * a pr.2 ≤ a pr.1 then PMF.pure (Sum.inl a)
    else trueLearnerNext hn j p ε a

/-- If some pair already crosses its ratio threshold, every supported result of a finite union
absorbing run still has a crossing pair. -/
theorem unionAbsorb_terminal {n : ℕ} (hn : 0 < n) (j : Fin n) (p ε R : ℝ)
    (S : Finset (Fin n × Fin n)) (fuel : ℕ)
    (cfg : Configuration (Fin n → ℝ) (Fin n → ℝ))
    (h : ∃ pr ∈ S, R * configPosterior cfg pr.2 ≤ configPosterior cfg pr.1) :
    ∀ x ∈ (runFor (unionAbsorbNext hn j p ε R S) fuel cfg).support,
      ∃ pr ∈ S, R * configPosterior x.1 pr.2 ≤ configPosterior x.1 pr.1 := by
  induction fuel generalizing cfg with
  | zero =>
      intro x hx
      rw [runFor_zero] at hx
      obtain rfl := (PMF.mem_support_pure_iff _ _).mp hx
      exact h
  | succ fuel ih =>
      intro x hx
      cases cfg with
      | inl out =>
          rw [runFor_halted] at hx
          obtain rfl := (PMF.mem_support_pure_iff _ _).mp hx
          exact h
      | inr s =>
          have habs : ∃ pr ∈ S, R * s pr.2 ≤ s pr.1 := h
          have htick : tick (unionAbsorbNext hn j p ε R S) (Sum.inr s)
              = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge 1 (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret (Sum.inl s)) := by
            rw [tick, unionAbsorbNext, if_pos habs, PMF.pure_map,
                Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge_ret]
          rw [show runFor (unionAbsorbNext hn j p ε R S) (fuel + 1) (Sum.inr s)
                = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind (tick (unionAbsorbNext hn j p ε R S) (Sum.inr s))
                    (runFor (unionAbsorbNext hn j p ε R S) fuel) from rfl,
            htick, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge_bind, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret_bind, runFor_halted,
            Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge_ret] at hx
          obtain rfl := (PMF.mem_support_pure_iff _ _).mp hx
          exact habs

/-- For `j < k < i`, a pair `(i, k)` in `S`, and `1 / 2 < p < 1`, the union absorbing step does
not increase the expected ratio potential `i / k`. -/
theorem unionAbsorb_one_step_right {n : ℕ} (hn : 0 < n) (j k i : Fin n)
    (p ε R : ℝ) (S : Finset (Fin n × Fin n)) (hmem : (i, k) ∈ S)
    (hp : 1 / 2 < p) (hp1 : p < 1) (hjk : (j : ℕ) < (k : ℕ)) (hki : (k : ℕ) < (i : ℕ))
    (a : Fin n → ℝ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (unionAbsorbNext hn j p ε R S a) (ratioPotential i k) ≤
      ratioPotential i k (Sum.inr a) := by
  by_cases habs : ∃ pr ∈ S, R * a pr.2 ≤ a pr.1
  · simp only [unionAbsorbNext, if_pos habs, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure,
      ratioPotential, configPosterior, Sum.elim_inl, Sum.elim_inr, id_eq]
    exact le_rfl
  · have hpair : ¬ (R * a k ≤ a i) := fun h => habs ⟨(i, k), hmem, h⟩
    rw [unionAbsorbNext, if_neg habs,
      show trueLearnerNext hn j p ε a = crossingAbsorbNext hn j p ε R i k a from by
        rw [crossingAbsorbNext, if_neg hpair]]
    exact crossingAbsorb_one_step_right hn j k i hp hp1 hjk hki a

/-- For `u < v < j`, a pair `(u, v)` in `S`, and `1 / 2 < p < 1`, the union absorbing step does
not increase the expected ratio potential `u / v`. -/
theorem unionAbsorb_one_step_left {n : ℕ} (hn : 0 < n) (j u v : Fin n)
    (p ε R : ℝ) (S : Finset (Fin n × Fin n)) (hmem : (u, v) ∈ S)
    (hp : 1 / 2 < p) (hp1 : p < 1) (huv : (u : ℕ) < (v : ℕ)) (hvj : (v : ℕ) < (j : ℕ))
    (a : Fin n → ℝ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (unionAbsorbNext hn j p ε R S a) (ratioPotential u v) ≤
      ratioPotential u v (Sum.inr a) := by
  by_cases habs : ∃ pr ∈ S, R * a pr.2 ≤ a pr.1
  · simp only [unionAbsorbNext, if_pos habs, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure,
      ratioPotential, configPosterior, Sum.elim_inl, Sum.elim_inr, id_eq]
    exact le_rfl
  · have hpair : ¬ (R * a v ≤ a u) := fun h => habs ⟨(u, v), hmem, h⟩
    rw [unionAbsorbNext, if_neg habs,
      show trueLearnerNext hn j p ε a = crossingAbsorbNext hn j p ε R u v a from by
        rw [crossingAbsorbNext, if_neg hpair]]
    exact crossingAbsorb_one_step_left hn u v j hp hp1 huv hvj a

/-- For `1 / 2 < p < 1`, a truth driven learner step preserves strictly positive posterior
entries and total mass at most one throughout its support. -/
theorem trueLearnerNext_support_inv {n : ℕ} (hn : 0 < n) (j : Fin n) (p ε : ℝ)
    (hp : 1 / 2 < p) (hp1 : p < 1) (a : Fin n → ℝ) (ha : truthInv a) :
    ∀ cfg ∈ (trueLearnerNext hn j p ε a).support, truthInv (configPosterior cfg) := by
  intro cfg hcfg
  simp only [trueLearnerNext] at hcfg
  by_cases hhalt : ∃ m : Fin n, ε ≤ a m
  · simp only [dif_pos hhalt] at hcfg
    obtain rfl := (PMF.mem_support_pure_iff _ _).mp hcfg
    exact ha
  · simp only [dif_neg hhalt] at hcfg
    obtain ⟨b, hb, hEq⟩ := (PMF.mem_support_bind_iff _ _ cfg).mp hcfg
    rw [PMF.mem_support_pure_iff _ _] at hEq
    obtain rfl := hEq
    have ha0 : ∀ m, 0 ≤ a m := fun m => le_of_lt (ha.1 m)
    obtain ⟨hposF, hposT⟩ :=
      zoo_bayes_truth_update_positivity a (stageTwoCut hn a ε) p hp hp1 ha.1 ha.2
    rcases b
    · exact ⟨hposF, updateFalse_sum_le a (stageTwoCut hn a ε) hp hp1 ha0 ha.2⟩
    · exact ⟨hposT, updateTrue_sum_le a (stageTwoCut hn a ε) hp hp1 ha0 ha.2⟩

/-- For `1 / 2 < p < 1`, a union absorbing step preserves `truthInv` throughout its support. -/
theorem unionAbsorb_support_inv {n : ℕ} (hn : 0 < n) (j : Fin n) (p ε R : ℝ)
    (S : Finset (Fin n × Fin n)) (hp : 1 / 2 < p) (hp1 : p < 1)
    (a : Fin n → ℝ) (ha : truthInv a) :
    ∀ cfg ∈ (unionAbsorbNext hn j p ε R S a).support, truthInv (configPosterior cfg) := by
  intro cfg hcfg
  by_cases habs : ∃ pr ∈ S, R * a pr.2 ≤ a pr.1
  · simp only [unionAbsorbNext, if_pos habs] at hcfg
    obtain rfl := (PMF.mem_support_pure_iff _ _).mp hcfg
    exact ha
  · simp only [unionAbsorbNext, if_neg habs] at hcfg
    exact trueLearnerNext_support_inv hn j p ε hp hp1 a ha cfg hcfg

/-- For `(i, k) ∈ S` with `j < k < i`, positive threshold `R`, and `1 / 2 < p < 1`, the crossing
event after any finite union absorbing run has probability at most `ENNReal.ofReal ((a₀ i /
a₀ k) / R)` for a positive prior of mass at most one. -/
theorem union_pair_crossing_right {n : ℕ} (hn : 0 < n) (j k i : Fin n)
    (p ε R : ℝ) (S : Finset (Fin n × Fin n)) (hmem : (i, k) ∈ S)
    (hp : 1 / 2 < p) (hp1 : p < 1) (hR : 0 < R)
    (hjk : (j : ℕ) < (k : ℕ)) (hki : (k : ℕ) < (i : ℕ))
    (a₀ : Fin n → ℝ) (hpos : ∀ m, 0 < a₀ m) (hsum : (∑ m, a₀ m) ≤ 1)
    (fuel : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (unionAbsorbNext hn j p ε R S) fuel (Sum.inr a₀))
      (fun x => R * configPosterior x.1 k ≤ configPosterior x.1 i) ≤
      ENNReal.ofReal ((a₀ i / a₀ k) / R) := by
  refine le_trans (ville_event_bound (unionAbsorbNext hn j p ε R S)
    (ratioPotential i k)
    (fun cfg => R * configPosterior cfg k ≤ configPosterior cfg i)
    (fun cfg => truthInv (configPosterior cfg))
    (ENNReal.ofReal R)
    (ENNReal.ofReal_pos.mpr hR).ne'
    ENNReal.ofReal_ne_top
    (unionAbsorb_one_step_right hn j k i p ε R S hmem hp hp1 hjk hki)
    (fun s hs cfg hcfg => unionAbsorb_support_inv hn j p ε R S hp hp1 s hs cfg hcfg)
    (fun cfg hI hQ => ENNReal.ofReal_le_ofReal ((le_div_iff₀ (hI.1 k)).mpr hQ))
    fuel (Sum.inr a₀) ⟨hpos, hsum⟩) ?_
  rw [show ratioPotential i k (Sum.inr a₀) / ENNReal.ofReal R
      = ENNReal.ofReal ((a₀ i / a₀ k) / R) from by
    rw [ratioPotential, configPosterior, Sum.elim_inr, id_eq, ENNReal.ofReal_div_of_pos hR]]

/-- For `(u, v) ∈ S` with `u < v < j`, positive threshold `R`, and `1 / 2 < p < 1`, the crossing
event after any finite union absorbing run has probability at most `ENNReal.ofReal ((a₀ u /
a₀ v) / R)` for a positive prior of mass at most one. -/
theorem union_pair_crossing_left {n : ℕ} (hn : 0 < n) (j u v : Fin n)
    (p ε R : ℝ) (S : Finset (Fin n × Fin n)) (hmem : (u, v) ∈ S)
    (hp : 1 / 2 < p) (hp1 : p < 1) (hR : 0 < R)
    (huv : (u : ℕ) < (v : ℕ)) (hvj : (v : ℕ) < (j : ℕ))
    (a₀ : Fin n → ℝ) (hpos : ∀ m, 0 < a₀ m) (hsum : (∑ m, a₀ m) ≤ 1)
    (fuel : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (unionAbsorbNext hn j p ε R S) fuel (Sum.inr a₀))
      (fun x => R * configPosterior x.1 v ≤ configPosterior x.1 u) ≤
      ENNReal.ofReal ((a₀ u / a₀ v) / R) := by
  refine le_trans (ville_event_bound (unionAbsorbNext hn j p ε R S)
    (ratioPotential u v)
    (fun cfg => R * configPosterior cfg v ≤ configPosterior cfg u)
    (fun cfg => truthInv (configPosterior cfg))
    (ENNReal.ofReal R)
    (ENNReal.ofReal_pos.mpr hR).ne'
    ENNReal.ofReal_ne_top
    (unionAbsorb_one_step_left hn j u v p ε R S hmem hp hp1 huv hvj)
    (fun s hs cfg hcfg => unionAbsorb_support_inv hn j p ε R S hp hp1 s hs cfg hcfg)
    (fun cfg hI hQ => ENNReal.ofReal_le_ofReal ((le_div_iff₀ (hI.1 v)).mpr hQ))
    fuel (Sum.inr a₀) ⟨hpos, hsum⟩) ?_
  rw [show ratioPotential u v (Sum.inr a₀) / ENNReal.ofReal R
      = ENNReal.ofReal ((a₀ u / a₀ v) / R) from by
    rw [ratioPotential, configPosterior, Sum.elim_inr, id_eq, ENNReal.ofReal_div_of_pos hR]]

/-- For a pair in `S` satisfying `crossSide`, the ratio threshold event after any finite union
absorbing run is bounded by the initial ratio divided by positive `R`, assuming `1 / 2 < p <
1` and a positive prior of mass at most one. -/
theorem union_pair_crossing {n : ℕ} (hn : 0 < n) (j u v : Fin n)
    (p ε R : ℝ) (S : Finset (Fin n × Fin n)) (hmem : (u, v) ∈ S)
    (hside : crossSide j u v)
    (hp : 1 / 2 < p) (hp1 : p < 1) (hR : 0 < R)
    (a₀ : Fin n → ℝ) (hpos : ∀ m, 0 < a₀ m) (hsum : (∑ m, a₀ m) ≤ 1)
    (fuel : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (unionAbsorbNext hn j p ε R S) fuel (Sum.inr a₀))
      (fun x => R * configPosterior x.1 v ≤ configPosterior x.1 u) ≤
      ENNReal.ofReal ((a₀ u / a₀ v) / R) := by
  rcases hside with ⟨hjv, hvu⟩ | ⟨huv, hvj⟩
  · exact union_pair_crossing_right hn j v u p ε R S hmem hp hp1 hR hjv hvu a₀ hpos hsum fuel
  · exact union_pair_crossing_left hn j u v p ε R S hmem hp hp1 hR huv hvj a₀ hpos hsum fuel

/-- The union absorbing kernel for a singleton pair is the corresponding pairwise crossing
absorbing kernel. -/
theorem singleton_unionAbsorbNext {n : ℕ} (hn : 0 < n) (j u v : Fin n) (p ε R : ℝ) :
    (unionAbsorbNext hn j p ε R {(u, v)} : (Fin n → ℝ) → _) = crossingAbsorbNext hn j p ε R u v := by
  funext a
  have hmem_iff : (∃ pr ∈ ({(u, v)} : Finset (Fin n × Fin n)), R * a pr.2 ≤ a pr.1)
      ↔ R * a v ≤ a u := by
    constructor
    · rintro ⟨pr, hpr, hle⟩
      rw [Finset.mem_singleton] at hpr
      subst hpr
      exact hle
    · intro hle
      exact ⟨(u, v), Finset.mem_singleton.mpr rfl, hle⟩
  by_cases h : R * a v ≤ a u
  · simp only [unionAbsorbNext, crossingAbsorbNext, if_pos (hmem_iff.mpr h), if_pos h]
  · simp only [unionAbsorbNext, crossingAbsorbNext, if_neg (fun hex => h (hmem_iff.mp hex)),
      if_neg h]

/-- For `j < k < i`, the singleton union absorbing kernel has crossing probability at most the
initial ratio `a₀ i / a₀ k` divided by positive `R`, at every fuel, under the noise and
prior hypotheses. -/
theorem union_pair_singleton_right {n : ℕ} (hn : 0 < n) (j k i : Fin n)
    (p ε R : ℝ) (hp : 1 / 2 < p) (hp1 : p < 1) (hR : 0 < R)
    (hjk : (j : ℕ) < (k : ℕ)) (hki : (k : ℕ) < (i : ℕ))
    (a₀ : Fin n → ℝ) (hpos : ∀ m, 0 < a₀ m) (hsum : (∑ m, a₀ m) ≤ 1)
    (fuel : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (unionAbsorbNext hn j p ε R {(i, k)}) fuel (Sum.inr a₀))
      (fun x => R * configPosterior x.1 k ≤ configPosterior x.1 i) ≤
      ENNReal.ofReal ((a₀ i / a₀ k) / R) := by
  rw [singleton_unionAbsorbNext]
  exact zoo_bayes_truth_ratio_crossing_right n hn j k i p ε R a₀ hjk hki hp hp1 hR hpos hsum fuel

/-- For `u < v < j`, the singleton union absorbing kernel has crossing probability at most the
initial ratio `a₀ u / a₀ v` divided by positive `R`, at every fuel, under the noise and
prior hypotheses. -/
theorem union_pair_singleton_left {n : ℕ} (hn : 0 < n) (j u v : Fin n)
    (p ε R : ℝ) (hp : 1 / 2 < p) (hp1 : p < 1) (hR : 0 < R)
    (huv : (u : ℕ) < (v : ℕ)) (hvj : (v : ℕ) < (j : ℕ))
    (a₀ : Fin n → ℝ) (hpos : ∀ m, 0 < a₀ m) (hsum : (∑ m, a₀ m) ≤ 1)
    (fuel : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (unionAbsorbNext hn j p ε R {(u, v)}) fuel (Sum.inr a₀))
      (fun x => R * configPosterior x.1 v ≤ configPosterior x.1 u) ≤
      ENNReal.ofReal ((a₀ u / a₀ v) / R) := by
  rw [singleton_unionAbsorbNext]
  exact zoo_bayes_truth_ratio_crossing_left n hn u v j p ε R a₀ huv hvj hp hp1 hR hpos hsum fuel

/-- The probability of a union of two events is at most the sum of their probabilities. -/
theorem event_or_le {α : Type*} (μ : PMF α) (A B : α → Prop) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event μ (fun x => A x ∨ B x) ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event μ A + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event μ B := by
  classical
  simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hA : A x
  · by_cases hB : B x
    · simp only [hA, hB, if_true, mul_one, true_or]
      calc μ x = μ x * 1 := by ring
        _ ≤ μ x * 1 + μ x * 1 := le_add_of_nonneg_right (zero_le : (0 : ℝ≥0∞) ≤ μ x * 1)
        _ = μ x + μ x := by ring
    · simp [hA, hB]
  · by_cases hB : B x
    · simp [hA, hB]
    · simp [hA, hB]

/-- The probability of a union indexed by a finite set is at most the sum of the event
probabilities. -/
theorem event_finite_union_le {α ι : Type*} (μ : PMF α) (s : Finset ι) (Q : ι → α → Prop) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event μ (fun x => ∃ i ∈ s, Q i x) ≤ ∑ i ∈ s, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event μ (Q i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hnone : (fun x => ∃ i ∈ (∅ : Finset ι), Q i x) = fun _ => False := by
        funext x
        exact propext ⟨fun hex => absurd hex.choose_spec.1 (Finset.notMem_empty _),
          fun h => h.elim⟩
      have hz : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event μ (fun _ => False) = 0 := by
        simp [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event]
      rw [hnone, hz]
      simp
  | insert a s ha ih =>
      have hsplit : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event μ (fun x => ∃ i ∈ insert a s, Q i x)
          ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event μ (Q a) + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event μ (fun x => ∃ i ∈ s, Q i x) := by
        have heq : (fun x => ∃ i ∈ insert a s, Q i x)
            = fun x => Q a x ∨ ∃ i ∈ s, Q i x := by
          funext x
          apply propext
          constructor
          · rintro ⟨i, hi, hQ⟩
            rcases Finset.mem_insert.mp hi with rfl | hi'
            · exact Or.inl hQ
            · exact Or.inr ⟨i, hi', hQ⟩
          · rintro (hQ | ⟨i, hi, hQ⟩)
            · exact ⟨a, Finset.mem_insert.mpr (Or.inl rfl), hQ⟩
            · exact ⟨i, Finset.mem_insert.mpr (Or.inr hi), hQ⟩
        rw [heq]
        exact event_or_le μ (Q a) (fun x => ∃ i ∈ s, Q i x)
      calc Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event μ (fun x => ∃ i ∈ insert a s, Q i x)
          ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event μ (Q a) + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event μ (fun x => ∃ i ∈ s, Q i x) := hsplit
        _ ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event μ (Q a) + ∑ i ∈ s, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event μ (Q i) :=
            add_le_add (le_refl _) ih
        _ = ∑ i ∈ insert a s, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event μ (Q i) := by rw [Finset.sum_insert ha]

/-- The initial posterior ratio associated with an ordered pair. -/
noncomputable def cutUnionWeight {n : ℕ} (a₀ : Fin n → ℝ) (pr : Fin n × Fin n) : ℝ :=
    a₀ pr.1 / a₀ pr.2

/-- The sum of the initial ratios for pairs in `S`, divided by the common threshold `R`. -/
noncomputable def cutUnionBound {n : ℕ} (S : Finset (Fin n × Fin n)) (a₀ : Fin n → ℝ) (R : ℝ) : ℝ :=
  (∑ pr ∈ S, cutUnionWeight a₀ pr) / R

/-- For positive `R`, a sum of pair weights at most `δ * R` gives `cutUnionBound S a₀ R ≤ δ`. -/
theorem cutUnionBound_le {n : ℕ} (S : Finset (Fin n × Fin n)) (a₀ : Fin n → ℝ) (R δ : ℝ)
    (hR : 0 < R) (hW : (∑ pr ∈ S, cutUnionWeight a₀ pr) ≤ δ * R) :
    cutUnionBound S a₀ R ≤ δ := by
  rw [cutUnionBound, div_le_iff₀ hR]
  exact hW

/-- For pairs satisfying `crossSide`, positive `R`, and `1 / 2 < p < 1`, the probability of any
crossing after a finite union absorbing run is at most `ENNReal.ofReal (cutUnionBound S a₀
R)` for a positive prior of mass at most one. -/
theorem cut_union_event_bound {n : ℕ} (hn : 0 < n) (j : Fin n) (p ε R : ℝ)
    (S : Finset (Fin n × Fin n)) (hside : ∀ pr ∈ S, crossSide j pr.1 pr.2)
    (hp : 1 / 2 < p) (hp1 : p < 1) (hR : 0 < R)
    (a₀ : Fin n → ℝ) (hpos : ∀ m, 0 < a₀ m) (hsum : (∑ m, a₀ m) ≤ 1)
    (fuel : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (unionAbsorbNext hn j p ε R S) fuel (Sum.inr a₀))
      (fun x => ∃ pr ∈ S, R * configPosterior x.1 pr.2 ≤ configPosterior x.1 pr.1) ≤
      ENNReal.ofReal (cutUnionBound S a₀ R) := by
  have hpos' : ∀ pr ∈ S, 0 ≤ cutUnionWeight a₀ pr / R := by
    intro pr _
    exact div_nonneg (div_nonneg (hpos pr.1).le (hpos pr.2).le) hR.le
  calc Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (unionAbsorbNext hn j p ε R S) fuel (Sum.inr a₀))
        (fun x => ∃ pr ∈ S, R * configPosterior x.1 pr.2 ≤ configPosterior x.1 pr.1)
      ≤ ∑ pr ∈ S, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (unionAbsorbNext hn j p ε R S) fuel (Sum.inr a₀))
          (fun x => R * configPosterior x.1 pr.2 ≤ configPosterior x.1 pr.1) :=
        (@event_finite_union_le (Configuration (Fin n → ℝ) (Fin n → ℝ) × ℕ) (Fin n × Fin n)
          (runFor (unionAbsorbNext hn j p ε R S) fuel (Sum.inr a₀)) S
          (fun pr x => R * configPosterior x.1 pr.2 ≤ configPosterior x.1 pr.1))
    _ ≤ ∑ pr ∈ S, ENNReal.ofReal (cutUnionWeight a₀ pr / R) :=
        Finset.sum_le_sum fun pr hpr =>
          union_pair_crossing hn j pr.1 pr.2 p ε R S hpr (hside pr hpr) hp hp1 hR
            a₀ hpos hsum fuel
    _ = ENNReal.ofReal (∑ pr ∈ S, cutUnionWeight a₀ pr / R) :=
        (ENNReal.ofReal_sum_of_nonneg hpos').symm
    _ = ENNReal.ofReal (cutUnionBound S a₀ R) := by
        rw [cutUnionBound, Finset.sum_div]

/-- The finite set of all ordered pairs satisfying `crossSide` for the truth index `j`. -/
noncomputable def fullCrossPairs {n : ℕ} (j : Fin n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun pr => crossSide j pr.1 pr.2)

/-- Every member of `fullCrossPairs j` satisfies `crossSide j`. -/
theorem fullCrossPairs_side {n : ℕ} (j : Fin n) (pr : Fin n × Fin n)
    (hpr : pr ∈ fullCrossPairs j) : crossSide j pr.1 pr.2 := by
  rw [fullCrossPairs, Finset.mem_filter] at hpr
  exact hpr.2

/-- The maximum of one and the natural ceiling of `log x / log (p / (1 - p))`. -/
noncomputable def deviationExponent (p x : ℝ) : ℕ :=
  max 1 (Nat.ceil (Real.log x / Real.log (p / (1 - p))))

/-- Every natural power of a real number at least one is at least one. -/
theorem one_le_pow' {q : ℝ} (hq : 1 ≤ q) (r : ℕ) : 1 ≤ q ^ r := by
  induction r with
  | zero => norm_num
  | succ k ih =>
      have h1 : (1 : ℝ) * q ^ k ≤ q * q ^ k :=
        mul_le_mul_of_nonneg_right hq (pow_nonneg (le_trans zero_le_one hq) k)
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ 1 * q ^ k := by simpa using! ih
        _ ≤ q * q ^ k := h1
        _ = q ^ (k + 1) := by ring

/-- For `1 / 2 < p < 1` and positive `x`, the odds ratio raised to `deviationExponent p x` is at
least `x`. -/
theorem pow_deviationExponent_ge {p : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1)
    {x : ℝ} (hx : 0 < x) :
    x ≤ (p / (1 - p)) ^ (deviationExponent p x) := by
  have hq1 : 1 < p / (1 - p) := by
    rw [one_lt_div (by linarith : (0 : ℝ) < 1 - p)]
    linarith
  have hq0 : 0 < p / (1 - p) := lt_trans zero_lt_one hq1
  rcases le_or_gt x 1 with hx1 | hx1
  · calc x ≤ 1 := hx1
      _ ≤ (p / (1 - p)) ^ deviationExponent p x := one_le_pow' hq1.le _
  · have hlogq : 0 < Real.log (p / (1 - p)) := Real.log_pos hq1
    have hceil : Real.log x / Real.log (p / (1 - p))
        ≤ ((deviationExponent p x : ℕ) : ℝ) := by
      refine le_trans (Nat.le_ceil _) (Nat.cast_le.mpr ?_)
      exact le_max_right 1 _
    have hqtx : (p / (1 - p)) ^ (Real.log x / Real.log (p / (1 - p))) = x := by
      apply Real.log_injOn_pos (Real.rpow_pos_of_pos hq0 _) hx
      rw [Real.log_rpow hq0]
      field_simp [hlogq.ne']
    calc x = (p / (1 - p)) ^ (Real.log x / Real.log (p / (1 - p))) := hqtx.symm
      _ ≤ (p / (1 - p)) ^ ((deviationExponent p x : ℕ) : ℝ) :=
          (Real.rpow_le_rpow_left_iff hq1).mpr hceil
      _ = (p / (1 - p)) ^ deviationExponent p x := Real.rpow_natCast _ _

/-- The union bound over all crossing pairs at threshold `(p / (1 - p))^r`. -/
noncomputable def fullCutUnionBound {n : ℕ} (j : Fin n) (a₀ : Fin n → ℝ) (p : ℝ) (r : ℕ) : ℝ :=
  cutUnionBound (fullCrossPairs j) a₀ ((p / (1 - p)) ^ r)

/-- For any positive `δ`, noise parameter `1 / 2 < p < 1`, and positive prior of mass at most
one, a positive odds ratio exponent makes the full union absorbing crossing probability at
most `ENNReal.ofReal δ` for every fuel. -/
theorem cut_union_calibration {n : ℕ} (hn : 0 < n) (j : Fin n) (p ε δ : ℝ)
    (hp : 1 / 2 < p) (hp1 : p < 1) (hδ : 0 < δ)
    (a₀ : Fin n → ℝ) (hpos : ∀ m, 0 < a₀ m) (hsum : (∑ m, a₀ m) ≤ 1) :
    ∃ r : ℕ, 0 < r ∧ ∀ fuel : ℕ,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
        (runFor (unionAbsorbNext hn j p ε ((p / (1 - p)) ^ r) (fullCrossPairs j)) fuel
          (Sum.inr a₀))
        (fun x => ∃ pr ∈ fullCrossPairs j,
          (p / (1 - p)) ^ r * configPosterior x.1 pr.2 ≤ configPosterior x.1 pr.1) ≤
        ENNReal.ofReal δ := by
  have hq1 : 1 < p / (1 - p) := by
    rw [one_lt_div (by linarith : (0 : ℝ) < 1 - p)]
    linarith
  have hq0 : 0 < p / (1 - p) := lt_trans zero_lt_one hq1
  have hWnn : 0 ≤ ∑ pr ∈ fullCrossPairs j, cutUnionWeight a₀ pr :=
    Finset.sum_nonneg fun pr _ => div_nonneg (hpos pr.1).le (hpos pr.2).le
  refine ⟨deviationExponent p ((∑ pr ∈ fullCrossPairs j, cutUnionWeight a₀ pr) / δ),
    lt_of_lt_of_le zero_lt_one (le_max_left 1 _), fun fuel => ?_⟩
  have hRpos : 0 < (p / (1 - p)) ^ (deviationExponent p
      ((∑ pr ∈ fullCrossPairs j, cutUnionWeight a₀ pr) / δ)) := pow_pos hq0 _
  refine le_trans (cut_union_event_bound hn j p ε _ (fullCrossPairs j)
    (fun pr hpr => fullCrossPairs_side j pr hpr) hp hp1 hRpos a₀ hpos hsum fuel)
    (ENNReal.ofReal_le_ofReal ?_)
  refine cutUnionBound_le _ _ _ _ hRpos ?_
  rcases eq_or_lt_of_le hWnn with hW | hW
  · rw [← hW]
    exact mul_nonneg hδ.le (pow_nonneg hq0.le _)
  · have hqge := pow_deviationExponent_ge hp hp1 (div_pos hW hδ)
    calc ∑ pr ∈ fullCrossPairs j, cutUnionWeight a₀ pr
        = (∑ pr ∈ fullCrossPairs j, cutUnionWeight a₀ pr) / δ * δ :=
          (div_mul_cancel₀ _ hδ.ne').symm
      _ ≤ (p / (1 - p)) ^ (deviationExponent p
            ((∑ pr ∈ fullCrossPairs j, cutUnionWeight a₀ pr) / δ)) * δ :=
            mul_le_mul_of_nonneg_right hqge hδ.le
      _ = δ * (p / (1 - p)) ^ (deviationExponent p
            ((∑ pr ∈ fullCrossPairs j, cutUnionWeight a₀ pr) / δ)) :=
            mul_comm _ _

/-- For `1 / 2 < p < 1`, the Bernoulli law defined using `truthAnswerProb` equals the ordered
search answer law `answerPMF`. -/
theorem run_answerPMF {n : ℕ} (j c : Fin n) {p : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) :
    (PMF.bernoulli (truthAnswerProb j c p)
        (clampProb_le (if (c : ℕ) ≤ (j : ℕ) then p else 1 - p))) =
    answerPMF ⟨p, by linarith, hp1⟩ j c := rfl

/-- An implication between two events on the support of a probability mass function gives the
corresponding inequality of event probabilities. -/
theorem event_mono {α : Type*} (μ : PMF α) {E F : α → Prop}
    (h : ∀ x ∈ μ.support, E x → F x) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event μ E ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event μ F := by
  classical
  simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : E x
  · by_cases hxs : x ∈ μ.support
    · rw [if_pos hx, if_pos (h x hxs hx)]
    · rw [if_pos hx, show μ x = 0 from by simpa [PMF.mem_support_iff] using! hxs,
        zero_mul]
      simp
  · rw [if_neg hx]
    simp

/-- A length `l` window immediately preceding `u`, with `0 < l ≤ u`, contains an entry at most
`1 / l` whenever the entries are nonnegative and sum to at most one. -/
theorem window_light_cell_le {n : ℕ} (a : Fin n → ℝ) (u : Fin n) (l : ℕ) (hl : 0 < l)
    (hul : l ≤ (u : ℕ)) (ha0 : ∀ m, 0 ≤ a m) (hsum : (∑ m, a m) ≤ 1) :
    ∃ k : Fin n, ((u : ℕ) - l ≤ (k : ℕ) ∧ (k : ℕ) < (u : ℕ)) ∧ a k ≤ 1 / (l : ℝ) := by
  classical
  by_contra hcon
  push Not at hcon
  set W : Finset (Fin n) :=
    Finset.univ.filter fun k => (u : ℕ) - l ≤ (k : ℕ) ∧ (k : ℕ) < (u : ℕ) with hWdef
  have hcard : W.card = l := by
    have himg : W.image Fin.val = Finset.Ico ((u : ℕ) - l) (u : ℕ) := by
      ext m
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_Ico, hWdef]
      constructor
      · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
        exact ⟨hk1, hk2⟩
      · intro ⟨hm1, hm2⟩
        exact ⟨⟨m, lt_trans hm2 (Fin.isLt u)⟩, ⟨hm1, hm2⟩, rfl⟩
    rw [← Finset.card_image_of_injOn (fun x _ y _ h => Fin.val_injective h), himg, Nat.card_Ico,
      Nat.sub_sub_self hul]
  have hWne : W.Nonempty := Finset.card_pos.mp (by rw [hcard]; omega)
  have hone : (1 : ℝ) = ∑ k ∈ W, 1 / (l : ℝ) := by
    have h1 : (∑ k ∈ W, 1 / (l : ℝ)) = (∑ _k ∈ W, (1 : ℝ)) / (l : ℝ) :=
      (Finset.sum_div _ _ _).symm
    have h2 : (∑ _k ∈ W, (1 : ℝ)) = (W.card : ℝ) := by
      rw [Finset.sum_const, Nat.smul_one_eq_cast]
    have hlR : ((l : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hl)
    rw [h1, h2, hcard, div_self hlR]
  have hlt : ∑ k ∈ W, 1 / (l : ℝ) < ∑ k ∈ W, a k := by
    refine Finset.sum_lt_sum_of_nonempty hWne fun k hk => ?_
    simp only [hWdef, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact hcon k hk
  have hle : ∑ k ∈ W, a k ≤ ∑ m, a m := by
    apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun m _ _ => ha0 m)
    rw [hWdef]
    exact Finset.filter_subset _ _
  linarith

/-- The finite set of pairs `(u, v)` with `j < v < u` and `u - l ≤ v`. -/
noncomputable def windowCrossPairs {n : ℕ} (j : Fin n) (l : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun pr =>
    (j : ℕ) < (pr.2 : ℕ) ∧ (pr.1 : ℕ) - l ≤ (pr.2 : ℕ) ∧ (pr.2 : ℕ) < (pr.1 : ℕ))

/-- Every pair in `windowCrossPairs j l` satisfies `crossSide j`. -/
theorem windowCrossPairs_side {n : ℕ} (j : Fin n) (l : ℕ) (pr : Fin n × Fin n)
    (hpr : pr ∈ windowCrossPairs j l) : crossSide j pr.1 pr.2 := by
  rw [windowCrossPairs, Finset.mem_filter] at hpr
  exact Or.inl ⟨hpr.2.1, hpr.2.2.2⟩

/-- If `j + l < u`, `l > 0`, and a nonnegative vector of mass at most one has `b u ≥ ε > 0`,
some `k` in the preceding window satisfies `j < k < u` and `(ε * l) * b k ≤ b u`. -/
theorem far_heavy_window_crossing {n : ℕ} (j u : Fin n) (l : ℕ) (hl : 0 < l)
    (hju : (j : ℕ) + l < (u : ℕ)) {ε : ℝ} (hε : 0 < ε)
    (b : Fin n → ℝ) (hb0 : ∀ m, 0 ≤ b m) (hbsum : (∑ m, b m) ≤ 1) (hεu : ε ≤ b u) :
    ∃ k : Fin n, (j : ℕ) < (k : ℕ) ∧ (u : ℕ) - l ≤ (k : ℕ) ∧ (k : ℕ) < (u : ℕ) ∧
      (ε * (l : ℝ)) * b k ≤ b u := by
  have hul : l ≤ (u : ℕ) := by omega
  obtain ⟨k, ⟨hk1, hk2⟩, hkle⟩ := window_light_cell_le b u l hl hul hb0 hbsum
  refine ⟨k, ?_, hk1, hk2, ?_⟩
  · omega
  · have hlR : ((l : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hl)
    calc (ε * (l : ℝ)) * b k ≤ (ε * (l : ℝ)) * (1 / (l : ℝ)) :=
          mul_le_mul_of_nonneg_left hkle (mul_nonneg hε.le (Nat.cast_nonneg l))
      _ = ε := by
          rw [mul_assoc, mul_div_cancel₀ 1 hlR, mul_one]
      _ ≤ b u := hεu

/-- For `1 / 2 < p < 1`, every supported result of a finite union absorbing run preserves
`truthInv` from the initial configuration. -/
theorem unionAbsorb_run_inv {n : ℕ} (hn : 0 < n) (j : Fin n) (p ε R : ℝ)
    (S : Finset (Fin n × Fin n)) (hp : 1 / 2 < p) (hp1 : p < 1)
    (cfg : Configuration (Fin n → ℝ) (Fin n → ℝ)) (hI : truthInv (configPosterior cfg))
    (fuel : ℕ) :
    ∀ x ∈ (runFor (unionAbsorbNext hn j p ε R S) fuel cfg).support,
      truthInv (configPosterior x.1) := by
  induction fuel generalizing cfg with
  | zero =>
      intro x hx
      rw [runFor_zero] at hx
      obtain rfl := (PMF.mem_support_pure_iff _ _).mp hx
      exact hI
  | succ fuel ih =>
      intro x hx
      cases cfg with
      | inl out =>
          rw [runFor_halted] at hx
          obtain rfl := (PMF.mem_support_pure_iff _ _).mp hx
          exact hI
      | inr s =>
          rw [show runFor (unionAbsorbNext hn j p ε R S) (fuel + 1) (Sum.inr s)
                = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind (tick (unionAbsorbNext hn j p ε R S) (Sum.inr s))
                    (runFor (unionAbsorbNext hn j p ε R S) fuel) from rfl] at hx
          obtain ⟨y, hy, hx⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
          rw [tick] at hy
          obtain ⟨z, hz, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
          have hzI : truthInv (configPosterior z) := by
            refine unionAbsorb_support_inv hn j p ε R S hp hp1 s ?_ z hz
            exact hI
          rw [show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge 1 (runFor (unionAbsorbNext hn j p ε R S) fuel z)
                = PMF.map (fun w => (w.1, 1 + w.2))
                    (runFor (unionAbsorbNext hn j p ε R S) fuel z) from rfl] at hx
          obtain ⟨w, hw, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
          exact ih z hzI w hw

/-- Under the stated noise and positive prior hypotheses, the union absorbing probability that
some `u > j + l` has posterior at least positive `ε` is bounded by the window pair union
bound at threshold `ε * l`. -/
theorem far_heavy_window_bound {n : ℕ} (hn : 0 < n) (j : Fin n) (p ε : ℝ)
    (hp : 1 / 2 < p) (hp1 : p < 1) (hε : 0 < ε) (l : ℕ) (hl : 0 < l)
    (a₀ : Fin n → ℝ) (hpos : ∀ m, 0 < a₀ m) (hsum : (∑ m, a₀ m) ≤ 1)
    (fuel : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
      (runFor (unionAbsorbNext hn j p ε (ε * (l : ℝ)) (windowCrossPairs j l)) fuel
        (Sum.inr a₀))
      (fun x => ∃ u : Fin n, ((j : ℕ) + l < (u : ℕ)) ∧ ε ≤ configPosterior x.1 u) ≤
      ENNReal.ofReal (cutUnionBound (windowCrossPairs j l) a₀ (ε * (l : ℝ))) := by
  refine le_trans (event_mono _
    (fun x hxs ⟨u, hju, hεu⟩ => ?_))
    (cut_union_event_bound hn j p ε _ (windowCrossPairs j l)
      (fun pr hpr => windowCrossPairs_side j l pr hpr) hp hp1
      (mul_pos hε (Nat.cast_pos.mpr hl)) a₀ hpos hsum fuel)
  have hI := unionAbsorb_run_inv hn j p ε (ε * (l : ℝ)) (windowCrossPairs j l) hp hp1
    (Sum.inr a₀) ⟨hpos, hsum⟩ fuel x hxs
  have hb0 : ∀ m, 0 ≤ configPosterior x.1 m := fun m => le_of_lt (hI.1 m)
  obtain ⟨k, hkj, hk1, hk2, hcross⟩ :=
    far_heavy_window_crossing j u l hl hju hε (configPosterior x.1) hb0 hI.2 hεu
  exact ⟨(u, k),
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hkj, hk1, hk2⟩⟩, hcross⟩

/-- For any positive error target and positive window length, a positive odds ratio exponent
makes the union absorbing probability of a cell beyond `j + l` reaching mass `(p / (1 -
p))^r / l` at most that target for every fuel, under the noise and prior hypotheses. -/
theorem far_heavy_window_calibration {n : ℕ} (hn : 0 < n) (j : Fin n) (p δ : ℝ)
    (hp : 1 / 2 < p) (hp1 : p < 1) (hδ : 0 < δ) (l : ℕ) (hl : 0 < l)
    (a₀ : Fin n → ℝ) (hpos : ∀ m, 0 < a₀ m) (hsum : (∑ m, a₀ m) ≤ 1) :
    ∃ r : ℕ, 0 < r ∧ ∀ fuel : ℕ,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
        (runFor (unionAbsorbNext hn j p ((p / (1 - p)) ^ r / (l : ℝ))
          ((p / (1 - p)) ^ r) (windowCrossPairs j l)) fuel (Sum.inr a₀))
        (fun x => ∃ u : Fin n, ((j : ℕ) + l < (u : ℕ)) ∧
          (p / (1 - p)) ^ r / (l : ℝ) ≤ configPosterior x.1 u) ≤
        ENNReal.ofReal δ := by
  have hq1 : 1 < p / (1 - p) := by
    rw [one_lt_div (by linarith : (0 : ℝ) < 1 - p)]
    linarith
  have hq0 : 0 < p / (1 - p) := lt_trans zero_lt_one hq1
  have hWnn : 0 ≤ ∑ pr ∈ windowCrossPairs j l, cutUnionWeight a₀ pr :=
    Finset.sum_nonneg fun pr _ => div_nonneg (hpos pr.1).le (hpos pr.2).le
  refine ⟨deviationExponent p ((∑ pr ∈ windowCrossPairs j l, cutUnionWeight a₀ pr) / δ),
    lt_of_lt_of_le zero_lt_one (le_max_left 1 _), fun fuel => ?_⟩
  have hkey := far_heavy_window_bound hn j p
    ((p / (1 - p)) ^ deviationExponent p
        ((∑ pr ∈ windowCrossPairs j l, cutUnionWeight a₀ pr) / δ) / (l : ℝ))
    hp hp1 (div_pos (pow_pos hq0 _) (Nat.cast_pos.mpr hl)) l hl a₀ hpos hsum fuel
  rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hl))] at hkey
  refine le_trans hkey (ENNReal.ofReal_le_ofReal ?_)
  refine cutUnionBound_le _ _ _ _ (pow_pos hq0 _) ?_
  rcases eq_or_lt_of_le hWnn with hW | hW
  · rw [← hW]
    exact mul_nonneg hδ.le (pow_nonneg hq0.le _)
  · have hqge := pow_deviationExponent_ge hp hp1 (div_pos hW hδ)
    calc ∑ pr ∈ windowCrossPairs j l, cutUnionWeight a₀ pr
        = (∑ pr ∈ windowCrossPairs j l, cutUnionWeight a₀ pr) / δ * δ :=
          (div_mul_cancel₀ _ hδ.ne').symm
      _ ≤ (p / (1 - p)) ^ deviationExponent p
            ((∑ pr ∈ windowCrossPairs j l, cutUnionWeight a₀ pr) / δ) * δ :=
          mul_le_mul_of_nonneg_right hqge hδ.le
      _ = δ * (p / (1 - p)) ^ deviationExponent p
            ((∑ pr ∈ windowCrossPairs j l, cutUnionWeight a₀ pr) / δ) :=
          mul_comm _ _

/-- For `j < k < i` and `1 / 2 < p < 1`, the truth driven learner step does not increase the
expected ratio potential `i / k`. -/
theorem trueLearner_one_step_right {n : ℕ} (hn : 0 < n) (j k i : Fin n) (p ε : ℝ)
    (hp : 1 / 2 < p) (hp1 : p < 1) (hjk : (j : ℕ) < (k : ℕ)) (hki : (k : ℕ) < (i : ℕ))
    (a : Fin n → ℝ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (trueLearnerNext hn j p ε a) (ratioPotential i k) ≤
      ratioPotential i k (Sum.inr a) := by
  by_cases hhalt : ∃ m : Fin n, ε ≤ a m
  · simp only [trueLearnerNext, dif_pos hhalt, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure]
    exact le_rfl
  · simp only [trueLearnerNext, dif_neg hhalt]
    have hbr := expectation_bernoulli_branches
      (q := truthAnswerProb j (stageTwoCut hn a ε) p)
      (clampProb_le (if (stageTwoCut hn a ε : ℕ) ≤ (j : ℕ) then p else 1 - p))
      (fun b => Sum.inr
        (if b then updateTrue a (stageTwoCut hn a ε) p
          else updateFalse a (stageTwoCut hn a ε) p))
      (ratioPotential i k)
    rw [hbr]
    simp only [ratioPotential, configPosterior, Sum.elim_inr, id_eq]
    rcases Classical.em ((i : ℕ) ≤ (stageTwoCut hn a ε : ℕ)) with hic | hic
    · have hside : ((i : ℕ) ≤ (stageTwoCut hn a ε : ℕ))
        = ((k : ℕ) ≤ (stageTwoCut hn a ε : ℕ)) := by
        simp [hic, le_trans (le_of_lt hki) hic]
      exact same_side_step_bound
        (q := truthAnswerProb j (stageTwoCut hn a ε) p)
        (clampProb_le (if (stageTwoCut hn a ε : ℕ) ≤ (j : ℕ) then p else 1 - p)) _ _ _
        (same_side_potential_le a _ i k p hside).1 (same_side_potential_le a _ i k p hside).2
    · rcases Classical.em ((k : ℕ) ≤ (stageTwoCut hn a ε : ℕ)) with hkc | hkc
      · have hcj : ¬ ((stageTwoCut hn a ε : ℕ) ≤ (j : ℕ)) := by omega
        obtain ⟨hw1, hw2⟩ := truthAnswerProb_weights j (stageTwoCut hn a ε) hp hp1
        rw [hw1, hw2]
        simp only [if_neg hcj]
        exact across_one_step_le a (stageTwoCut hn a ε) i k (by linarith) (by linarith)
          (by linarith) (by ring)
          (zoo_bayes_update_ratio_across_true a _ k i p hkc (by omega))
          (zoo_bayes_update_ratio_across_false a _ k i p hkc (by omega))
      · have hside : ((i : ℕ) ≤ (stageTwoCut hn a ε : ℕ))
          = ((k : ℕ) ≤ (stageTwoCut hn a ε : ℕ)) := by
          simp [hic, hkc]
        exact same_side_step_bound
          (q := truthAnswerProb j (stageTwoCut hn a ε) p)
          (clampProb_le (if (stageTwoCut hn a ε : ℕ) ≤ (j : ℕ) then p else 1 - p)) _ _ _
          (same_side_potential_le a _ i k p hside).1 (same_side_potential_le a _ i k p hside).2

/-- For `u < v < j` and `1 / 2 < p < 1`, the truth driven learner step does not increase the
expected ratio potential `u / v`. -/
theorem trueLearner_one_step_left {n : ℕ} (hn : 0 < n) (j u v : Fin n) (p ε : ℝ)
    (hp : 1 / 2 < p) (hp1 : p < 1) (huv : (u : ℕ) < (v : ℕ)) (hvj : (v : ℕ) < (j : ℕ))
    (a : Fin n → ℝ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (trueLearnerNext hn j p ε a) (ratioPotential u v) ≤
      ratioPotential u v (Sum.inr a) := by
  by_cases hhalt : ∃ m : Fin n, ε ≤ a m
  · simp only [trueLearnerNext, dif_pos hhalt, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure]
    exact le_rfl
  · simp only [trueLearnerNext, dif_neg hhalt]
    have hbr := expectation_bernoulli_branches
      (q := truthAnswerProb j (stageTwoCut hn a ε) p)
      (clampProb_le (if (stageTwoCut hn a ε : ℕ) ≤ (j : ℕ) then p else 1 - p))
      (fun b => Sum.inr
        (if b then updateTrue a (stageTwoCut hn a ε) p
          else updateFalse a (stageTwoCut hn a ε) p))
      (ratioPotential u v)
    rw [hbr]
    simp only [ratioPotential, configPosterior, Sum.elim_inr, id_eq]
    rcases Classical.em ((v : ℕ) ≤ (stageTwoCut hn a ε : ℕ)) with hic | hic
    · have hside : ((u : ℕ) ≤ (stageTwoCut hn a ε : ℕ))
        = ((v : ℕ) ≤ (stageTwoCut hn a ε : ℕ)) := by
        simp [hic, le_trans (le_of_lt huv) hic]
      exact same_side_step_bound
        (q := truthAnswerProb j (stageTwoCut hn a ε) p)
        (clampProb_le (if (stageTwoCut hn a ε : ℕ) ≤ (j : ℕ) then p else 1 - p)) _ _ _
        (same_side_potential_le a _ u v p hside).1 (same_side_potential_le a _ u v p hside).2
    · rcases Classical.em ((u : ℕ) ≤ (stageTwoCut hn a ε : ℕ)) with hkc | hkc
      · have hcj : (stageTwoCut hn a ε : ℕ) ≤ (j : ℕ) := by omega
        obtain ⟨hw1, hw2⟩ := truthAnswerProb_weights j (stageTwoCut hn a ε) hp hp1
        rw [hw1, hw2]
        simp only [if_pos hcj]
        refine across_one_step_le a (stageTwoCut hn a ε) u v (by linarith) (by linarith)
          (by linarith) (by ring) ?_ ?_
        · calc p * (updateTrue a (stageTwoCut hn a ε) p u * a v)
                = p * (a v * updateTrue a (stageTwoCut hn a ε) p u) := by ring
            _ = (1 - p) * (updateTrue a (stageTwoCut hn a ε) p v * a u) :=
                (zoo_bayes_update_ratio_across_true a _ u v p hkc (by omega)).symm
            _ = (1 - p) * (a u * updateTrue a (stageTwoCut hn a ε) p v) := by ring
        · calc (1 - p) * (updateFalse a (stageTwoCut hn a ε) p u * a v)
                = (1 - p) * (a v * updateFalse a (stageTwoCut hn a ε) p u) := by ring
            _ = p * (updateFalse a (stageTwoCut hn a ε) p v * a u) :=
                (zoo_bayes_update_ratio_across_false a _ u v p hkc (by omega)).symm
            _ = p * (a u * updateFalse a (stageTwoCut hn a ε) p v) := by ring
      · have hside : ((u : ℕ) ≤ (stageTwoCut hn a ε : ℕ))
          = ((v : ℕ) ≤ (stageTwoCut hn a ε : ℕ)) := by
          simp [hic, hkc]
        exact same_side_step_bound
          (q := truthAnswerProb j (stageTwoCut hn a ε) p)
          (clampProb_le (if (stageTwoCut hn a ε : ℕ) ≤ (j : ℕ) then p else 1 - p)) _ _ _
          (same_side_potential_le a _ u v p hside).1 (same_side_potential_le a _ u v p hside).2

/-- For `1 / 2 < p < 1`, every supported result of a finite truth driven learner run preserves
`truthInv` from the initial configuration. -/
theorem learner_run_inv {n : ℕ} (hn : 0 < n) (j : Fin n) (p ε : ℝ)
    (hp : 1 / 2 < p) (hp1 : p < 1)
    (cfg : Configuration (Fin n → ℝ) (Fin n → ℝ)) (hI : truthInv (configPosterior cfg))
    (fuel : ℕ) :
    ∀ x ∈ (runFor (trueLearnerNext hn j p ε) fuel cfg).support,
      truthInv (configPosterior x.1) := by
  induction fuel generalizing cfg with
  | zero =>
      intro x hx
      rw [runFor_zero] at hx
      obtain rfl := (PMF.mem_support_pure_iff _ _).mp hx
      exact hI
  | succ fuel ih =>
      intro x hx
      cases cfg with
      | inl out =>
          rw [runFor_halted] at hx
          obtain rfl := (PMF.mem_support_pure_iff _ _).mp hx
          exact hI
      | inr s =>
          rw [show runFor (trueLearnerNext hn j p ε) (fuel + 1) (Sum.inr s)
                = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind (tick (trueLearnerNext hn j p ε) (Sum.inr s))
                    (runFor (trueLearnerNext hn j p ε) fuel) from rfl] at hx
          obtain ⟨y, hy, hx⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
          rw [tick] at hy
          obtain ⟨z, hz, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
          have hzI : truthInv (configPosterior z) :=
            trueLearnerNext_support_inv hn j p ε hp hp1 s hI z hz
          rw [show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge 1 (runFor (trueLearnerNext hn j p ε) fuel z)
                = PMF.map (fun w => (w.1, 1 + w.2))
                    (runFor (trueLearnerNext hn j p ε) fuel z) from rfl] at hx
          obtain ⟨w, hw, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
          exact ih z hzI w hw

/-- For `j < k < i`, positive `R`, and `1 / 2 < p < 1`, the event `R * a k ≤ a i` after any
finite truth driven run is bounded by the initial ratio `a₀ i / a₀ k` divided by `R`, for a
positive prior of mass at most one. -/
theorem learner_pair_crossing_right {n : ℕ} (hn : 0 < n) (j k i : Fin n)
    (p ε R : ℝ) (hp : 1 / 2 < p) (hp1 : p < 1) (hR : 0 < R)
    (hjk : (j : ℕ) < (k : ℕ)) (hki : (k : ℕ) < (i : ℕ))
    (a₀ : Fin n → ℝ) (hpos : ∀ m, 0 < a₀ m) (hsum : (∑ m, a₀ m) ≤ 1)
    (fuel : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (trueLearnerNext hn j p ε) fuel (Sum.inr a₀))
      (fun x => R * configPosterior x.1 k ≤ configPosterior x.1 i) ≤
      ENNReal.ofReal ((a₀ i / a₀ k) / R) := by
  refine le_trans (ville_event_bound (trueLearnerNext hn j p ε)
    (ratioPotential i k)
    (fun cfg => R * configPosterior cfg k ≤ configPosterior cfg i)
    (fun cfg => truthInv (configPosterior cfg))
    (ENNReal.ofReal R)
    (ENNReal.ofReal_pos.mpr hR).ne'
    ENNReal.ofReal_ne_top
    (trueLearner_one_step_right hn j k i p ε hp hp1 hjk hki)
    (fun s hs cfg hcfg => trueLearnerNext_support_inv hn j p ε hp hp1 s hs cfg hcfg)
    (fun cfg hI hQ => ENNReal.ofReal_le_ofReal ((le_div_iff₀ (hI.1 k)).mpr hQ))
    fuel (Sum.inr a₀) ⟨hpos, hsum⟩) ?_
  rw [show ratioPotential i k (Sum.inr a₀) / ENNReal.ofReal R
      = ENNReal.ofReal ((a₀ i / a₀ k) / R) from by
    rw [ratioPotential, configPosterior, Sum.elim_inr, id_eq, ENNReal.ofReal_div_of_pos hR]]

/-- For `u < v < j`, positive `R`, and `1 / 2 < p < 1`, the event `R * a v ≤ a u` after any
finite truth driven run is bounded by the initial ratio `a₀ u / a₀ v` divided by `R`, for a
positive prior of mass at most one. -/
theorem learner_pair_crossing_left {n : ℕ} (hn : 0 < n) (j u v : Fin n)
    (p ε R : ℝ) (hp : 1 / 2 < p) (hp1 : p < 1) (hR : 0 < R)
    (huv : (u : ℕ) < (v : ℕ)) (hvj : (v : ℕ) < (j : ℕ))
    (a₀ : Fin n → ℝ) (hpos : ∀ m, 0 < a₀ m) (hsum : (∑ m, a₀ m) ≤ 1)
    (fuel : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (trueLearnerNext hn j p ε) fuel (Sum.inr a₀))
      (fun x => R * configPosterior x.1 v ≤ configPosterior x.1 u) ≤
      ENNReal.ofReal ((a₀ u / a₀ v) / R) := by
  refine le_trans (ville_event_bound (trueLearnerNext hn j p ε)
    (ratioPotential u v)
    (fun cfg => R * configPosterior cfg v ≤ configPosterior cfg u)
    (fun cfg => truthInv (configPosterior cfg))
    (ENNReal.ofReal R)
    (ENNReal.ofReal_pos.mpr hR).ne'
    ENNReal.ofReal_ne_top
    (trueLearner_one_step_left hn j u v p ε hp hp1 huv hvj)
    (fun s hs cfg hcfg => trueLearnerNext_support_inv hn j p ε hp hp1 s hs cfg hcfg)
    (fun cfg hI hQ => ENNReal.ofReal_le_ofReal ((le_div_iff₀ (hI.1 v)).mpr hQ))
    fuel (Sum.inr a₀) ⟨hpos, hsum⟩) ?_
  rw [show ratioPotential u v (Sum.inr a₀) / ENNReal.ofReal R
      = ENNReal.ofReal ((a₀ u / a₀ v) / R) from by
    rw [ratioPotential, configPosterior, Sum.elim_inr, id_eq, ENNReal.ofReal_div_of_pos hR]]

/-- For a pair satisfying `crossSide`, the ratio threshold event after any finite truth driven
learner run is bounded by the initial ratio divided by positive `R`, under the noise and
prior hypotheses. -/
theorem learner_pair_crossing {n : ℕ} (hn : 0 < n) (j u v : Fin n)
    (p ε R : ℝ) (hside : crossSide j u v)
    (hp : 1 / 2 < p) (hp1 : p < 1) (hR : 0 < R)
    (a₀ : Fin n → ℝ) (hpos : ∀ m, 0 < a₀ m) (hsum : (∑ m, a₀ m) ≤ 1)
    (fuel : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (trueLearnerNext hn j p ε) fuel (Sum.inr a₀))
      (fun x => R * configPosterior x.1 v ≤ configPosterior x.1 u) ≤
      ENNReal.ofReal ((a₀ u / a₀ v) / R) := by
  rcases hside with ⟨hjv, hvu⟩ | ⟨huv, hvj⟩
  · exact learner_pair_crossing_right hn j v u p ε R hp hp1 hR hjv hvu a₀ hpos hsum fuel
  · exact learner_pair_crossing_left hn j u v p ε R hp hp1 hR huv hvj a₀ hpos hsum fuel

/-- For pairs satisfying `crossSide`, the probability of any crossing after a finite truth
driven run is bounded by `ENNReal.ofReal (cutUnionBound S a₀ R)`, under the noise, positive
threshold, and prior hypotheses. -/
theorem learner_cut_union_event_bound {n : ℕ} (hn : 0 < n) (j : Fin n) (p ε R : ℝ)
    (S : Finset (Fin n × Fin n)) (hside : ∀ pr ∈ S, crossSide j pr.1 pr.2)
    (hp : 1 / 2 < p) (hp1 : p < 1) (hR : 0 < R)
    (a₀ : Fin n → ℝ) (hpos : ∀ m, 0 < a₀ m) (hsum : (∑ m, a₀ m) ≤ 1)
    (fuel : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (trueLearnerNext hn j p ε) fuel (Sum.inr a₀))
      (fun x => ∃ pr ∈ S, R * configPosterior x.1 pr.2 ≤ configPosterior x.1 pr.1) ≤
      ENNReal.ofReal (cutUnionBound S a₀ R) := by
  have hpos' : ∀ pr ∈ S, 0 ≤ cutUnionWeight a₀ pr / R := by
    intro pr _
    exact div_nonneg (div_nonneg (hpos pr.1).le (hpos pr.2).le) hR.le
  calc Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (trueLearnerNext hn j p ε) fuel (Sum.inr a₀))
        (fun x => ∃ pr ∈ S, R * configPosterior x.1 pr.2 ≤ configPosterior x.1 pr.1)
      ≤ ∑ pr ∈ S, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (trueLearnerNext hn j p ε) fuel (Sum.inr a₀))
          (fun x => R * configPosterior x.1 pr.2 ≤ configPosterior x.1 pr.1) :=
        (@event_finite_union_le (Configuration (Fin n → ℝ) (Fin n → ℝ) × ℕ) (Fin n × Fin n)
          (runFor (trueLearnerNext hn j p ε) fuel (Sum.inr a₀)) S
          (fun pr x => R * configPosterior x.1 pr.2 ≤ configPosterior x.1 pr.1))
    _ ≤ ∑ pr ∈ S, ENNReal.ofReal (cutUnionWeight a₀ pr / R) :=
        Finset.sum_le_sum fun pr hpr =>
          learner_pair_crossing hn j pr.1 pr.2 p ε R (hside pr hpr) hp hp1 hR
            a₀ hpos hsum fuel
    _ = ENNReal.ofReal (∑ pr ∈ S, cutUnionWeight a₀ pr / R) :=
        (ENNReal.ofReal_sum_of_nonneg hpos').symm
    _ = ENNReal.ofReal (cutUnionBound S a₀ R) := by
        rw [cutUnionBound, Finset.sum_div]

/-- Under the stated noise and prior hypotheses, the probability after a finite truth driven run
that some `u > j + l` has posterior at least positive `ε` is bounded by the window pair
union bound at threshold `ε * l`. -/
theorem learner_far_heavy_window_bound {n : ℕ} (hn : 0 < n) (j : Fin n) (p ε : ℝ)
    (hp : 1 / 2 < p) (hp1 : p < 1) (hε : 0 < ε) (l : ℕ) (hl : 0 < l)
    (a₀ : Fin n → ℝ) (hpos : ∀ m, 0 < a₀ m) (hsum : (∑ m, a₀ m) ≤ 1)
    (fuel : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (trueLearnerNext hn j p ε) fuel (Sum.inr a₀))
      (fun x => ∃ u : Fin n, ((j : ℕ) + l < (u : ℕ)) ∧ ε ≤ configPosterior x.1 u) ≤
      ENNReal.ofReal (cutUnionBound (windowCrossPairs j l) a₀ (ε * (l : ℝ))) := by
  refine le_trans (event_mono _
    (fun x hxs ⟨u, hju, hεu⟩ => ?_))
    (learner_cut_union_event_bound hn j p ε _ (windowCrossPairs j l)
      (fun pr hpr => windowCrossPairs_side j l pr hpr) hp hp1
      (mul_pos hε (Nat.cast_pos.mpr hl)) a₀ hpos hsum fuel)
  have hI := learner_run_inv hn j p ε hp hp1 (Sum.inr a₀) ⟨hpos, hsum⟩ fuel x hxs
  have hb0 : ∀ m, 0 ≤ configPosterior x.1 m := fun m => le_of_lt (hI.1 m)
  obtain ⟨k, hkj, hk1, hk2, hcross⟩ :=
    far_heavy_window_crossing j u l hl hju hε (configPosterior x.1) hb0 hI.2 hεu
  exact ⟨(u, k),
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hkj, hk1, hk2⟩⟩, hcross⟩

/-- If some posterior entry is at least `ε`, the entry chosen by `haltCut` is at least `ε`. -/
theorem haltCut_heavy {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ε : ℝ)
    (h : ∃ i : Fin n, ε ≤ a i) : ε ≤ a (haltCut hn a ε) := by
  have hne : (Finset.univ.filter fun i : Fin n => ε ≤ a i).Nonempty :=
    ⟨h.choose, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.choose_spec⟩⟩
  rw [haltCut, dif_pos hne]
  exact (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2

/-- The probability of a halted truth driven configuration with an entry beyond `j + l` of mass
at least `ε` is bounded by the window pair union bound at threshold `ε * l`, under the
stated hypotheses. -/
theorem learner_eps_halt_far_bound {n : ℕ} (hn : 0 < n) (j : Fin n) (p ε : ℝ)
    (hp : 1 / 2 < p) (hp1 : p < 1) (hε : 0 < ε) (l : ℕ) (hl : 0 < l)
    (a₀ : Fin n → ℝ) (hpos : ∀ m, 0 < a₀ m) (hsum : (∑ m, a₀ m) ≤ 1)
    (fuel : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (trueLearnerNext hn j p ε) fuel (Sum.inr a₀))
      (fun x => (∃ o : Fin n → ℝ, x.1 = Sum.inl o) ∧
        ∃ u : Fin n, ((j : ℕ) + l < (u : ℕ)) ∧ ε ≤ configPosterior x.1 u) ≤
      ENNReal.ofReal (cutUnionBound (windowCrossPairs j l) a₀ (ε * (l : ℝ))) := by
  refine le_trans (event_mono _ (fun x _ hx => hx.2)) ?_
  exact learner_far_heavy_window_bound hn j p ε hp hp1 hε l hl a₀ hpos hsum fuel

/-- The probability that some entry reaches `ε` and `haltCut` selects an index beyond `j + l` is
bounded by the window pair union bound at threshold `ε * l`, under the stated hypotheses. -/
theorem learner_haltCut_far_bound {n : ℕ} (hn : 0 < n) (j : Fin n) (p ε : ℝ)
    (hp : 1 / 2 < p) (hp1 : p < 1) (hε : 0 < ε) (l : ℕ) (hl : 0 < l)
    (a₀ : Fin n → ℝ) (hpos : ∀ m, 0 < a₀ m) (hsum : (∑ m, a₀ m) ≤ 1)
    (fuel : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (trueLearnerNext hn j p ε) fuel (Sum.inr a₀))
      (fun x => (∃ i : Fin n, ε ≤ configPosterior x.1 i) ∧
        (j : ℕ) + l < ((haltCut hn (configPosterior x.1) ε : ℕ))) ≤
      ENNReal.ofReal (cutUnionBound (windowCrossPairs j l) a₀ (ε * (l : ℝ))) := by
  refine le_trans (event_mono _ (fun x _ hx => ?_))
    (learner_far_heavy_window_bound hn j p ε hp hp1 hε l hl a₀ hpos hsum fuel)
  exact ⟨haltCut hn (configPosterior x.1) ε, hx.2, haltCut_heavy hn _ ε hx.1⟩

/-- The finite set of pairs with first coordinate `u` and second coordinate in the length `l`
window immediately preceding `u`. -/
noncomputable def singleWindowPairs {n : ℕ} (u : Fin n) (l : ℕ) :
    Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun pr =>
    pr.1 = u ∧ (u : ℕ) - l ≤ (pr.2 : ℕ) ∧ (pr.2 : ℕ) < (u : ℕ))

/-- There are at most `l` pairs in `singleWindowPairs u l`. -/
theorem singleWindowPairs_card_le {n : ℕ} (u : Fin n) (l : ℕ) :
    (singleWindowPairs u l).card ≤ l := by
  classical
  let f : Fin n × Fin n → ℕ := fun pr => (pr.2 : ℕ) - ((u : ℕ) - l)
  have hmap : Set.MapsTo f (singleWindowPairs u l) (Finset.range l) := by
    intro pr hpr
    have h1 : (u : ℕ) - l ≤ (pr.2 : ℕ) := (Finset.mem_filter.mp hpr).2.2.1
    have h2 : (pr.2 : ℕ) < (u : ℕ) := (Finset.mem_filter.mp hpr).2.2.2
    refine Finset.mem_range.mpr ?_
    show (pr.2 : ℕ) - ((u : ℕ) - l) < l
    omega
  have hinj : Set.InjOn f (singleWindowPairs u l) := by
    intro a ha b hb hab
    have hae : a.1 = u := (Finset.mem_filter.mp ha).2.1
    have hbe : b.1 = u := (Finset.mem_filter.mp hb).2.1
    have ha1 : (u : ℕ) - l ≤ (a.2 : ℕ) := (Finset.mem_filter.mp ha).2.2.1
    have hb1 : (u : ℕ) - l ≤ (b.2 : ℕ) := (Finset.mem_filter.mp hb).2.2.1
    have hab' : (a.2 : ℕ) - ((u : ℕ) - l) = (b.2 : ℕ) - ((u : ℕ) - l) := hab
    have hval : (a.2 : ℕ) = (b.2 : ℕ) := by omega
    exact Prod.ext (by rw [hae, hbe]) (Fin.val_injective hval)
  have hle := Finset.card_le_card_of_injOn f hmap hinj
  rw [Finset.card_range] at hle
  exact hle

/-- If `j + l < u`, every pair in `singleWindowPairs u l` satisfies `crossSide j`. -/
theorem singleWindowPairs_side {n : ℕ} (j u : Fin n) (l : ℕ)
    (hjul : (j : ℕ) + l < (u : ℕ)) (pr : Fin n × Fin n)
    (hpr : pr ∈ singleWindowPairs u l) : crossSide j pr.1 pr.2 := by
  simp only [singleWindowPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hpr
  rw [hpr.1]
  exact Or.inl ⟨by omega, hpr.2.2⟩

/-- For fixed `u > j + l`, the probability after a finite truth driven run that its posterior
reaches positive `ε` is bounded by the single window union bound at threshold `ε * l`, under
the noise and prior hypotheses. -/
theorem learner_far_heavy_single_bound {n : ℕ} (hn : 0 < n) (j u : Fin n) (l : ℕ)
    (hl : 0 < l) (hjul : (j : ℕ) + l < (u : ℕ))
    (p ε : ℝ) (hp : 1 / 2 < p) (hp1 : p < 1) (hε : 0 < ε)
    (a₀ : Fin n → ℝ) (hpos : ∀ m, 0 < a₀ m) (hsum : (∑ m, a₀ m) ≤ 1)
    (fuel : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (trueLearnerNext hn j p ε) fuel (Sum.inr a₀))
      (fun x => ε ≤ configPosterior x.1 u) ≤
      ENNReal.ofReal (cutUnionBound (singleWindowPairs u l) a₀ (ε * (l : ℝ))) := by
  refine le_trans (event_mono _ (fun x hxs hεu => ?_))
    (learner_cut_union_event_bound hn j p ε _ (singleWindowPairs u l)
      (singleWindowPairs_side j u l hjul) hp hp1 (mul_pos hε (Nat.cast_pos.mpr hl))
      a₀ hpos hsum fuel)
  have hI := learner_run_inv hn j p ε hp hp1 (Sum.inr a₀) ⟨hpos, hsum⟩ fuel x hxs
  have hb0 : ∀ m, 0 ≤ configPosterior x.1 m := fun m => le_of_lt (hI.1 m)
  obtain ⟨k, hkj, hk1, hk2, hcross⟩ :=
    far_heavy_window_crossing j u l hl hjul hε (configPosterior x.1) hb0 hI.2 hεu
  exact ⟨(u, k), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨rfl, hk1, hk2⟩⟩, hcross⟩

/-- For a constant positive prior of mass at most one and `u > j + l`, the probability that the
posterior at `u` reaches positive `ε` after any finite truth driven run is at most
`ENNReal.ofReal (1 / ε)`, under the noise hypotheses. -/
theorem learner_far_heavy_single_uniform {n : ℕ} (hn : 0 < n) (j u : Fin n) (l : ℕ)
    (hl : 0 < l) (hjul : (j : ℕ) + l < (u : ℕ))
    (p ε : ℝ) (hp : 1 / 2 < p) (hp1 : p < 1) (hε : 0 < ε)
    (c : ℝ) (hc : 0 < c) (a₀ : Fin n → ℝ) (ha₀ : ∀ m, a₀ m = c)
    (hsum : (∑ m, a₀ m) ≤ 1) (fuel : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (trueLearnerNext hn j p ε) fuel (Sum.inr a₀))
      (fun x => ε ≤ configPosterior x.1 u) ≤ ENNReal.ofReal (1 / ε) := by
  refine le_trans (learner_far_heavy_single_bound hn j u l hl hjul p ε hp hp1 hε
    a₀ (fun m => by rw [ha₀ m]; exact hc) hsum fuel) (ENNReal.ofReal_le_ofReal ?_)
  have hlR : ((l : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hl)
  have hwt : ∀ pr ∈ singleWindowPairs u l, cutUnionWeight a₀ pr = 1 := by
    intro pr _
    rw [cutUnionWeight, ha₀ pr.1, ha₀ pr.2, div_self hc.ne']
  have hsum' : ∑ pr ∈ singleWindowPairs u l, cutUnionWeight a₀ pr ≤ (l : ℝ) := by
    calc ∑ pr ∈ singleWindowPairs u l, cutUnionWeight a₀ pr
        = ∑ _pr ∈ singleWindowPairs u l, 1 :=
          Finset.sum_congr rfl fun pr hpr => hwt pr hpr
      _ = ((singleWindowPairs u l).card : ℝ) := by rw [Finset.sum_const, Nat.smul_one_eq_cast]
      _ ≤ (l : ℝ) := by exact_mod_cast singleWindowPairs_card_le u l
  rw [cutUnionBound]
  have hεl : 0 < ε * (l : ℝ) := by positivity
  calc (∑ pr ∈ singleWindowPairs u l, cutUnionWeight a₀ pr) / (ε * (l : ℝ))
      ≤ (l : ℝ) / (ε * (l : ℝ)) := by
        rw [div_le_div_iff₀ hεl hεl]
        exact mul_le_mul_of_nonneg_right hsum' hεl.le
    _ = 1 / ε := by
        rw [div_eq_div_iff (mul_ne_zero hε.ne' hlR) hε.ne', one_mul]
        ring

/-- For any positive error target and positive window length, a positive odds ratio exponent
makes the truth driven probability of a cell beyond `j + l` reaching mass `(p / (1 - p))^r /
l` at most that target for every fuel, under the noise and prior hypotheses. -/
theorem learner_far_heavy_calibration {n : ℕ} (hn : 0 < n) (j : Fin n) (p δ : ℝ)
    (hp : 1 / 2 < p) (hp1 : p < 1) (hδ : 0 < δ) (l : ℕ) (hl : 0 < l)
    (a₀ : Fin n → ℝ) (hpos : ∀ m, 0 < a₀ m) (hsum : (∑ m, a₀ m) ≤ 1) :
    ∃ r : ℕ, 0 < r ∧ ∀ fuel : ℕ,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
        (runFor (trueLearnerNext hn j p ((p / (1 - p)) ^ r / (l : ℝ))) fuel
          (Sum.inr a₀))
        (fun x => ∃ u : Fin n, ((j : ℕ) + l < (u : ℕ)) ∧
          (p / (1 - p)) ^ r / (l : ℝ) ≤ configPosterior x.1 u) ≤
        ENNReal.ofReal δ := by
  have hq1 : 1 < p / (1 - p) := by
    rw [one_lt_div (by linarith : (0 : ℝ) < 1 - p)]
    linarith
  have hq0 : 0 < p / (1 - p) := lt_trans zero_lt_one hq1
  have hWnn : 0 ≤ ∑ pr ∈ windowCrossPairs j l, cutUnionWeight a₀ pr :=
    Finset.sum_nonneg fun pr _ => div_nonneg (hpos pr.1).le (hpos pr.2).le
  refine ⟨deviationExponent p ((∑ pr ∈ windowCrossPairs j l, cutUnionWeight a₀ pr) / δ),
    lt_of_lt_of_le zero_lt_one (le_max_left 1 _), fun fuel => ?_⟩
  have hkey := learner_far_heavy_window_bound hn j p
    ((p / (1 - p)) ^ deviationExponent p
        ((∑ pr ∈ windowCrossPairs j l, cutUnionWeight a₀ pr) / δ) / (l : ℝ))
    hp hp1 (div_pos (pow_pos hq0 _) (Nat.cast_pos.mpr hl)) l hl a₀ hpos hsum fuel
  rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hl))] at hkey
  refine le_trans hkey (ENNReal.ofReal_le_ofReal ?_)
  refine cutUnionBound_le _ _ _ _ (pow_pos hq0 _) ?_
  rcases eq_or_lt_of_le hWnn with hW | hW
  · rw [← hW]
    exact mul_nonneg hδ.le (pow_nonneg hq0.le _)
  · have hqge := pow_deviationExponent_ge hp hp1 (div_pos hW hδ)
    calc ∑ pr ∈ windowCrossPairs j l, cutUnionWeight a₀ pr
        = (∑ pr ∈ windowCrossPairs j l, cutUnionWeight a₀ pr) / δ * δ :=
          (div_mul_cancel₀ _ hδ.ne').symm
      _ ≤ (p / (1 - p)) ^ deviationExponent p
            ((∑ pr ∈ windowCrossPairs j l, cutUnionWeight a₀ pr) / δ) * δ :=
            mul_le_mul_of_nonneg_right hqge hδ.le
      _ = δ * (p / (1 - p)) ^ deviationExponent p
            ((∑ pr ∈ windowCrossPairs j l, cutUnionWeight a₀ pr) / δ) :=
            mul_comm _ _

/-- Under the stated noise and prior hypotheses, packages the truth driven learner's pairwise
and finite union ratio bounds, far heavy cell and halting bounds, single cell bounds, and
calibration to any positive error target. -/
theorem frontier2 {n : ℕ} (hn : 0 < n) (j : Fin n) (p ε : ℝ)
    (hp : 1 / 2 < p) (hp1 : p < 1) (hε : 0 < ε) (l : ℕ) (hl : 0 < l)
    (S : Finset (Fin n × Fin n)) (hside : ∀ pr ∈ S, crossSide j pr.1 pr.2)
    (a₀ : Fin n → ℝ) (hpos : ∀ m, 0 < a₀ m) (hsum : (∑ m, a₀ m) ≤ 1) :
    (∀ pr ∈ S, ∀ R : ℝ, 0 < R → ∀ fuel : ℕ,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (trueLearnerNext hn j p ε) fuel (Sum.inr a₀))
          (fun x => R * configPosterior x.1 pr.2 ≤ configPosterior x.1 pr.1) ≤
        ENNReal.ofReal (cutUnionWeight a₀ pr / R)) ∧
    (∀ R : ℝ, 0 < R → ∀ fuel : ℕ,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (trueLearnerNext hn j p ε) fuel (Sum.inr a₀))
          (fun x => ∃ pr' ∈ S, R * configPosterior x.1 pr'.2 ≤ configPosterior x.1 pr'.1) ≤
        ENNReal.ofReal (cutUnionBound S a₀ R)) ∧
    (∀ fuel : ℕ,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (trueLearnerNext hn j p ε) fuel (Sum.inr a₀))
          (fun x => ∃ u : Fin n, ((j : ℕ) + l < (u : ℕ)) ∧ ε ≤ configPosterior x.1 u) ≤
        ENNReal.ofReal (cutUnionBound (windowCrossPairs j l) a₀ (ε * (l : ℝ)))) ∧
    (∀ fuel : ℕ,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (trueLearnerNext hn j p ε) fuel (Sum.inr a₀))
          (fun x => (∃ o : Fin n → ℝ, x.1 = Sum.inl o) ∧
            ∃ u : Fin n, ((j : ℕ) + l < (u : ℕ)) ∧ ε ≤ configPosterior x.1 u) ≤
        ENNReal.ofReal (cutUnionBound (windowCrossPairs j l) a₀ (ε * (l : ℝ)))) ∧
    (∀ fuel : ℕ,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (trueLearnerNext hn j p ε) fuel (Sum.inr a₀))
          (fun x => (∃ i : Fin n, ε ≤ configPosterior x.1 i) ∧
            (j : ℕ) + l < ((haltCut hn (configPosterior x.1) ε : ℕ))) ≤
        ENNReal.ofReal (cutUnionBound (windowCrossPairs j l) a₀ (ε * (l : ℝ)))) ∧
    (∀ u : Fin n, (j : ℕ) + l < (u : ℕ) → ∀ fuel : ℕ,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (trueLearnerNext hn j p ε) fuel (Sum.inr a₀))
          (fun x => ε ≤ configPosterior x.1 u) ≤
        ENNReal.ofReal (cutUnionBound (singleWindowPairs u l) a₀ (ε * (l : ℝ)))) ∧
    (∀ δ : ℝ, 0 < δ → ∃ r : ℕ, 0 < r ∧ ∀ fuel : ℕ,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
          (runFor (trueLearnerNext hn j p ((p / (1 - p)) ^ r / (l : ℝ))) fuel
            (Sum.inr a₀))
          (fun x => ∃ u : Fin n, ((j : ℕ) + l < (u : ℕ)) ∧
            (p / (1 - p)) ^ r / (l : ℝ) ≤ configPosterior x.1 u) ≤
          ENNReal.ofReal δ) := by
  refine ⟨fun pr hpr R hR fuel =>
    learner_pair_crossing hn j pr.1 pr.2 p ε R (hside pr hpr) hp hp1 hR a₀ hpos hsum fuel,
    fun R hR fuel =>
      learner_cut_union_event_bound hn j p ε R S hside hp hp1 hR a₀ hpos hsum fuel,
    fun fuel => learner_far_heavy_window_bound hn j p ε hp hp1 hε l hl a₀ hpos hsum fuel,
    fun fuel => learner_eps_halt_far_bound hn j p ε hp hp1 hε l hl a₀ hpos hsum fuel,
    fun fuel => learner_haltCut_far_bound hn j p ε hp hp1 hε l hl a₀ hpos hsum fuel,
    fun u hjul fuel =>
      learner_far_heavy_single_bound hn j u l hl hjul p ε hp hp1 hε a₀ hpos hsum fuel,
    fun δ hδ => learner_far_heavy_calibration hn j p δ hp hp1 hδ l hl a₀ hpos hsum⟩

/-- Under the stated noise and prior hypotheses, packages pairwise and finite union ratio bounds
for the union absorbing kernel together with full pair calibration to any positive error
target. -/
theorem frontier1 {n : ℕ} (hn : 0 < n) (j : Fin n) (p ε : ℝ)
    (hp : 1 / 2 < p) (hp1 : p < 1)
    (S : Finset (Fin n × Fin n)) (hside : ∀ pr ∈ S, crossSide j pr.1 pr.2)
    (a₀ : Fin n → ℝ) (hpos : ∀ m, 0 < a₀ m) (hsum : (∑ m, a₀ m) ≤ 1) :
    (∀ pr ∈ S, ∀ R : ℝ, 0 < R → ∀ fuel : ℕ,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (unionAbsorbNext hn j p ε R S) fuel (Sum.inr a₀))
          (fun x => R * configPosterior x.1 pr.2 ≤ configPosterior x.1 pr.1) ≤
        ENNReal.ofReal (cutUnionWeight a₀ pr / R)) ∧
    (∀ R : ℝ, 0 < R → ∀ fuel : ℕ,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor (unionAbsorbNext hn j p ε R S) fuel (Sum.inr a₀))
          (fun x => ∃ pr' ∈ S, R * configPosterior x.1 pr'.2 ≤ configPosterior x.1 pr'.1) ≤
        ENNReal.ofReal (cutUnionBound S a₀ R)) ∧
    (∀ δ : ℝ, 0 < δ → ∃ r : ℕ, 0 < r ∧ ∀ fuel : ℕ,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
          (runFor (unionAbsorbNext hn j p ε ((p / (1 - p)) ^ r) (fullCrossPairs j)) fuel
            (Sum.inr a₀))
          (fun x => ∃ pr ∈ fullCrossPairs j,
            (p / (1 - p)) ^ r * configPosterior x.1 pr.2 ≤ configPosterior x.1 pr.1) ≤
          ENNReal.ofReal δ) := by
  refine ⟨fun pr hpr R hR fuel =>
    union_pair_crossing hn j pr.1 pr.2 p ε R S hpr (hside pr hpr) hp hp1 hR a₀ hpos hsum fuel,
    fun R hR fuel =>
      cut_union_event_bound hn j p ε R S hside hp hp1 hR a₀ hpos hsum fuel,
    fun δ hδ => cut_union_calibration hn j p ε δ hp hp1 hδ a₀ hpos hsum⟩

end Qatlib.Concepts.OrderedBayes.BayesRatioCore.AdaptiveCutUnionBound
