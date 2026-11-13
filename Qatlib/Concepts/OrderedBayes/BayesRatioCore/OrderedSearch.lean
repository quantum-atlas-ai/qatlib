/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.OrderedSearchDefs
import Qatlib.Concepts.OrderedBayes.BayesRatioCore.ConsistencyChecks
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Bayesian Ordered Search and Query Bounds

This module proves consistency and probability bounds for Bayesian ordered search, using the
adaptive-learning setting of [BenOrHassidim2007]. It identifies iterated posterior transport
with normalized record likelihoods, establishes likelihood-ratio crossing bounds, and derives
concentration estimates from crossing-score martingales and light cells in neighboring windows.

It also develops entropy and Fano lower bounds for finite noisy query trees, Markov tail
estimates, rational readout identities, and recursive query accounting. The FGGS calculations
and oracle results include corrected rate constants, a unitary diluted oracle, and explicit
counterexamples to several printed formulas.

## Main statements

* `transportFold_eq_recordPosterior`: iterated Bayesian transport equals the record posterior.
* `cross_pair_joint_bound`: a pairwise ratio crossing functional is bounded by the reciprocal
  threshold.
* `clause13_deviation_endpoint`: light-cell witnesses and concentration bounds for deviations on
  either side of the truth.
* `fggs_corrected_rate`: the FGGS constants satisfy the corrected query-to-information rate
  bound.
* `fano_capacity_lower_bound`: the Fano capacity expression bounds uniform expected queries from
  below.
* `source_lemma_2_8`: a generalized Markov estimate refines the query tail bound.
* `dilutedOracle_unitary`: the diluted comparison oracle is unitary for noise parameters in the
  unit interval.
* `clause16_cost_endpoint`: answer probabilities, posterior normalization, and expected oracle
  costs agree with the query-tree semantics.

## References

* [Ben-Or and Hassidim, 2007][BenOrHassidim2007]
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Classical
open Qatlib
open Qatlib.Concepts.OrderedBayes.BayesRatioCore
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels.OrderedSearch2007
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma23Quan

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore.OrderedSearch

/-- Pointwise equal functions have equal sums over a finite type. -/
theorem sum_congr' {ι : Type*} {M : Type*} [AddCommMonoid M] [Fintype ι] {f g : ι → M}
    (h : ∀ x, f x = g x) : (∑ x, f x) = (∑ x, g x) :=
  Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun x _ => h x)

/-- The uniform posterior on a nonempty finite set has total mass one. -/
theorem uniform_sum {n : ℕ} (hn : 0 < n) : (∑ m : Fin n, uniformPosterior (n := n) m) = 1 := by
  simp [uniformPosterior, Finset.sum_const, Finset.card_univ]
  exact_mod_cast (mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)))

/-- The likelihood of a true answer is positive when `0 < p < 1`. -/
theorem bayesTrueLikelihood_pos {n : ℕ} (c m : Fin n) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    0 < bayesTrueLikelihood c m p := by
  by_cases h : (c : ℕ) ≤ (m : ℕ)
  · unfold bayesTrueLikelihood; rw [if_pos h]; linarith
  · unfold bayesTrueLikelihood; rw [if_neg h]; linarith

/-- Both Boolean answer likelihoods are positive when `0 < p < 1`. -/
theorem answerLikelihood_pos {n : ℕ} (m c : Fin n) (p : ℝ) (b : Bool) (hp : 0 < p)
    (hp1 : p < 1) : 0 < answerLikelihood m c p b := by
  by_cases hb : b
  · unfold answerLikelihood; rw [if_pos hb]
    exact bayesTrueLikelihood_pos c m p hp hp1
  · unfold answerLikelihood; rw [if_neg hb]
    by_cases h : (c : ℕ) ≤ (m : ℕ)
    · unfold bayesFalseLikelihood; rw [if_pos h]; linarith
    · unfold bayesFalseLikelihood; rw [if_neg h]; linarith

/-- The printed true-answer likelihood is positive when `0 < p < 1`. -/
theorem printedTrueLikelihood_pos {n : ℕ} (c m : Fin n) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    0 < printedTrueLikelihood c m p := by
  by_cases h : (m : ℕ) ≤ (c : ℕ)
  · unfold printedTrueLikelihood; rw [if_pos h]; linarith
  · unfold printedTrueLikelihood; rw [if_neg h]; linarith

/-- A nonnegative weighted sum of positive values is positive if at least one weight is
positive. -/
theorem sum_mul_pos_of_pos {n : ℕ} (a : Fin n → ℝ) (f : Fin n → ℝ)
    (ha : ∀ m, 0 ≤ a m) (hf : ∀ m, 0 < f m) (hw : ∃ m, 0 < a m) :
    0 < (∑ m, a m * f m) := by
  apply Finset.sum_pos'
  · intro m _; exact mul_nonneg (ha m) (le_of_lt (hf m))
  · obtain ⟨m, hm⟩ := hw
    exact ⟨m, Finset.mem_univ _, mul_pos hm (hf m)⟩

/-- The corrected posterior equals the prior times the answer likelihood, divided by the total
weighted likelihood. -/
theorem correctPost_eq {n : ℕ} (a : Fin n → ℝ) (c : Fin n) (p : ℝ) (b : Bool) (m : Fin n) :
    correctPost a c p b m =
      (a m * answerLikelihood m c p b) / (∑ m', a m' * answerLikelihood m' c p b) := by
  by_cases hb : b
  · simp only [correctPost, answerLikelihood, if_pos hb, bayesTruePost, bayesTrueNorm]
  · simp only [correctPost, answerLikelihood, if_neg hb, bayesFalsePost, bayesFalseNorm]

/-- Every transported weight is positive for a nonempty search space and `0 < p < 1`. -/
theorem transportWeights_pos {n : ℕ} (hn : 0 < n) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∀ (t : Record n) (m : Fin n), 0 < transportWeights t p m := by
  intro t
  induction t with
  | nil =>
    intro m
    simp only [transportWeights]
    exact div_pos (by norm_num) (by exact_mod_cast (Nat.cast_pos.mpr hn))
  | cons obs t ih =>
    intro m
    simp only [transportWeights]
    exact mul_pos (ih m) (answerLikelihood_pos m obs.1 p obs.2 hp hp1)

/-- The total transported weight is positive for a nonempty search space and `0 < p < 1`. -/
theorem transportWeights_sum_pos {n : ℕ} (hn : 0 < n) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (t : Record n) : 0 < (∑ m, transportWeights t p m) := by
  apply Finset.sum_pos'
  · intro m _; exact le_of_lt (transportWeights_pos hn p hp hp1 t m)
  · exact ⟨⟨0, hn⟩, Finset.mem_univ _,
      transportWeights_pos hn p hp hp1 t ⟨0, hn⟩⟩

/-- Summing transported weights against a positive function gives a positive value when `0 < p <
1`. -/
theorem transportWeights_mul_sum_pos {n : ℕ} (hn : 0 < n) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (t : Record n) (f : Fin n → ℝ) (hf : ∀ m, 0 < f m) :
    0 < (∑ m, transportWeights t p m * f m) := by
  apply Finset.sum_pos'
  · intro m _
    exact mul_nonneg (le_of_lt (transportWeights_pos hn p hp hp1 t m)) (le_of_lt (hf m))
  · exact ⟨⟨0, hn⟩, Finset.mem_univ _,
      mul_pos (transportWeights_pos hn p hp hp1 t ⟨0, hn⟩) (hf ⟨0, hn⟩)⟩

/-- Iterated Bayesian transport agrees pointwise with the normalized record posterior when `0 <
p < 1`. -/
theorem transportFold_eq_recordPosterior {n : ℕ} (hn : 0 < n) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∀ (t : Record n) (m : Fin n), transportFold t p m = recordPosterior t p m := by
  intro t
  induction t with
  | nil =>
    intro m
    simp only [transportFold, recordPosterior, transportWeights]
    rw [uniform_sum hn]
    field_simp
  | cons obs t ih =>
    intro m
    have hZ : (∑ m', transportWeights t p m') ≠ 0 :=
      ne_of_gt (transportWeights_sum_pos hn p hp hp1 t)
    have hih : ∀ m' : Fin n,
        transportFold t p m' = transportWeights t p m' / (∑ m', transportWeights t p m') :=
      fun m' => ih m'
    have hS : (∑ m', transportWeights t p m' * answerLikelihood m' obs.1 p obs.2) ≠ 0 :=
      ne_of_gt (transportWeights_mul_sum_pos hn p hp hp1 t
        (fun m' => answerLikelihood m' obs.1 p obs.2)
        (fun m' => answerLikelihood_pos m' obs.1 p obs.2 hp hp1))
    simp only [transportFold, recordPosterior, transportWeights]
    rw [correctPost_eq]
    simp_rw [hih]
    have hinner : (∑ m', (transportWeights t p m' / (∑ m', transportWeights t p m'))
          * answerLikelihood m' obs.1 p obs.2)
        = (∑ m', transportWeights t p m' * answerLikelihood m' obs.1 p obs.2)
          / (∑ m', transportWeights t p m') := by
      calc ∑ m', (transportWeights t p m' / (∑ m', transportWeights t p m'))
          * answerLikelihood m' obs.1 p obs.2
          = ∑ m', (transportWeights t p m' * answerLikelihood m' obs.1 p obs.2)
              / (∑ m', transportWeights t p m') := by
            exact sum_congr' (fun m' => by ring)
        _ = (∑ m', transportWeights t p m' * answerLikelihood m' obs.1 p obs.2)
              / (∑ m', transportWeights t p m') :=
          (Finset.sum_div (s := (Finset.univ : Finset (Fin n)))
            (f := fun m' => transportWeights t p m' * answerLikelihood m' obs.1 p obs.2)
            (∑ m', transportWeights t p m')).symm
    rw [hinner]
    field_simp

/-- The record posterior has total mass one for a nonempty search space and `0 < p < 1`. -/
theorem recordPosterior_sum {n : ℕ} (hn : 0 < n) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (t : Record n) : (∑ m, recordPosterior t p m) = 1 := by
  have hZ : (∑ m, transportWeights t p m) ≠ 0 :=
    ne_of_gt (transportWeights_sum_pos hn p hp hp1 t)
  have hmain : (∑ m, recordPosterior t p m)
      = (∑ m, transportWeights t p m) / (∑ m, transportWeights t p m) := by
    simp only [recordPosterior]
    exact (Finset.sum_div (s := (Finset.univ : Finset (Fin n)))
      (f := fun m => transportWeights t p m) (∑ m, transportWeights t p m)).symm
  rw [hmain]
  exact div_self hZ

/-- Every cell has positive record posterior when the search space is nonempty and `0 < p < 1`. -/
theorem recordPosterior_pos {n : ℕ} (hn : 0 < n) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (t : Record n) (m : Fin n) : 0 < recordPosterior t p m := by
  simp only [recordPosterior]
  exact div_pos (transportWeights_pos hn p hp hp1 t m) (transportWeights_sum_pos hn p hp hp1 t)

/-- The printed true-answer update equals the prior times `printedTrueLikelihood`, divided by
`normTrue`. -/
theorem printed_updateTrue_eq {n : ℕ} (a : Fin n → ℝ) (c : Fin n) (p : ℝ) (m : Fin n) :
    updateTrue a c p m = (a m * printedTrueLikelihood c m p) / normTrue a c p := by
  by_cases h1 : (m : ℕ) ≤ (c : ℕ)
  · simp only [updateTrue, printedTrueLikelihood, if_pos h1]
    ring
  · simp only [updateTrue, printedTrueLikelihood, if_neg h1]
    ring

/-- The printed and Bayesian true-answer likelihoods agree away from the queried cell. -/
theorem printedTrueLikelihood_eq_bayesTrueLikelihood {n : ℕ} {c m : Fin n} (p : ℝ)
    (hne : m ≠ c) : printedTrueLikelihood c m p = bayesTrueLikelihood c m p := by
  by_cases h1 : (m : ℕ) ≤ (c : ℕ)
  · have h2 : (m : ℕ) < (c : ℕ) := by omega
    have h3 : ¬((c : ℕ) ≤ (m : ℕ)) := by omega
    unfold printedTrueLikelihood bayesTrueLikelihood
    simp only [if_pos h1, if_neg h3]
  · have h2 : (c : ℕ) < (m : ℕ) := by omega
    unfold printedTrueLikelihood bayesTrueLikelihood
    simp only [if_neg h1, if_pos (Nat.le_of_lt h2)]

/-- At the queried cell, the printed and Bayesian true-answer likelihoods differ whenever `p ≠ 1
/ 2`. -/
theorem printedTrueLikelihood_ne_bayesTrueLikelihood_at_equal {n : ℕ} (c : Fin n) (p : ℝ)
    (hp : p ≠ 1 / 2) :
    printedTrueLikelihood c c p ≠ bayesTrueLikelihood c c p := by
  have h1 : printedTrueLikelihood c c p = 1 - p := by
    unfold printedTrueLikelihood; rw [if_pos le_rfl]
  have h2 : bayesTrueLikelihood c c p = p := by
    unfold bayesTrueLikelihood; rw [if_pos le_rfl]
  rw [h1, h2]
  intro h
  have hp' : p = 1 / 2 := by linarith
  exact hp hp'

/-- For a prior of total mass one, the weighted printed likelihood sums to `normTrue`. -/
theorem printedLikelihood_sum {n : ℕ} (a : Fin n → ℝ) (c : Fin n) (p : ℝ)
    (hsum : (∑ m, a m) = 1) :
    (∑ m, a m * printedTrueLikelihood c m p) = normTrue a c p := by
  have hsplit : ∀ m : Fin n,
      a m * printedTrueLikelihood c m p
        = (if (m : ℕ) ≤ (c : ℕ) then a m * (1 - p) else 0)
          + (if (c : ℕ) < (m : ℕ) then a m * p else 0) := by
    intro m
    by_cases h1 : (m : ℕ) ≤ (c : ℕ)
    · have h2 : ¬((c : ℕ) < (m : ℕ)) := by omega
      unfold printedTrueLikelihood
      simp only [if_pos h1, if_neg h2]
      ring
    · have h2 : (c : ℕ) < (m : ℕ) := by omega
      unfold printedTrueLikelihood
      simp only [if_neg h1, if_pos h2]
      ring
  have hpart : ∀ m : Fin n,
      (if (m : ℕ) ≤ (c : ℕ) then a m * (1 - p) else 0)
        = (1 - p) * (if (m : ℕ) ≤ (c : ℕ) then a m else 0) := by
    intro m
    by_cases h1 : (m : ℕ) ≤ (c : ℕ)
    · simp only [if_pos h1]; ring
    · simp only [if_neg h1]; ring
  have hpart2 : ∀ m : Fin n,
      (if (c : ℕ) < (m : ℕ) then a m * p else 0)
        = p * (if (c : ℕ) < (m : ℕ) then a m else 0) := by
    intro m
    by_cases h1 : (c : ℕ) < (m : ℕ)
    · simp only [if_pos h1]; ring
    · simp only [if_neg h1]; ring
  have hcov : ∀ m : Fin n,
      (if (m : ℕ) ≤ (c : ℕ) then a m else 0)
        + (if (c : ℕ) < (m : ℕ) then a m else 0) = a m := by
    intro m
    by_cases h1 : (m : ℕ) ≤ (c : ℕ)
    · have h2 : ¬((c : ℕ) < (m : ℕ)) := by omega
      simp only [if_pos h1, if_neg h2]; ring
    · have h2 : (c : ℕ) < (m : ℕ) := by omega
      simp only [if_neg h1, if_pos h2]; ring
  have hS1 : (∑ m : Fin n, (if (m : ℕ) ≤ (c : ℕ) then a m else 0)) = prefixMass a c := rfl
  have hS2 : (∑ m : Fin n, (if (c : ℕ) < (m : ℕ) then a m else 0))
      = (∑ m, a m) - prefixMass a c := by
    have e : (∑ m, a m) = ∑ m : Fin n, ((if (m : ℕ) ≤ (c : ℕ) then a m else 0)
        + (if (c : ℕ) < (m : ℕ) then a m else 0)) :=
      sum_congr' (fun m => (hcov m).symm)
    rw [e, Finset.sum_add_distrib, hS1]
    linarith
  have hsplit' : (∑ m, a m * printedTrueLikelihood c m p)
      = (∑ m : Fin n, (if (m : ℕ) ≤ (c : ℕ) then a m * (1 - p) else 0))
        + (∑ m : Fin n, (if (c : ℕ) < (m : ℕ) then a m * p else 0)) := by
    rw [sum_congr' (fun m => hsplit m), Finset.sum_add_distrib]
  rw [hsplit']
  rw [sum_congr' (fun m => hpart m)]
  rw [sum_congr' (fun m => hpart2 m)]
  rw [← Finset.mul_sum (Finset.univ : Finset (Fin n))
    (fun m => (if (m : ℕ) ≤ (c : ℕ) then a m else 0)) (1 - p)]
  rw [← Finset.mul_sum (Finset.univ : Finset (Fin n))
    (fun m => (if (c : ℕ) < (m : ℕ) then a m else 0)) p]
  rw [hS1, hS2, hsum]
  unfold normTrue normFalse
  ring

/-- For a normalized prior, the scaled difference between the Bayesian and printed normalizers
equals `1 - 2 * p` times the off-cell weighted Bayesian likelihood. -/
theorem printed_true_norm_difference {n : ℕ} (a : Fin n → ℝ) (c : Fin n) (p : ℝ)
    (hsum : (∑ m, a m) = 1) :
    (1 - p) * bayesTrueNorm a c p - p * normTrue a c p
      = (1 - 2 * p) * (∑ m, offCellMass a c m * bayesTrueLikelihood c m p) := by
  have hterm : ∀ m : Fin n,
      a m * ((1 - p) * bayesTrueLikelihood c m p - p * printedTrueLikelihood c m p)
        = (1 - 2 * p) * (offCellMass a c m * bayesTrueLikelihood c m p) := by
    intro m
    by_cases heq : m = c
    · rw [heq]
      have ho : offCellMass a c c = 0 := by simp [offCellMass]
      rw [ho]
      have h1 : bayesTrueLikelihood c c p = p := by
        unfold bayesTrueLikelihood; rw [if_pos le_rfl]
      have h2 : printedTrueLikelihood c c p = 1 - p := by
        unfold printedTrueLikelihood; rw [if_pos le_rfl]
      rw [h1, h2]
      ring
    · have h3 : printedTrueLikelihood c m p = bayesTrueLikelihood c m p :=
        printedTrueLikelihood_eq_bayesTrueLikelihood p heq
      rw [h3]
      have ho : offCellMass a c m = a m := by simp [offCellMass, heq]
      rw [ho]
      ring
  rw [show bayesTrueNorm a c p = ∑ m, a m * bayesTrueLikelihood c m p from rfl]
  rw [← printedLikelihood_sum a c p hsum]
  calc (1 - p) * (∑ m, a m * bayesTrueLikelihood c m p)
        - p * (∑ m, a m * printedTrueLikelihood c m p)
      = ∑ m, ((1 - p) * (a m * bayesTrueLikelihood c m p)
          - p * (a m * printedTrueLikelihood c m p)) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_sub_distrib]
    _ = ∑ m, a m * ((1 - p) * bayesTrueLikelihood c m p
        - p * printedTrueLikelihood c m p) := by
        exact sum_congr' (fun m => by ring)
    _ = ∑ m, (1 - 2 * p) * (offCellMass a c m * bayesTrueLikelihood c m p) :=
      sum_congr' (fun m => hterm m)
    _ = (1 - 2 * p) * (∑ m, offCellMass a c m * bayesTrueLikelihood c m p) := by
      rw [Finset.mul_sum]

/-- The off-cell weighted Bayesian likelihood is positive if a nonnegative prior assigns
positive mass away from the cut and `0 < p < 1`. -/
theorem offCell_likelihood_sum_pos {n : ℕ} (a : Fin n → ℝ) (c m' : Fin n) (p : ℝ)
    (ha0 : ∀ m, 0 ≤ a m) (ha : 0 < a m') (hne : m' ≠ c) (hp : 0 < p) (hp1 : p < 1) :
    0 < (∑ m, offCellMass a c m * bayesTrueLikelihood c m p) := by
  apply Finset.sum_pos'
  · intro m _
    by_cases heq : m = c
    · simp only [offCellMass, if_pos heq]
      exact mul_nonneg (by norm_num) (le_of_lt (bayesTrueLikelihood_pos c m p hp hp1))
    · simp only [offCellMass, if_neg heq]
      exact mul_nonneg (ha0 m) (le_of_lt (bayesTrueLikelihood_pos c m p hp hp1))
  · refine ⟨m', Finset.mem_univ _, ?_⟩
    simp only [offCellMass, if_neg hne]
    exact mul_pos ha (bayesTrueLikelihood_pos c m' p hp hp1)

/-- For `1 / 2 < p < 1`, a normalized nonnegative prior with positive mass both at and away from
the cut gives different printed and Bayesian updates at the cut. -/
theorem printed_updateTrue_ne_bayesTruePost_at_equal {n : ℕ} (a : Fin n → ℝ) (c : Fin n)
    (p : ℝ) (hsum : (∑ m, a m) = 1) (hac : 0 < a c) (ha0 : ∀ m, 0 ≤ a m)
    (hother : ∃ m', m' ≠ c ∧ 0 < a m') (hp : 1 / 2 < p) (hp1 : p < 1) :
    updateTrue a c p c ≠ bayesTruePost a c p c := by
  have hp0 : 0 < p := by linarith
  have hNpos : 0 < normTrue a c p := by
    rw [← printedLikelihood_sum a c p hsum]
    exact sum_mul_pos_of_pos a (printedTrueLikelihood c · p) ha0
      (fun m => printedTrueLikelihood_pos c m p hp0 hp1) ⟨c, hac⟩
  have hBpos : 0 < bayesTrueNorm a c p := by
    exact sum_mul_pos_of_pos a (bayesTrueLikelihood c · p) ha0
      (fun m => bayesTrueLikelihood_pos c m p hp0 hp1) ⟨c, hac⟩
  intro hcon
  have h1 : updateTrue a c p c = (a c * printedTrueLikelihood c c p) / normTrue a c p :=
    printed_updateTrue_eq a c p c
  have h2 : bayesTruePost a c p c = (a c * bayesTrueLikelihood c c p) / bayesTrueNorm a c p :=
    rfl
  rw [h1, h2] at hcon
  have h3 : printedTrueLikelihood c c p = 1 - p := by
    unfold printedTrueLikelihood; rw [if_pos le_rfl]
  have h4 : bayesTrueLikelihood c c p = p := by
    unfold bayesTrueLikelihood; rw [if_pos le_rfl]
  rw [h3, h4] at hcon
  field_simp [ne_of_gt hNpos, ne_of_gt hBpos] at hcon
  have hcross : (1 - p) * bayesTrueNorm a c p = p * normTrue a c p := hcon
  obtain ⟨m', hne, ham'⟩ := hother
  have hS : 0 < (∑ m, offCellMass a c m * bayesTrueLikelihood c m p) :=
    offCell_likelihood_sum_pos a c m' p ha0 ham' hne hp0 hp1
  have hdiff : (1 - p) * bayesTrueNorm a c p - p * normTrue a c p ≠ 0 := by
    rw [printed_true_norm_difference a c p hsum]
    exact mul_ne_zero (by linarith : (1 : ℝ) - 2 * p ≠ 0) (ne_of_gt hS)
  have hzero : (1 - p) * bayesTrueNorm a c p - p * normTrue a c p = 0 := by
    linarith [hcross]
  exact hdiff hzero

/-- If all prior weights away from `c` vanish, the weighted sum reduces to its term at `c`. -/
theorem sum_eq_single_cell {n : ℕ} (a : Fin n → ℝ) (c : Fin n) (f : Fin n → ℝ)
    (hother : ∀ m, m ≠ c → a m = 0) : (∑ m, a m * f m) = a c * f c := by
  have e : (∑ m, a m * f m) = ∑ m, (if m = c then a m * f m else 0) := by
    refine sum_congr' (fun m => ?_)
    by_cases heq : m = c
    · rw [if_pos heq]
    · rw [if_neg heq, hother m heq, zero_mul]
  rw [e]
  rw [Finset.sum_ite_eq']
  simp

/-- For a prior concentrated at the cut and `1 / 2 < p < 1`, the printed and Bayesian updates
agree at that cell. -/
theorem printed_updateTrue_eq_bayesTruePost_at_equal_degenerate {n : ℕ} (a : Fin n → ℝ)
    (c : Fin n) (p : ℝ) (hsum : (∑ m, a m) = 1) (hac : a c = 1)
    (hother : ∀ m, m ≠ c → a m = 0) (hp : 1 / 2 < p) (hp1 : p < 1) :
    updateTrue a c p c = bayesTruePost a c p c := by
  have hN : normTrue a c p = 1 - p := by
    rw [← printedLikelihood_sum a c p hsum]
    have h1 : (∑ m, a m * printedTrueLikelihood c m p)
        = a c * printedTrueLikelihood c c p :=
      sum_eq_single_cell a c (printedTrueLikelihood c · p) hother
    rw [h1]
    have h2 : printedTrueLikelihood c c p = 1 - p := by
      unfold printedTrueLikelihood; rw [if_pos le_rfl]
    rw [h2, hac]
    norm_num
  have hB : bayesTrueNorm a c p = p := by
    rw [show bayesTrueNorm a c p = ∑ m, a m * bayesTrueLikelihood c m p from rfl]
    have h1 : (∑ m, a m * bayesTrueLikelihood c m p)
        = a c * bayesTrueLikelihood c c p :=
      sum_eq_single_cell a c (bayesTrueLikelihood c · p) hother
    rw [h1]
    have h2 : bayesTrueLikelihood c c p = p := by
      unfold bayesTrueLikelihood; rw [if_pos le_rfl]
    rw [h2, hac]
    norm_num
  have h1 : updateTrue a c p c = (a c * printedTrueLikelihood c c p) / normTrue a c p :=
    printed_updateTrue_eq a c p c
  have h2 : bayesTruePost a c p c = (a c * bayesTrueLikelihood c c p) / bayesTrueNorm a c p :=
    rfl
  have h3 : printedTrueLikelihood c c p = 1 - p := by
    unfold printedTrueLikelihood; rw [if_pos le_rfl]
  have h4 : bayesTrueLikelihood c c p = p := by
    unfold bayesTrueLikelihood; rw [if_pos le_rfl]
  rw [h1, h2, h3, h4, hN, hB, hac]
  have hp0 : p ≠ 0 := by linarith
  have h1p : (1 : ℝ) - p ≠ 0 := by linarith
  simp only [one_mul]
  rw [div_self h1p, div_self hp0]

/-- For three uniform cells, cut `1`, and `p = 3 / 4`, the Bayesian and printed normalizers are
`7 / 12` and `5 / 12`, with cut posteriors `3 / 7` and `1 / 5`. -/
theorem equalCutWitness :
    bayesTrueNorm (uniformPosterior (n := 3)) 1 (3 / 4) = 7 / 12 ∧
    normTrue (uniformPosterior (n := 3)) 1 (3 / 4) = 5 / 12 ∧
    bayesTruePost (uniformPosterior (n := 3)) 1 (3 / 4) 1 = 3 / 7 ∧
    updateTrue (uniformPosterior (n := 3)) 1 (3 / 4) 1 = 1 / 5 := by
  norm_num [bayesTrueNorm, bayesTrueLikelihood, bayesTruePost, normTrue, normFalse,
    prefixMass, uniformPosterior, updateTrue, Fin.sum_univ_succ, Fin.sum_univ_two]

/-- Comparing source ranks is equivalent to the source-side predicate. -/
theorem sourceRank_side_iff {n : ℕ} (c j : Fin n) :
    (sourceRank c ≤ sourceRank j) ↔ (sourceSide c j) := by
  show (c.val + 1 ≤ j.val + 1) ↔ (c.val ≤ j.val)
  exact Nat.succ_le_succ_iff

/-- The set of cells with source rank at most that of `j` equals the corresponding source-side
set. -/
theorem sourceRank_side_set {n : ℕ} (j : Fin n) :
    { m : Fin n | sourceRank m ≤ sourceRank j } = { m : Fin n | sourceSide m j } := by
  ext m
  simp only [Set.mem_setOf_eq]
  exact sourceRank_side_iff m j

/-- The source rank of the index associated with a valid one-based rank `r` is `r`. -/
theorem sourceRank_rankIndex {n : ℕ} (r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n) :
    sourceRank (rankIndex r hr hrn) = r := by
  show (r - 1) + 1 = r
  omega

/-- The natural-number value of `rankIndex` is monotone in its valid rank argument. -/
theorem rankIndex_mono {n : ℕ} (r₁ r₂ : ℕ) (h1 : 1 ≤ r₁) (h1' : r₁ ≤ n) (h2 : 1 ≤ r₂)
    (h2' : r₂ ≤ n) (h : r₁ ≤ r₂) :
    (rankIndex r₁ h1 h1' : ℕ) ≤ (rankIndex r₂ h2 h2' : ℕ) := by
  show r₁ - 1 ≤ r₂ - 1
  omega

/-- At an index specified by a valid rank, iterated Bayesian transport equals the record
posterior. -/
theorem transportFold_rank_eq {n : ℕ} (hn : 0 < n) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (t : Record n) (r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n) :
    transportFold t p (rankIndex r hr hrn) = recordPosterior t p (rankIndex r hr hrn) :=
  transportFold_eq_recordPosterior hn p hp hp1 t (rankIndex r hr hrn)

/-- In a search space of at least two cells, every cell has a distinct cell. -/
theorem exists_ne_cell {n : ℕ} (hn2 : 2 ≤ n) (c : Fin n) : ∃ m : Fin n, m ≠ c := by
  by_cases hz : c.val = 0
  · refine ⟨⟨1, by omega⟩, ?_⟩
    intro he
    have hval := congrArg Fin.val he
    simp at hval
    omega
  · refine ⟨⟨0, by omega⟩, ?_⟩
    intro he
    have hval := congrArg Fin.val he
    simp at hval
    exact hz hval.symm

/-- The likelihoods of the two Boolean answers sum to one. -/
theorem answerLikelihood_sum {n : ℕ} (m c : Fin n) (p : ℝ) :
    answerLikelihood m c p true + answerLikelihood m c p false = 1 := by
  have h1 : answerLikelihood m c p true = bayesTrueLikelihood c m p := rfl
  have h2 : answerLikelihood m c p false = bayesFalseLikelihood c m p := rfl
  rw [h1, h2]
  by_cases h : (c : ℕ) ≤ (m : ℕ)
  · simp [bayesTrueLikelihood, bayesFalseLikelihood, h]
  · simp [bayesTrueLikelihood, bayesFalseLikelihood, h]

/-- Every finite record has positive likelihood under each cell when `0 < p < 1`. -/
theorem recordLikelihood_pos {n : ℕ} (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∀ (t : Record n) (m : Fin n), 0 < recordLikelihood t m p := by
  intro t
  induction t with
  | nil =>
    intro m
    simp only [recordLikelihood, List.foldr_nil]
    norm_num
  | cons obs t ih =>
    intro m
    simp only [recordLikelihood, List.foldr_cons]
    exact mul_pos (answerLikelihood_pos m obs.1 p obs.2 hp hp1) (ih m)

/-- Folding multiplication by answer likelihoods over a record equals its likelihood times the
initial accumulator. -/
theorem foldr_recordLikelihood {n : ℕ} (m : Fin n) (p : ℝ) (t : Record n) (z : ℝ) :
    t.foldr (fun obs acc => answerLikelihood m obs.1 p obs.2 * acc) z
      = recordLikelihood t m p * z := by
  induction t with
  | nil =>
    simp only [List.foldr_nil, recordLikelihood, List.foldr_nil]
    ring
  | cons obs t ih =>
    simp only [List.foldr_cons]
    rw [ih]
    simp only [recordLikelihood, List.foldr_cons]
    ring

/-- The likelihood of concatenated records is the product of their likelihoods. -/
theorem recordLikelihood_append {n : ℕ} (m : Fin n) (p : ℝ) (t u : Record n) :
    recordLikelihood (t ++ u) m p = recordLikelihood t m p * recordLikelihood u m p := by
  induction t with
  | nil =>
    simp only [recordLikelihood, List.foldr_nil, List.nil_append]
    ring
  | cons obs t ih =>
    simp only [recordLikelihood, List.foldr_cons]
    rw [List.foldr_append, foldr_recordLikelihood]
    simp only [recordLikelihood, List.foldr_cons, List.foldr_nil]

/-- Extending a record multiplies its likelihood by the likelihood of the new answer at `cutAt`. -/
theorem recordLikelihood_extend {n : ℕ} (hn : 0 < n) (p ε : ℝ) (m : Fin n) (t : Record n)
    (b : Bool) :
    recordLikelihood (extend hn p ε t b) m p
      = recordLikelihood t m p * answerLikelihood m (cutAt hn p ε t) p b := by
  have h1 := recordLikelihood_append m p t [(cutAt hn p ε t, b)]
  unfold extend
  rw [h1]
  simp only [recordLikelihood, List.foldr_cons, List.foldr_nil]
  ring

/-- The record likelihood ratio is nonnegative when `0 < p < 1`. -/
theorem recordRatio_nonneg {n : ℕ} (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (t : Record n)
    (u v : Fin n) : 0 ≤ recordRatio t u v p := by
  unfold recordRatio
  have hu : 0 < recordLikelihood t u p := recordLikelihood_pos p hp hp1 t u
  have hv : 0 ≤ recordLikelihood t v p := le_of_lt (recordLikelihood_pos p hp hp1 t v)
  exact div_nonneg hv (le_of_lt hu)

/-- A record extension multiplies the likelihood ratio by the corresponding one-step answer
likelihood ratio. -/
theorem recordRatio_extend {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u v : Fin n) (t : Record n)
    (b : Bool) (hp : 0 < p) (hp1 : p < 1) :
    recordRatio (extend hn p ε t b) u v p
      = recordRatio t u v p
        * (answerLikelihood v (cutAt hn p ε t) p b / answerLikelihood u (cutAt hn p ε t) p b) := by
  unfold recordRatio
  rw [recordLikelihood_extend hn p ε v t b, recordLikelihood_extend hn p ε u t b]
  have hu : 0 < recordLikelihood t u p := recordLikelihood_pos p hp hp1 t u
  have hv : 0 < recordLikelihood t v p := recordLikelihood_pos p hp hp1 t v
  have hub : 0 < answerLikelihood u (cutAt hn p ε t) p b :=
    answerLikelihood_pos u (cutAt hn p ε t) p b hp hp1
  have hvb : 0 < answerLikelihood v (cutAt hn p ε t) p b :=
    answerLikelihood_pos v (cutAt hn p ε t) p b hp hp1
  field_simp

/-- The one-step likelihood ratio has mean one under the denominator cell's answer likelihoods
when `0 < p < 1`. -/
theorem oneStep_ratio_mean {n : ℕ} (u v c : Fin n) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (∑ b : Bool, answerLikelihood u c p b
        * (answerLikelihood v c p b / answerLikelihood u c p b)) = 1 := by
  have h1 : answerLikelihood u c p true ≠ 0 :=
    ne_of_gt (answerLikelihood_pos u c p true hp hp1)
  have h2 : answerLikelihood u c p false ≠ 0 :=
    ne_of_gt (answerLikelihood_pos u c p false hp hp1)
  have h3 : answerLikelihood u c p true
      * (answerLikelihood v c p true / answerLikelihood u c p true)
      = answerLikelihood v c p true := by field_simp
  have h4 : answerLikelihood u c p false
      * (answerLikelihood v c p false / answerLikelihood u c p false)
      = answerLikelihood v c p false := by field_simp
  simp only [Fintype.sum_bool]
  rw [h3, h4]
  exact answerLikelihood_sum v c p

/-- Averaging the likelihood ratio after one adaptive extension under cell `u` recovers its
current value. -/
theorem ratio_drift {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u v : Fin n) (t : Record n)
    (hp : 0 < p) (hp1 : p < 1) :
    (∑ b : Bool, answerLikelihood u (cutAt hn p ε t) p b
        * recordRatio (extend hn p ε t b) u v p)
      = recordRatio t u v p := by
  have hsum : (∑ b : Bool, answerLikelihood u (cutAt hn p ε t) p b
      * (answerLikelihood v (cutAt hn p ε t) p b / answerLikelihood u (cutAt hn p ε t) p b)) = 1 :=
    oneStep_ratio_mean u v (cutAt hn p ε t) p hp hp1
  have hterm : ∀ b : Bool,
      answerLikelihood u (cutAt hn p ε t) p b * recordRatio (extend hn p ε t b) u v p
        = recordRatio t u v p
          * (answerLikelihood u (cutAt hn p ε t) p b
            * (answerLikelihood v (cutAt hn p ε t) p b / answerLikelihood u (cutAt hn p ε t) p b)) := by
    intro b
    rw [recordRatio_extend hn p ε u v t b hp hp1]
    ring
  calc (∑ b : Bool, answerLikelihood u (cutAt hn p ε t) p b
        * recordRatio (extend hn p ε t b) u v p)
      = ∑ b : Bool, recordRatio t u v p
        * (answerLikelihood u (cutAt hn p ε t) p b
          * (answerLikelihood v (cutAt hn p ε t) p b / answerLikelihood u (cutAt hn p ε t) p b)) := by
        exact Finset.sum_congr rfl (fun b _ => hterm b)
    _ = recordRatio t u v p
        * (∑ b : Bool, answerLikelihood u (cutAt hn p ε t) p b
          * (answerLikelihood v (cutAt hn p ε t) p b / answerLikelihood u (cutAt hn p ε t) p b)) := by
        rw [Finset.mul_sum]
    _ = recordRatio t u v p * 1 := by rw [hsum]
    _ = recordRatio t u v p := by ring

/-- The tree-weight functional sends the constant function one to one. -/
theorem treeWeight_one {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u : Fin n) :
    ∀ (m : ℕ) (t : Record n), treeWeight hn p ε u (fun _ => 1) m t = 1 := by
  intro m
  induction m with
  | zero =>
    intro t
    simp only [treeWeight]
  | succ m ih =>
    intro t
    simp only [treeWeight]
    rw [Fintype.sum_bool]
    simp only [ih, stepWeight, mul_one]
    exact answerLikelihood_sum u (cutAt hn p ε t) p

/-- Under cell `u`, the tree-weighted likelihood ratio of `v` to `u` equals its value at the
initial record. -/
theorem treeWeight_ratio {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u v : Fin n) (hp : 0 < p)
    (hp1 : p < 1) :
    ∀ (m : ℕ) (t : Record n),
      treeWeight hn p ε u (fun s => recordRatio s u v p) m t = recordRatio t u v p := by
  intro m
  induction m with
  | zero =>
    intro t
    simp only [treeWeight]
  | succ m ih =>
    intro t
    simp only [treeWeight]
    simp only [ih]
    exact (by simpa [stepWeight] using! ratio_drift hn p ε u v t hp hp1)

/-- The tree difference equals the tree-weighted record ratio minus `R` times the crossing
functional. -/
theorem treeDiff_eq {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u v : Fin n) (R : ℝ) :
    ∀ (m : ℕ) (t : Record n),
      treeDiff hn p ε u v R m t
        = treeWeight hn p ε u (fun s => recordRatio s u v p) m t
          - R * treeCross hn p ε u v R m t := by
  intro m
  induction m with
  | zero =>
    intro t
    simp only [treeDiff, treeWeight, treeCross]
  | succ m ih =>
    intro t
    simp only [treeDiff, treeWeight, treeCross]
    simp only [Fintype.sum_bool, ih]
    ring

/-- The tree difference is nonnegative when `0 < p < 1`. -/
theorem treeDiff_nonneg {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u v : Fin n) (R : ℝ)
    (hp : 0 < p) (hp1 : p < 1) : ∀ (m : ℕ) (t : Record n), 0 ≤ treeDiff hn p ε u v R m t := by
  intro m
  induction m with
  | zero =>
    intro t
    simp only [treeDiff]
    by_cases h : R ≤ recordRatio t u v p
    · rw [if_pos h]; linarith
    · rw [if_neg h]
      have := recordRatio_nonneg p hp hp1 t u v
      linarith
  | succ m ih =>
    intro t
    simp only [treeDiff]
    apply Finset.sum_nonneg
    intro b _
    have hb : 0 ≤ stepWeight hn p ε u t b := by
      unfold stepWeight
      have := answerLikelihood_pos u (cutAt hn p ε t) p b hp hp1
      linarith
    exact mul_nonneg hb (ih (extend hn p ε t b))

/-- From the empty record, the pairwise tree crossing functional at a positive threshold `R` is
at most `1 / R`. -/
theorem cross_pair_joint_bound {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u v : Fin n) (R : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hR : 0 < R) :
    ∀ (m : ℕ), treeCross hn p ε u v R m [] ≤ 1 / R := by
  intro m
  have hdiff := treeDiff_nonneg hn p ε u v R hp hp1 m []
  have htw := treeWeight_ratio hn p ε u v hp hp1 m []
  have hde := treeDiff_eq hn p ε u v R m []
  rw [hde, htw] at hdiff
  have hzero : recordRatio [] u v p = 1 := by
    simp [recordRatio, recordLikelihood]
  have hle : R * treeCross hn p ε u v R m [] ≤ 1 := by linarith
  have hR0 : R ≠ 0 := ne_of_gt hR
  have hle' : treeCross hn p ε u v R m [] * R ≤ 1 := by
    have hc : treeCross hn p ε u v R m [] * R = R * treeCross hn p ε u v R m [] := mul_comm _ _
    rw [hc]
    exact hle
  exact (le_div_iff₀ hR).mpr hle'

/-- Setting the pairwise crossing threshold to `1 / δ` bounds the tree crossing functional by
`δ` for positive `δ`. -/
theorem r_delta_calibration {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u v : Fin n) (δ : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hδ : 0 < δ) :
    ∀ (m : ℕ), treeCross hn p ε u v (1 / δ) m [] ≤ δ := by
  intro m
  have h1 := cross_pair_joint_bound hn p ε u v (1 / δ) hp hp1 (by positivity) m
  have h2 : (1 / (1 / δ) : ℝ) = δ := by field_simp
  rw [h2] at h1
  exact h1

/-- If `u ≤ k < i`, the likelihood ratio of `i` to `k` has one-step mean one under cell `u`. -/
theorem three_cell_one_step_ratio_mean {n : ℕ} (u k i c : Fin n) (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (huk : (u : ℕ) ≤ (k : ℕ)) (hki : (k : ℕ) < (i : ℕ)) :
    (∑ b : Bool, answerLikelihood u c p b
        * (answerLikelihood i c p b / answerLikelihood k c p b)) = 1 := by
  have h1 : answerLikelihood u c p true ≠ 0 :=
    ne_of_gt (answerLikelihood_pos u c p true hp hp1)
  have h2 : answerLikelihood u c p false ≠ 0 :=
    ne_of_gt (answerLikelihood_pos u c p false hp hp1)
  have h3 : answerLikelihood i c p true ≠ 0 :=
    ne_of_gt (answerLikelihood_pos i c p true hp hp1)
  have h4 : answerLikelihood i c p false ≠ 0 :=
    ne_of_gt (answerLikelihood_pos i c p false hp hp1)
  have h5 : answerLikelihood k c p true ≠ 0 :=
    ne_of_gt (answerLikelihood_pos k c p true hp hp1)
  have h6 : answerLikelihood k c p false ≠ 0 :=
    ne_of_gt (answerLikelihood_pos k c p false hp hp1)
  have h7 : answerLikelihood u c p true = (if (c : ℕ) ≤ (u : ℕ) then p else 1 - p) := by
    simp [answerLikelihood, bayesTrueLikelihood]
  have h8 : answerLikelihood u c p false = (if (c : ℕ) ≤ (u : ℕ) then 1 - p else p) := by
    simp [answerLikelihood, bayesFalseLikelihood]
  have h9 : answerLikelihood i c p true = (if (c : ℕ) ≤ (i : ℕ) then p else 1 - p) := by
    simp [answerLikelihood, bayesTrueLikelihood]
  have h10 : answerLikelihood i c p false = (if (c : ℕ) ≤ (i : ℕ) then 1 - p else p) := by
    simp [answerLikelihood, bayesFalseLikelihood]
  have h11 : answerLikelihood k c p true = (if (c : ℕ) ≤ (k : ℕ) then p else 1 - p) := by
    simp [answerLikelihood, bayesTrueLikelihood]
  have h12 : answerLikelihood k c p false = (if (c : ℕ) ≤ (k : ℕ) then 1 - p else p) := by
    simp [answerLikelihood, bayesFalseLikelihood]
  simp only [Fintype.sum_bool]
  have hp0 : (0 : ℝ) < p := hp
  have hp1' : (0 : ℝ) < 1 - p := by linarith
  by_cases hck : (c : ℕ) ≤ (k : ℕ)
  · have hci : (c : ℕ) ≤ (i : ℕ) := by omega
    rw [h9, h10, h11, h12, if_pos hck, if_pos hck, if_pos hci, if_pos hci]
    field_simp
    exact answerLikelihood_sum u c p
  · by_cases hci : (c : ℕ) ≤ (i : ℕ)
    · have hcu : ¬ ((c : ℕ) ≤ (u : ℕ)) := by omega
      rw [h7, h8, h9, h10, h11, h12, if_neg hck, if_neg hck, if_pos hci, if_pos hci,
        if_neg hcu, if_neg hcu]
      field_simp
      ring
    · have hcu : ¬ ((c : ℕ) ≤ (u : ℕ)) := by omega
      rw [h9, h10, h11, h12, if_neg hck, if_neg hck, if_neg hci, if_neg hci]
      field_simp
      exact answerLikelihood_sum u c p

/-- If `u ≤ k < i`, the tree-weighted likelihood ratio of `i` to `k` under cell `u` equals its
initial value. -/
theorem treeWeight_ratio_three {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u k i : Fin n)
    (hp : 0 < p) (hp1 : p < 1) (huk : (u : ℕ) ≤ (k : ℕ)) (hki : (k : ℕ) < (i : ℕ)) :
    ∀ (m : ℕ) (t : Record n),
      treeWeight hn p ε u (fun s => recordRatio s k i p) m t = recordRatio t k i p := by
  intro m
  induction m with
  | zero =>
    intro t
    simp only [treeWeight]
  | succ m ih =>
    intro t
    simp only [treeWeight]
    simp only [ih]
    simp only [stepWeight]
    have hstep : ∀ b : Bool,
        answerLikelihood u (cutAt hn p ε t) p b * recordRatio (extend hn p ε t b) k i p
          = recordRatio t k i p
            * (answerLikelihood u (cutAt hn p ε t) p b
              * (answerLikelihood i (cutAt hn p ε t) p b
                / answerLikelihood k (cutAt hn p ε t) p b)) := by
      intro b
      rw [recordRatio_extend hn p ε k i t b hp hp1]
      ring
    calc (∑ b : Bool, answerLikelihood u (cutAt hn p ε t) p b
        * recordRatio (extend hn p ε t b) k i p)
        = ∑ b : Bool, recordRatio t k i p
            * (answerLikelihood u (cutAt hn p ε t) p b
              * (answerLikelihood i (cutAt hn p ε t) p b
                / answerLikelihood k (cutAt hn p ε t) p b)) := by
            exact Finset.sum_congr rfl (fun b _ => hstep b)
      _ = recordRatio t k i p
          * (∑ b : Bool, answerLikelihood u (cutAt hn p ε t) p b
              * (answerLikelihood i (cutAt hn p ε t) p b
                / answerLikelihood k (cutAt hn p ε t) p b)) := by
            rw [Finset.mul_sum]
      _ = recordRatio t k i p * 1 := by
            rw [three_cell_one_step_ratio_mean u k i (cutAt hn p ε t) p hp hp1 huk hki]
      _ = recordRatio t k i p := by ring

/-- The generalized tree difference is nonnegative when `0 < p < 1`. -/
theorem treeDiffOf_nonneg {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u v w : Fin n) (R : ℝ)
    (hp : 0 < p) (hp1 : p < 1) : ∀ (m : ℕ) (t : Record n), 0 ≤ treeDiffOf hn p ε u v w R m t := by
  intro m
  induction m with
  | zero =>
    intro t
    simp only [treeDiffOf]
    by_cases h : R ≤ recordRatio t v w p
    · rw [if_pos h]; linarith
    · rw [if_neg h]
      have := recordRatio_nonneg p hp hp1 t v w
      linarith
  | succ m ih =>
    intro t
    simp only [treeDiffOf]
    apply Finset.sum_nonneg
    intro b _
    have hb : 0 ≤ stepWeight hn p ε u t b := by
      unfold stepWeight
      have := answerLikelihood_pos u (cutAt hn p ε t) p b hp hp1
      linarith
    exact mul_nonneg hb (ih (extend hn p ε t b))

/-- The generalized tree difference equals the tree-weighted ratio minus the threshold times the
generalized crossing functional. -/
theorem treeDiffOf_eq {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u v w : Fin n) (R : ℝ) :
    ∀ (m : ℕ) (t : Record n),
      treeDiffOf hn p ε u v w R m t
        = treeWeight hn p ε u (fun s => recordRatio s v w p) m t
          - R * treeCrossOf hn p ε u v w R m t := by
  intro m
  induction m with
  | zero =>
    intro t
    simp only [treeDiffOf, treeWeight, treeCrossOf]
  | succ m ih =>
    intro t
    simp only [treeDiffOf, treeWeight, treeCrossOf]
    simp only [Fintype.sum_bool, ih]
    ring

/-- If `u ≤ k < i`, the generalized crossing functional from the empty record is at most `1 / R`
for positive `R`. -/
theorem three_cell_crossing_bound {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u k i : Fin n) (R : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (huk : (u : ℕ) ≤ (k : ℕ)) (hki : (k : ℕ) < (i : ℕ))
    (hR : 0 < R) :
    ∀ (m : ℕ), treeCrossOf hn p ε u k i R m [] ≤ 1 / R := by
  intro m
  have hdiff := treeDiffOf_nonneg hn p ε u k i R hp hp1 m []
  have htw := treeWeight_ratio_three hn p ε u k i hp hp1 huk hki m []
  have hde := treeDiffOf_eq hn p ε u k i R m []
  rw [hde, htw] at hdiff
  have hzero : recordRatio [] k i p = 1 := by
    simp [recordRatio, recordLikelihood]
  have hle : R * treeCrossOf hn p ε u k i R m [] ≤ 1 := by linarith
  have hR0 : R ≠ 0 := ne_of_gt hR
  exact (le_div_iff₀ hR).mpr (by rw [mul_comm]; exact hle)

/-- Each transported weight is the uniform prior weight times the record likelihood. -/
theorem transportWeights_eq {n : ℕ} (p : ℝ) : ∀ (t : Record n) (m : Fin n),
    transportWeights t p m = uniformPosterior m * recordLikelihood t m p := by
  intro t
  induction t with
  | nil =>
    intro m
    simp only [transportWeights]
    rw [recordLikelihood, List.foldr_nil]
    ring
  | cons obs t ih =>
    intro m
    have hrec : recordLikelihood (obs :: t) m p
        = answerLikelihood m obs.1 p obs.2 * recordLikelihood t m p := by
      show (obs :: t).foldr (fun obs acc => answerLikelihood m obs.1 p obs.2 * acc) 1
          = answerLikelihood m obs.1 p obs.2 * recordLikelihood t m p
      rw [List.foldr_cons]
      rfl
    simp only [transportWeights]
    rw [hrec, ih]
    ring

/-- The total transported weight is the sum of record likelihoods divided by the number of
cells. -/
theorem transportWeights_sum_eq {n : ℕ} (p : ℝ) (t : Record n) :
    (∑ m, transportWeights t p m) = (∑ m, recordLikelihood t m p) / n := by
  calc (∑ m, transportWeights t p m)
      = ∑ m, uniformPosterior m * recordLikelihood t m p := by
        exact Finset.sum_congr rfl (fun m _ => transportWeights_eq p t m)
    _ = (1 / n) * ∑ m, recordLikelihood t m p := by
        rw [Finset.mul_sum]
        congr 1
    _ = (∑ m, recordLikelihood t m p) / n := by ring

/-- For `0 < p < 1`, the record posterior is the record likelihood normalized by its sum over
cells. -/
theorem recordPosterior_eq_likelihood {n : ℕ} (hn : 0 < n) (p : ℝ) (hp : 0 < p)
    (hp1 : p < 1) (t : Record n) (m : Fin n) :
    recordPosterior t p m = recordLikelihood t m p / (∑ m', recordLikelihood t m' p) := by
  have hZ : (∑ m', transportWeights t p m') ≠ 0 :=
    ne_of_gt (transportWeights_sum_pos hn p hp hp1 t)
  have hsum := transportWeights_sum_eq p t
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hZ2 : (∑ m', recordLikelihood t m' p) ≠ 0 := by
    intro h0
    have hneg : (∑ m', transportWeights t p m') = 0 := by rw [hsum, h0, zero_div]
    exact hZ hneg
  have hu : uniformPosterior m = (1 / n : ℝ) := rfl
  simp only [recordPosterior]
  rw [transportWeights_eq p t m, hsum, hu]
  field_simp

/-- The ratio of posterior masses at `i` and `k` equals `recordRatio t k i p`. -/
theorem recordPosterior_ratio {n : ℕ} (hn : 0 < n) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (t : Record n) (i k : Fin n) :
    recordPosterior t p i / recordPosterior t p k = recordRatio t k i p := by
  have hZi : recordPosterior t p i ≠ 0 :=
    ne_of_gt (recordPosterior_pos hn p hp hp1 t i)
  have hZk : recordPosterior t p k ≠ 0 :=
    ne_of_gt (recordPosterior_pos hn p hp hp1 t k)
  have hLi := recordPosterior_eq_likelihood hn p hp hp1 t i
  have hLk := recordPosterior_eq_likelihood hn p hp hp1 t k
  have hZ : (∑ m', recordLikelihood t m' p) ≠ 0 := by
    intro h0
    have := recordPosterior_pos hn p hp hp1 t i
    rw [hLi, h0, div_zero] at this
    exact (ne_of_gt this) rfl
  unfold recordRatio
  rw [hLi, hLk]
  field_simp

/-- A normalized nonnegative mass function has a cell of mass at most `1 / l` in any valid
preceding window of length `l > 0`. -/
theorem window_light_cell {n : ℕ} (a : Fin n → ℝ) (i : Fin n) (l : ℕ)
    (hl : 0 < l) (hil : l ≤ (i : ℕ)) (ha0 : ∀ m, 0 ≤ a m) (hsum : (∑ m, a m) = 1) :
    ∃ k : Fin n, k ∈ windowCells i l ∧ a k ≤ 1 / (l : ℝ) := by
  obtain ⟨k, hk, hkle⟩ :=
    zoo_bayes_truth_window_light_cell a i l hl hil ha0 hsum
  refine ⟨k, ?_, hkle⟩
  simp only [windowCells, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hk

/-- A posterior mass at least `ε` at `i` and at most `1 / l` at `k` force their likelihood ratio
to be at least `ε * l`. -/
theorem halt_forces_light_ratio {n : ℕ} (hn : 0 < n) (p ε : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (t : Record n) (i k : Fin n) (l : ℕ) (hl : 0 < l) (hε : 0 < ε)
    (hhi : ε ≤ recordPosterior t p i) (hkl : recordPosterior t p k ≤ 1 / (l : ℝ)) :
    ε * (l : ℝ) ≤ recordRatio t k i p := by
  have hk0 : 0 < recordPosterior t p k := recordPosterior_pos hn p hp hp1 t k
  have hr := recordPosterior_ratio hn p hp hp1 t i k
  have hl0 : (l : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hl)
  have h2 : (l : ℝ) * recordPosterior t p k ≤ 1 := by
    have hx := mul_le_mul_of_nonneg_left hkl (le_of_lt (by positivity : (0 : ℝ) < (l : ℝ)))
    calc (l : ℝ) * recordPosterior t p k ≤ (l : ℝ) * (1 / (l : ℝ)) := hx
      _ = 1 := by field_simp
  have h1 : ε * (l : ℝ) * recordPosterior t p k ≤ ε := by
    have := mul_le_mul_of_nonneg_right h2 (le_of_lt hε)
    nlinarith
  have h3 : ε * (l : ℝ) * recordPosterior t p k ≤ recordPosterior t p i := by linarith
  rw [← hr]
  exact (le_div_iff₀ hk0).mpr h3

/-- The tree-count functional of the constantly false predicate is zero. -/
theorem treeCount_false {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u : Fin n) :
    ∀ (m : ℕ) (t : Record n), treeCount hn p ε u (fun _ => False) m t = 0 := by
  intro m
  induction m with
  | zero =>
    intro t
    simp [treeCount]
  | succ m ih =>
    intro t
    simp [treeCount, ih]

/-- Pointwise implication of record predicates gives an inequality between their tree-count
functionals when `0 < p < 1`. -/
theorem treeCount_mono {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u : Fin n) {φ ψ : Record n → Prop}
    (hφψ : ∀ t, φ t → ψ t) (hp : 0 < p) (hp1 : p < 1) :
    ∀ (m : ℕ) (t : Record n), treeCount hn p ε u φ m t ≤ treeCount hn p ε u ψ m t := by
  intro m
  induction m with
  | zero =>
    intro t
    simp only [treeCount]
    by_cases h : φ t
    · rw [if_pos h, if_pos (hφψ t h)]
    · rw [if_neg h]; by_cases hψ : ψ t <;> simp [hψ]
  | succ m ih =>
    intro t
    simp only [treeCount]
    apply Finset.sum_le_sum
    intro b _
    apply mul_le_mul_of_nonneg_left (ih (extend hn p ε t b))
    unfold stepWeight
    exact le_of_lt (answerLikelihood_pos u (cutAt hn p ε t) p b hp hp1)

/-- The tree count of a finite existential event is bounded by the corresponding finite-family
tree count. -/
theorem treeCount_exists_le_finset {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u : Fin n)
    (S : Finset (Fin n)) (φ : Fin n → Record n → Prop) (hp : 0 < p) (hp1 : p < 1) :
    ∀ (m : ℕ) (t : Record n),
      treeCount hn p ε u (fun s => ∃ k ∈ S, φ k s) m t
        ≤ treeCountFinset hn p ε u S φ m t := by
  intro m
  induction m with
  | zero =>
    intro t
    simp only [treeCount, treeCountFinset]
    by_cases h : ∃ k ∈ S, φ k t
    · rw [if_pos h]
      obtain ⟨k, hk, hφ⟩ := h
      have h1 : (1 : ℝ) ≤ ∑ j ∈ S, (if φ j t then 1 else 0) := by
        have hsingle := Finset.single_le_sum (s := S) (f := fun j => if φ j t then (1 : ℝ) else 0)
          (fun j _ => by by_cases h : φ j t <;> simp [h]) hk
        simpa [hφ] using! hsingle
      linarith
    · rw [if_neg h]
      exact Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num
  | succ m ih =>
    intro t
    simp only [treeCount, treeCountFinset]
    apply Finset.sum_le_sum
    intro b _
    apply mul_le_mul_of_nonneg_left (ih (extend hn p ε t b))
    unfold stepWeight
    exact le_of_lt (answerLikelihood_pos u (cutAt hn p ε t) p b hp hp1)

/-- The finite-family tree count is the sum of the individual tree counts. -/
theorem treeCountFinset_eq_sum {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u : Fin n)
    (S : Finset (Fin n)) (φ : Fin n → Record n → Prop) :
    ∀ (m : ℕ) (t : Record n),
      treeCountFinset hn p ε u S φ m t = ∑ k ∈ S, treeCount hn p ε u (φ k) m t := by
  intro m
  induction m with
  | zero =>
    intro t
    simp only [treeCountFinset, treeCount]
  | succ m ih =>
    intro t
    simp only [treeCountFinset, treeCount]
    calc (∑ b : Bool, stepWeight hn p ε u t b
            * treeCountFinset hn p ε u S φ m (extend hn p ε t b))
        = ∑ b : Bool, stepWeight hn p ε u t b
            * (∑ k ∈ S, treeCount hn p ε u (φ k) m (extend hn p ε t b)) := by
              exact Finset.sum_congr rfl (fun b _ =>
                congrArg (fun z => stepWeight hn p ε u t b * z) (ih (extend hn p ε t b)))
      _ = ∑ b : Bool, ∑ k ∈ S, stepWeight hn p ε u t b
            * treeCount hn p ε u (φ k) m (extend hn p ε t b) := by
              exact Finset.sum_congr rfl (fun b _ =>
                Finset.mul_sum (s := S)
                  (f := fun k => treeCount hn p ε u (φ k) m (extend hn p ε t b))
                  (stepWeight hn p ε u t b))
      _ = ∑ k ∈ S, ∑ b : Bool, stepWeight hn p ε u t b
            * treeCount hn p ε u (φ k) m (extend hn p ε t b) := by
              exact Finset.sum_comm (s := (Finset.univ : Finset Bool)) (t := S)
                (f := fun b k => stepWeight hn p ε u t b
                  * treeCount hn p ε u (φ k) m (extend hn p ε t b))
      _ = ∑ k ∈ S, treeCount hn p ε u (φ k) (m + 1) t := by
              simp only [treeCount]

/-- Counting records whose ratio is at least `R` equals the generalized tree crossing
functional. -/
theorem treeCount_eq_treeCrossOf {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u k i : Fin n) (R : ℝ) :
    ∀ (m : ℕ) (t : Record n),
      treeCount hn p ε u (fun s => R ≤ recordRatio s k i p) m t
        = treeCrossOf hn p ε u k i R m t := by
  intro m
  induction m with
  | zero => intro t; simp [treeCount, treeCrossOf]
  | succ m ih =>
    intro t
    simp only [treeCount, treeCrossOf]
    simp only [ih]

/-- If `u ≤ k < i`, the tree count of posterior mass at least `ε` at `i` together with ratio at
least `R > 0` is at most `1 / R`. -/
theorem containment_pair_bound {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u k i : Fin n) (R : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (huk : (u : ℕ) ≤ (k : ℕ)) (hki : (k : ℕ) < (i : ℕ))
    (hR : 0 < R) :
    ∀ (m : ℕ),
      treeCount hn p ε u (fun t => ε ≤ recordPosterior t p i ∧ R ≤ recordRatio t k i p) m []
        ≤ 1 / R := by
  intro m
  have h1 := treeCount_mono (φ := fun t => ε ≤ recordPosterior t p i ∧ R ≤ recordRatio t k i p)
    (ψ := fun s => R ≤ recordRatio s k i p) hn p ε u (fun t h => h.2) hp hp1 m []
  have h2 := treeCount_eq_treeCrossOf hn p ε u k i R m []
  have h3 := three_cell_crossing_bound hn p ε u k i R hp hp1 huk hki hR m
  linarith

/-- If `u ≤ k < i`, the tree count of a heavy cell `i` and a cell `k` of mass at most `1 / l` is
at most `1 / (ε * l)`. -/
theorem containment_light_bound {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u k i : Fin n) (l : ℕ)
    (hp : 0 < p) (hp1 : p < 1) (huk : (u : ℕ) ≤ (k : ℕ)) (hki : (k : ℕ) < (i : ℕ))
    (hl : 0 < l) (hε : 0 < ε) :
    ∀ (m : ℕ),
      treeCount hn p ε u
        (fun t => ε ≤ recordPosterior t p i ∧ recordPosterior t p k ≤ 1 / (l : ℝ)) m []
        ≤ 1 / (ε * (l : ℝ)) := by
  intro m
  have hR : 0 < ε * (l : ℝ) := by positivity
  have hmono : treeCount hn p ε u
        (fun t => ε ≤ recordPosterior t p i ∧ recordPosterior t p k ≤ 1 / (l : ℝ)) m []
      ≤ treeCount hn p ε u
        (fun t => ε ≤ recordPosterior t p i ∧ ε * (l : ℝ) ≤ recordRatio t k i p) m [] :=
    treeCount_mono hn p ε u
      (fun t ht => ⟨ht.1, halt_forces_light_ratio hn p ε hp hp1 t i k l hl hε ht.1 ht.2⟩)
      hp hp1 m []
  have h2 := containment_pair_bound hn p ε u k i (ε * (l : ℝ)) hp hp1 huk hki hR m
  linarith

/-- A preceding window contains at most `l` cells when `l ≤ i`. -/
theorem windowCells_card_le {n : ℕ} (i : Fin n) (l : ℕ) (hl : l ≤ (i : ℕ)) :
    (windowCells i l).card ≤ l := by
  let f : Fin n → ℕ := fun j => (j : ℕ) - ((i : ℕ) - l)
  have hmap : Set.MapsTo f (windowCells i l) (Finset.range l) := by
    intro j hj
    refine Finset.mem_range.mpr ?_
    have hj1 : (i : ℕ) - l ≤ (j : ℕ) := (Finset.mem_filter.mp hj).2.1
    have hj2 : (j : ℕ) < (i : ℕ) := (Finset.mem_filter.mp hj).2.2
    have hcancel : (i : ℕ) - l + l = (i : ℕ) := Nat.sub_add_cancel hl
    rw [Nat.sub_lt_iff_lt_add hj1]
    calc (j : ℕ) < (i : ℕ) := hj2
      _ = l + ((i : ℕ) - l) := by rw [Nat.add_comm, hcancel]
  have hinj : Set.InjOn f (windowCells i l) := by
    intro a ha b hb hab
    have ha1 : (i : ℕ) - l ≤ (a : ℕ) := (Finset.mem_filter.mp ha).2.1
    have hb1 : (i : ℕ) - l ≤ (b : ℕ) := (Finset.mem_filter.mp hb).2.1
    have hab' : (a : ℕ) - ((i : ℕ) - l) = (b : ℕ) - ((i : ℕ) - l) := hab
    have h1 : (a : ℕ) - ((i : ℕ) - l) + ((i : ℕ) - l) = (a : ℕ) := Nat.sub_add_cancel ha1
    have h2 : (b : ℕ) - ((i : ℕ) - l) + ((i : ℕ) - l) = (b : ℕ) := Nat.sub_add_cancel hb1
    apply Fin.ext
    calc (a : ℕ) = (a : ℕ) - ((i : ℕ) - l) + ((i : ℕ) - l) := h1.symm
      _ = (b : ℕ) - ((i : ℕ) - l) + ((i : ℕ) - l) := by rw [hab']
      _ = (b : ℕ) := h2
  have hle := Finset.card_le_card_of_injOn f hmap hinj
  rw [Finset.card_range] at hle
  exact hle

/-- When the truth lies before the preceding window of `i`, its heavy-cell and light-witness
event has tree count at most the window cardinality divided by `ε * l`. -/
theorem window_containment_bound {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u i : Fin n) (l : ℕ)
    (hp : 0 < p) (hp1 : p < 1) (hε : 0 < ε) (hl : 0 < l) (hil : l ≤ (i : ℕ))
    (hul : (u : ℕ) + l ≤ (i : ℕ)) :
    ∀ (m : ℕ),
      treeCount hn p ε u
        (fun t => ε ≤ recordPosterior t p i ∧
          ∃ k, k ∈ windowCells i l ∧ recordPosterior t p k ≤ 1 / (l : ℝ)) m []
        ≤ (windowCells i l).card / (ε * (l : ℝ)) := by
  intro m
  have hR : 0 < ε * (l : ℝ) := by positivity
  have hmono1 : treeCount hn p ε u
        (fun t => ε ≤ recordPosterior t p i ∧
          ∃ k, k ∈ windowCells i l ∧ recordPosterior t p k ≤ 1 / (l : ℝ)) m []
      ≤ treeCount hn p ε u
        (fun t => ∃ k ∈ windowCells i l,
          ε ≤ recordPosterior t p i ∧ ε * (l : ℝ) ≤ recordRatio t k i p) m [] :=
    treeCount_mono hn p ε u (fun t ht => by
      obtain ⟨k, hk, hlight⟩ := ht.2
      exact ⟨k, hk, ht.1, halt_forces_light_ratio hn p ε hp hp1 t i k l hl hε ht.1 hlight⟩)
      hp hp1 m []
  have hunion := treeCount_exists_le_finset hn p ε u (windowCells i l)
    (fun k t => ε ≤ recordPosterior t p i ∧ ε * (l : ℝ) ≤ recordRatio t k i p) hp hp1 m []
  have hsum := treeCountFinset_eq_sum hn p ε u (windowCells i l)
    (fun k t => ε ≤ recordPosterior t p i ∧ ε * (l : ℝ) ≤ recordRatio t k i p) m []
  have hper : ∀ k ∈ windowCells i l,
      treeCount hn p ε u
        (fun t => ε ≤ recordPosterior t p i ∧ ε * (l : ℝ) ≤ recordRatio t k i p) m []
        ≤ 1 / (ε * (l : ℝ)) := by
    intro k hk
    have hku : (u : ℕ) ≤ (k : ℕ) := by
      have hk1 := (Finset.mem_filter.mp hk).2.1
      omega
    have hki : (k : ℕ) < (i : ℕ) := (Finset.mem_filter.mp hk).2.2
    exact containment_pair_bound hn p ε u k i (ε * (l : ℝ)) hp hp1 hku hki hR m
  calc treeCount hn p ε u
        (fun t => ε ≤ recordPosterior t p i ∧
          ∃ k, k ∈ windowCells i l ∧ recordPosterior t p k ≤ 1 / (l : ℝ)) m []
      ≤ treeCount hn p ε u
        (fun t => ∃ k ∈ windowCells i l,
          ε ≤ recordPosterior t p i ∧ ε * (l : ℝ) ≤ recordRatio t k i p) m [] := hmono1
    _ ≤ treeCountFinset hn p ε u (windowCells i l)
        (fun k t => ε ≤ recordPosterior t p i ∧ ε * (l : ℝ) ≤ recordRatio t k i p) m [] := hunion
    _ = ∑ k ∈ windowCells i l, treeCount hn p ε u
        (fun t => ε ≤ recordPosterior t p i ∧ ε * (l : ℝ) ≤ recordRatio t k i p) m [] := hsum
    _ ≤ ∑ _k ∈ windowCells i l, (1 / (ε * (l : ℝ))) :=
        Finset.sum_le_sum fun k hk => hper k hk
    _ = (windowCells i l).card / (ε * (l : ℝ)) := by
        rw [Finset.sum_const]
        ring

/-- When the truth lies before a valid preceding window of `i`, its heavy-cell and light-witness
event has tree count at most `1 / ε`. -/
theorem window_containment_bound_le {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u i : Fin n) (l : ℕ)
    (hp : 0 < p) (hp1 : p < 1) (hε : 0 < ε) (hl : 0 < l) (hil : l ≤ (i : ℕ))
    (hul : (u : ℕ) + l ≤ (i : ℕ)) :
    ∀ (m : ℕ),
      treeCount hn p ε u
        (fun t => ε ≤ recordPosterior t p i ∧
          ∃ k, k ∈ windowCells i l ∧ recordPosterior t p k ≤ 1 / (l : ℝ)) m []
        ≤ 1 / ε := by
  intro m
  have h1 := window_containment_bound hn p ε u i l hp hp1 hε hl hil hul m
  have hcard : ((windowCells i l).card : ℝ) ≤ (l : ℝ) := by
    exact_mod_cast (windowCells_card_le i l hil)
  have h5 : (0 : ℝ) < ε * (l : ℝ) := by positivity
  have h4 : (windowCells i l).card / (ε * (l : ℝ)) ≤ 1 / ε := by
    rw [div_le_div_iff₀ h5 (by positivity : (0 : ℝ) < ε)]
    nlinarith
  linarith

/-- Collects adaptive record extension, likelihood normalization, ratio preservation, and
pairwise and three-cell crossing bounds for `1 / 2 < p < 1`. -/
theorem clause13_endpoint :
    ∀ (n : ℕ) (p ε : ℝ) (u v k : Fin n),
      (hn : 0 < n) → (hp : 1 / 2 < p) → (hp1 : p < 1) → (hε : 0 < ε) →
      (∀ (t : Record n) (b : Bool), extend hn p ε t b = t ++ [(cutAt hn p ε t, b)]) ∧
      (∀ (m : ℕ) (t : Record n), treeWeight hn p ε u (fun _ => 1) m t = 1) ∧
      (∀ (m : ℕ) (t : Record n), treeWeight hn p ε v (fun _ => 1) m t = 1) ∧
      (∀ (w : Fin n) (c : Fin n),
        answerLikelihood w c p true + answerLikelihood w c p false = 1) ∧
      (∀ (c : Fin n),
        (∑ b : Bool, answerLikelihood u c p b
          * (answerLikelihood v c p b / answerLikelihood u c p b)) = 1) ∧
      (∀ (m : ℕ) (t : Record n),
        treeWeight hn p ε u (fun s => recordRatio s u v p) m t = recordRatio t u v p) ∧
      (∀ (R : ℝ), 0 < R → ∀ (m : ℕ), treeCross hn p ε u v R m [] ≤ 1 / R) ∧
      (∀ (δ : ℝ), 0 < δ → ∀ (m : ℕ), treeCross hn p ε u v (1 / δ) m [] ≤ δ) ∧
      (∀ (c : Fin n), (u : ℕ) ≤ (k : ℕ) → (k : ℕ) < (v : ℕ) →
        (∑ b : Bool, answerLikelihood u c p b
          * (answerLikelihood v c p b / answerLikelihood k c p b)) = 1) ∧
      (∀ (m : ℕ) (t : Record n), (u : ℕ) ≤ (k : ℕ) → (k : ℕ) < (v : ℕ) →
        treeWeight hn p ε u (fun s => recordRatio s k v p) m t = recordRatio t k v p) ∧
      (∀ (R : ℝ), 0 < R → ∀ (m : ℕ), (u : ℕ) ≤ (k : ℕ) → (k : ℕ) < (v : ℕ) →
        treeCrossOf hn p ε u k v R m [] ≤ 1 / R) ∧
      (∀ (l : ℕ), 0 < l → ∀ (m : ℕ), (u : ℕ) ≤ (k : ℕ) → (k : ℕ) < (v : ℕ) →
        treeCount hn p ε u
          (fun t => ε ≤ recordPosterior t p v ∧ recordPosterior t p k ≤ 1 / (l : ℝ)) m []
          ≤ 1 / (ε * (l : ℝ))) := by
  intro n p ε u v k hn hp hp1 hε
  have hp0 : 0 < p := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t b; rfl
  · intro m t; exact treeWeight_one hn p ε u m t
  · intro m t; exact treeWeight_one hn p ε v m t
  · intro w c; exact answerLikelihood_sum w c p
  · intro c; exact oneStep_ratio_mean u v c p hp0 hp1
  · intro m t; exact treeWeight_ratio hn p ε u v hp0 hp1 m t
  · intro R hR m; exact cross_pair_joint_bound hn p ε u v R hp0 hp1 hR m
  · intro δ hδ m; exact r_delta_calibration hn p ε u v δ hp0 hp1 hδ m
  · intro c huk hkv; exact three_cell_one_step_ratio_mean u k v c p hp0 hp1 huk hkv
  · intro m t huk hkv; exact treeWeight_ratio_three hn p ε u k v hp0 hp1 huk hkv m t
  · intro R hR m huk hkv; exact three_cell_crossing_bound hn p ε u k v R hp0 hp1 huk hkv hR m
  · intro l hl m huk hkv;
      exact containment_light_bound hn p ε u k v l hp0 hp1 huk hkv hl hε m

/-- The cyclic predecessor on `Fin (2 * N)` subtracts one at positive indices and wraps zero to
`2 * N - 1`. -/
theorem fggs_pred_val {N : ℕ} (hN : 0 < N) (x : Fin (2 * N)) :
    (fggsPred hN x).val = if 0 < x.val then x.val - 1 else 2 * N - 1 := by
  by_cases h0 : 0 < x.val
  · rw [fggsPred, if_pos h0]
    rw [if_pos h0]
  · rw [fggsPred, if_neg h0]
    rw [if_neg h0]

/-- The cyclic successor on `Fin (2 * N)` adds one modulo `2 * N`. -/
theorem fggs_succ_val {N : ℕ} (hN : 0 < N) (x : Fin (2 * N)) :
    (fggsSucc hN x).val = (x.val + 1) % (2 * N) := by
  rfl

/-- The cyclic predecessor of the cyclic successor is the original index. -/
theorem fggs_pred_succ {N : ℕ} (hN : 0 < N) (x : Fin (2 * N)) :
    fggsPred hN (fggsSucc hN x) = x := by
  have h2N : 0 < 2 * N := by omega
  apply Fin.ext
  rw [fggs_pred_val, fggs_succ_val]
  by_cases h1 : x.val + 1 < 2 * N
  · rw [Nat.mod_eq_of_lt h1]
    rw [if_pos (by omega : (0 : ℕ) < x.val + 1)]
    omega
  · have h2 : x.val + 1 = 2 * N := by omega
    rw [h2, Nat.mod_self]
    rw [if_neg (by omega : ¬((0 : ℕ) < 0))]
    omega

/-- For `j < N`, increasing the FGGS index from `j` to `j + 1` is equivalent to evaluating at
the cyclic predecessor. -/
theorem fggsFull_succ {N : ℕ} (hN : 0 < N) (j : ℕ) (hj : j < N) (x : Fin (2 * N))
    (y : Fin (2 * N)) (hy : y.val = if 0 < x.val then x.val - 1 else 2 * N - 1) :
    fggsFull (j + 1) x = fggsFull j y := by
  have h2N : 0 < 2 * N := by omega
  rcases lt_trichotomy x.val 0 with hlt0 | heq0 | hgt0
  · omega
  · have h5 : ¬((0 : ℕ) < x.val) := by omega
    have h6 : x.val < N := by omega
    have h7 : x.val < j + 1 := by omega
    have h8 : ¬((2 * N - 1 : ℕ) < N) := by omega
    have h10 : ¬((2 * N - 1) - N < j) := by omega
    rw [fggsFull, fggsFull, hy, if_neg h5]
    rw [if_pos h6, if_pos h7, if_neg h8, if_neg h10]
  · rcases lt_trichotomy x.val N with hltN | heqN | hgtN
    · have h6 : x.val < N := by omega
      have h7 : x.val - 1 < N := by omega
      by_cases hA : x.val < j + 1
      · have h8 : x.val - 1 < j := by omega
        rw [fggsFull, fggsFull, hy, if_pos hgt0]
        rw [if_pos h6, if_pos h7, if_pos hA, if_pos h8]
      · have h8 : ¬(x.val - 1 < j) := by omega
        rw [fggsFull, fggsFull, hy, if_pos hgt0]
        rw [if_pos h6, if_pos h7, if_neg hA, if_neg h8]
    · have h6 : ¬((x.val : ℕ) < N) := by omega
      have h7 : x.val - N < j + 1 := by omega
      have h8 : x.val - 1 < N := by omega
      have h9 : ¬(x.val - 1 < j) := by omega
      rw [fggsFull, fggsFull, hy, if_pos hgt0]
      rw [if_neg h6, if_pos h7, if_pos h8, if_neg h9]
    · have h6 : ¬((x.val : ℕ) < N) := by omega
      have h7 : ¬((x.val - 1 : ℕ) < N) := by omega
      by_cases hA : x.val - N < j + 1
      · have h8 : (x.val - 1) - N < j := by omega
        rw [fggsFull, fggsFull, hy, if_pos hgt0]
        rw [if_neg h6, if_neg h7, if_pos hA, if_pos h8]
      · have h8 : ¬((x.val - 1) - N < j) := by omega
        rw [fggsFull, fggsFull, hy, if_pos hgt0]
        rw [if_neg h6, if_neg h7, if_neg hA, if_neg h8]

/-- The FGGS full function at `j + 1` equals its value at `j` on the cyclic predecessor when `j
< N`. -/
theorem fggsFull_succ_pred {N : ℕ} (hN : 0 < N) (j : ℕ) (hj : j < N) (x : Fin (2 * N)) :
    fggsFull (j + 1) x = fggsFull j (fggsPred hN x) :=
  fggsFull_succ hN j hj x (fggsPred hN x) (fggs_pred_val hN x)

/-- For `N = 2`, the FGGS values at `(j, x) = (1, 3)` and `(0, 0)` differ, giving a concrete
failure of the printed shift identity. -/
theorem fggs_conj_printed_refuted :
    fggsFull (N := 2) 1 ⟨3, by decide⟩ ≠ fggsFull (N := 2) 0 ⟨0, by decide⟩ := by
  norm_num [fggsFull]

/-- Expresses `fggsFull` by its threshold-dependent signs on the two halves of `Fin (2 * N)`. -/
theorem fggsFull_values (N : ℕ) (j : ℕ) (x : Fin (2 * N)) :
    fggsFull j x = if x.val < N then (if x.val < j then -1 else 1)
      else (if x.val - N < j then 1 else -1) := rfl

/-- For `j < N`, the restriction of `fggsFull j` to the first half is `fggsThreshold j`. -/
theorem fggsFull_first_half {N : ℕ} (hN : 0 < N) (j : ℕ) (hj : j < N) (x : Fin N) :
    fggsFull (N := N) j ⟨x.val, lt_trans x.is_lt (by omega)⟩ = fggsThreshold j x := by
  rw [fggsFull, fggsThreshold]
  rw [if_pos x.is_lt]

/-- The FGGS query count, fixed to six. -/
def fggsQueryCount : ℕ := 6

/-- The FGGS interval count, fixed to `2 ^ 23`. -/
def fggsIntervals : ℕ := 2 ^ 23

/-- The FGGS information threshold `500 / 27`. -/
def fggsInfoThreshold : ℝ := 500 / 27

/-- The reported FGGS information value `297 / 16`. -/
def fggsReportedInfo : ℝ := 297 / 16

/-- The printed FGGS query-rate coefficient `32 / 100`. -/
def fggsPrintedCoefficient : ℝ := 32 / 100

/-- The corrected FGGS query-rate coefficient `324 / 1000`. -/
def fggsCorrectedCoefficient : ℝ := 324 / 1000

/-- The query count divided by the reported information exceeds the printed coefficient, so
these constants do not give that rate [BenOrHassidim2007]. -/
theorem fggs_printed_not_implied :
    (fggsQueryCount : ℝ) / fggsReportedInfo > fggsPrintedCoefficient := by
  have h1 : fggsReportedInfo = 297 / 16 := rfl
  have h2 : fggsQueryCount = 6 := rfl
  have h3 : fggsPrintedCoefficient = 32 / 100 := rfl
  norm_num [h1, h2, h3, fggsReportedInfo, fggsPrintedCoefficient]

/-- The reported FGGS information value strictly exceeds the chosen information threshold. -/
theorem fggs_reported_beats_threshold : fggsInfoThreshold < fggsReportedInfo := by
  have h1 : fggsInfoThreshold = 500 / 27 := rfl
  have h2 : fggsReportedInfo = 297 / 16 := rfl
  norm_num [h1, h2, fggsInfoThreshold, fggsReportedInfo]

/-- The query count divided by the information threshold is at most the corrected coefficient,
providing the corrected numerical rate for [BenOrHassidim2007]. -/
theorem fggs_corrected_rate :
    (fggsQueryCount : ℝ) / fggsInfoThreshold ≤ fggsCorrectedCoefficient := by
  have h1 : fggsQueryCount = 6 := rfl
  have h2 : fggsInfoThreshold = 500 / 27 := rfl
  have h3 : fggsCorrectedCoefficient = 324 / 1000 := rfl
  norm_num [h1, h2, h3, fggsInfoThreshold, fggsCorrectedCoefficient]

/-- The existence of an array whose strict positivity and normalization imply the FGGS entropy
bound. -/
def FGGSInfoCertificate : Prop :=
  ∃ (Q : Fin fggsIntervals → ℝ),
    (∀ i, 0 < Q i) → (∑ i, Q i) = 1 →
      (∑ i, -(Q i * (Real.log (Q i) / Real.log 2))) ≤
        (23 : ℝ) - fggsInfoThreshold

/-- An information value strictly above `fggsInfoThreshold` gives a query-to-information ratio
strictly below `fggsCorrectedCoefficient`. -/
theorem fggs_certificate_gives_corrected_rate (I_FGGS : ℝ)
    (hI : fggsInfoThreshold < I_FGGS) :
    (fggsQueryCount : ℝ) / I_FGGS < fggsCorrectedCoefficient := by
  have h1 : fggsQueryCount = 6 := rfl
  have h3 : fggsCorrectedCoefficient = 324 / 1000 := rfl
  have hstep : (fggsQueryCount : ℝ) / fggsInfoThreshold ≤ fggsCorrectedCoefficient := by
    have h2 : fggsInfoThreshold = 500 / 27 := rfl
    norm_num [h1, h2, h3, fggsInfoThreshold, fggsCorrectedCoefficient]
  have hposT : 0 < fggsInfoThreshold := by norm_num [fggsInfoThreshold]
  have hposI : 0 < I_FGGS := lt_trans hposT hI
  have hq : (0 : ℝ) < fggsQueryCount := by norm_num [fggsQueryCount]
  have hmono : (fggsQueryCount : ℝ) / I_FGGS < (fggsQueryCount : ℝ) / fggsInfoThreshold := by
    rw [div_lt_div_iff₀ hposI hposT]
    nlinarith [mul_lt_mul_of_pos_left hI hq]
  exact lt_of_lt_of_le hmono hstep

/-- The existence of an array whose strict positivity and normalization imply the threshold
bound on `23` minus its entropy sum. -/
def FGGSMultiInfoCertificate : Prop :=
  ∃ (Q : Fin fggsIntervals → ℝ),
    (∀ i, 0 < Q i) → (∑ i, Q i) = 1 →
      23 - (∑ i, -(Q i * (Real.log (Q i) / Real.log 2))) ≥ fggsInfoThreshold

/-- The entropy and multi-information formulations of the FGGS certificate are equivalent. -/
theorem fggs_certificate_multiInfo_iff : FGGSInfoCertificate ↔ FGGSMultiInfoCertificate := by
  constructor
  · rintro ⟨Q, hQ⟩
    refine ⟨Q, ?_⟩
    intro hQ0 hQ1
    have hH := hQ hQ0 hQ1
    linarith
  · rintro ⟨Q, hQ⟩
    refine ⟨Q, ?_⟩
    intro hQ0 hQ1
    have hI := hQ hQ0 hQ1
    linarith

/-- Summing `f (h - iv)` over a nonempty finite cyclic index type gives the same result as
summing `f`. -/
theorem fggs_shift_sum {K : ℕ} (hK : 0 < K) (f : Fin K → ℝ) (h : Fin K) :
    (∑ iv, f (h - iv)) = ∑ j, f j := by
  classical
  letI : NeZero K := ⟨hK.ne'⟩
  have h1 := (Equiv.subLeft h).sum_comp f
  simpa only [Equiv.subLeft_apply] using! h1

/-- Summing `f (iv - h)` over a nonempty finite cyclic index type gives the same result as
summing `f`. -/
theorem fggs_shift_sum' {K : ℕ} (hK : 0 < K) (f : Fin K → ℝ) (h : Fin K) :
    (∑ iv, f (iv - h)) = ∑ j, f j := by
  classical
  letI : NeZero K := ⟨hK.ne'⟩
  have h1 := (Equiv.subRight h).sum_comp f
  simpa only [Equiv.subRight_apply] using! h1

/-- A normalized array `Q` gives a uniform report marginal under the uniform FGGS prior. -/
theorem fggs_reportMarginal_uniform {K : ℕ} (hK : 0 < K) (Q : Fin K → ℝ)
    (hQ : (∑ j, Q j) = 1) (h : Fin K) :
    fggsReportMarginal fggsUniformPrior Q h = 1 / K := by
  have hshift : (∑ iv, Q (h - iv)) = ∑ j, Q j := fggs_shift_sum hK Q h
  have hsum : (∑ iv, (1 / K) * Q (h - iv)) = (1 / K) * (∑ iv, Q (h - iv)) := by
    rw [Finset.mul_sum]
  show (∑ iv, (1 / K) * Q (h - iv)) = 1 / K
  calc (∑ iv, (1 / K) * Q (h - iv)) = (1 / K) * (∑ iv, Q (h - iv)) := hsum
    _ = (1 / K) * (∑ j, Q j) := by rw [hshift]
    _ = (1 / K) * 1 := by rw [hQ]
    _ = 1 / K := by ring

/-- Under the uniform FGGS prior and a normalized array `Q`, the posterior after report `h` is
`Q (h - iv)`. -/
theorem fggs_posterior_uniform {K : ℕ} (hK : 0 < K) (Q : Fin K → ℝ) (hQ : (∑ j, Q j) = 1)
    (h : Fin K) (iv : Fin K) :
    fggsPosterior fggsUniformPrior Q h iv = Q (h - iv) := by
  have hshift : (∑ iv', Q (h - iv')) = ∑ j, Q j := fggs_shift_sum hK Q h
  have hsum : (∑ iv', (1 / K) * Q (h - iv')) = (1 / K) * (∑ iv', Q (h - iv')) := by
    rw [Finset.mul_sum]
  have hden : (∑ iv', (1 / K) * Q (h - iv')) = 1 / K := by
    calc (∑ iv', (1 / K) * Q (h - iv')) = (1 / K) * (∑ iv', Q (h - iv')) := hsum
      _ = (1 / K) * (∑ j, Q j) := by rw [hshift]
      _ = (1 / K) * 1 := by rw [hQ]
      _ = 1 / K := by ring
  have hKne : (K : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hK)
  show (1 / K) * Q (h - iv) / (∑ iv', (1 / K) * Q (h - iv')) = Q (h - iv)
  rw [hden]
  field_simp

/-- For strictly positive prior and channel arrays with normalized prior, FGGS mutual
information in natural units equals report entropy minus channel entropy. -/
theorem fggs_mutualInfo_eq {K : ℕ} (hK : 0 < K) (a : Fin K → ℝ) (Q : Fin K → ℝ)
    (ha : ∀ iv, 0 < a iv) (hQ : ∀ iv, 0 < Q iv) (ha1 : (∑ iv, a iv) = 1) :
    fggsMutualInfoNat a Q
      = fggsEntropyNat (fggsReportMarginal a Q) - fggsEntropyNat Q := by
  classical
  letI : NeZero K := ⟨hK.ne'⟩
  have hP : ∀ h, 0 < fggsReportMarginal a Q h := by
    intro h
    have hpos : 0 < ∑ iv, a iv * Q (h - iv) := by
      refine Finset.sum_pos' ?_ ?_
      · intro iv _
        exact le_of_lt (mul_pos (ha iv) (hQ (h - iv)))
      · refine ⟨⟨0, hK⟩, Finset.mem_univ _, ?_⟩
        exact mul_pos (ha 0) (hQ (h - 0))
    simpa [fggsReportMarginal] using! hpos
  have hD : ∀ h, fggsReportMarginal a Q h = (∑ iv', a iv' * Q (h - iv')) := by
    intro h; rfl
  have hmul : ∀ h iv, fggsReportMarginal a Q h * fggsPosterior a Q h iv = a iv * Q (h - iv) := by
    intro h iv
    have hne : fggsReportMarginal a Q h ≠ 0 := ne_of_gt (hP h)
    show fggsReportMarginal a Q h * (a iv * Q (h - iv) / (∑ iv', a iv' * Q (h - iv')))
      = a iv * Q (h - iv)
    rw [hD h]
    exact mul_div_cancel₀ _ hne
  have hlog : ∀ h iv, Real.log (fggsPosterior a Q h iv / a iv)
      = Real.log (Q (h - iv)) - Real.log (fggsReportMarginal a Q h) := by
    intro h iv
    have hne : fggsReportMarginal a Q h ≠ 0 := ne_of_gt (hP h)
    have hne' : a iv ≠ 0 := ne_of_gt (ha iv)
    have hratio : fggsPosterior a Q h iv / a iv
        = Q (h - iv) / fggsReportMarginal a Q h := by
      show (a iv * Q (h - iv) / (∑ iv', a iv' * Q (h - iv'))) / a iv
        = Q (h - iv) / fggsReportMarginal a Q h
      rw [hD h]
      field_simp
    rw [hratio, Real.log_div (ne_of_gt (hQ (h - iv))) (ne_of_gt (hP h))]
  have hexp : fggsMutualInfoNat a Q
      = ∑ h, ((∑ iv, a iv * Q (h - iv) * Real.log (Q (h - iv)))
                - fggsReportMarginal a Q h * Real.log (fggsReportMarginal a Q h)) := by
    show (∑ h, fggsReportMarginal a Q h *
          (∑ iv, fggsPosterior a Q h iv * Real.log (fggsPosterior a Q h iv / a iv)))
        = ∑ h, ((∑ iv, a iv * Q (h - iv) * Real.log (Q (h - iv)))
                - fggsReportMarginal a Q h * Real.log (fggsReportMarginal a Q h))
    refine sum_congr' (fun h => ?_)
    have h1 : fggsReportMarginal a Q h *
          (∑ iv, fggsPosterior a Q h iv * Real.log (fggsPosterior a Q h iv / a iv))
        = ∑ iv, (fggsReportMarginal a Q h * fggsPosterior a Q h iv)
            * Real.log (fggsPosterior a Q h iv / a iv) := by
      rw [Finset.mul_sum]
      refine sum_congr' (fun iv => ?_)
      ring
    have hdist : (∑ iv, (fggsReportMarginal a Q h * fggsPosterior a Q h iv)
            * Real.log (fggsPosterior a Q h iv / a iv))
        = ∑ iv, ((fggsReportMarginal a Q h * fggsPosterior a Q h iv)
            * Real.log (Q (h - iv))
          - (fggsReportMarginal a Q h * fggsPosterior a Q h iv)
            * Real.log (fggsReportMarginal a Q h)) := by
      refine sum_congr' (fun iv => ?_)
      rw [hlog]
      ring
    have h2 : (∑ iv, ((fggsReportMarginal a Q h * fggsPosterior a Q h iv)
            * Real.log (Q (h - iv))
          - (fggsReportMarginal a Q h * fggsPosterior a Q h iv)
            * Real.log (fggsReportMarginal a Q h)))
        = (∑ iv, (fggsReportMarginal a Q h * fggsPosterior a Q h iv)
            * Real.log (Q (h - iv)))
          - (∑ iv, (fggsReportMarginal a Q h * fggsPosterior a Q h iv)
            * Real.log (fggsReportMarginal a Q h)) := by
      rw [Finset.sum_sub_distrib]
    have h3 : (∑ iv, (fggsReportMarginal a Q h * fggsPosterior a Q h iv)
            * Real.log (Q (h - iv)))
        = ∑ iv, a iv * Q (h - iv) * Real.log (Q (h - iv)) := by
      refine sum_congr' (fun iv => ?_)
      rw [hmul]
    have h4 : (∑ iv, (fggsReportMarginal a Q h * fggsPosterior a Q h iv)
            * Real.log (fggsReportMarginal a Q h))
        = fggsReportMarginal a Q h * Real.log (fggsReportMarginal a Q h) := by
      calc (∑ iv, (fggsReportMarginal a Q h * fggsPosterior a Q h iv)
            * Real.log (fggsReportMarginal a Q h))
          = ∑ iv, (a iv * Q (h - iv)) * Real.log (fggsReportMarginal a Q h) := by
              refine Finset.sum_congr rfl (fun iv _ => ?_)
              rw [hmul]
        _ = (∑ iv, a iv * Q (h - iv)) * Real.log (fggsReportMarginal a Q h) := by
              rw [← Finset.sum_mul]
        _ = fggsReportMarginal a Q h * Real.log (fggsReportMarginal a Q h) := by
              rw [fggsReportMarginal]
    rw [h1, hdist, h2, h3, h4]
  have hre : (∑ h, ∑ iv, a iv * Q (h - iv) * Real.log (Q (h - iv)))
      = ∑ iv, a iv * (∑ r, Q r * Real.log (Q r)) := by
    calc (∑ h, ∑ iv, a iv * Q (h - iv) * Real.log (Q (h - iv)))
        = ∑ iv, ∑ h, a iv * Q (h - iv) * Real.log (Q (h - iv)) := Finset.sum_comm
      _ = ∑ iv, a iv * (∑ r, Q r * Real.log (Q r)) := by
          refine Finset.sum_congr rfl (fun iv _ => ?_)
          have hshift := fggs_shift_sum' hK (fun r : Fin K => Q r * Real.log (Q r)) iv
          calc (∑ h, a iv * Q (h - iv) * Real.log (Q (h - iv)))
              = ∑ h, a iv * (Q (h - iv) * Real.log (Q (h - iv))) := by
                  refine Finset.sum_congr rfl (fun h _ => ?_)
                  ring
            _ = a iv * (∑ h, Q (h - iv) * Real.log (Q (h - iv))) := by
                  rw [Finset.mul_sum]
            _ = a iv * (∑ r, Q r * Real.log (Q r)) := by rw [hshift]
  have hre2 : (∑ iv, a iv * (∑ r, Q r * Real.log (Q r)))
      = (∑ iv, a iv) * (∑ r, Q r * Real.log (Q r)) := by
    rw [Finset.sum_mul]
  rw [hexp, Finset.sum_sub_distrib, hre, hre2, ha1]
  simp only [fggsEntropyNat, fggsReportMarginal]
  ring

/-- The natural entropy of the uniform array on `Fin K`, with `K > 0`, is `Real.log K`. -/
theorem fggs_entropy_uniform {K : ℕ} (hK : 0 < K) :
    fggsEntropyNat (K := K) (fun _ => (1 / K : ℝ)) = Real.log K := by
  have hKne : (K : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hK)
  have hlog : Real.log (1 / K) = -Real.log K := by
    rw [one_div, Real.log_inv]
  have hsum : (∑ h : Fin K, (1 / K : ℝ) * Real.log (1 / K))
      = (K : ℝ) * ((1 / K : ℝ) * Real.log (1 / K)) := by
    rw [Finset.sum_const, Finset.card_fin]
    simp
  simp only [fggsEntropyNat]
  rw [hsum, hlog]
  field_simp

/-- For positive normalized `Q`, FGGS mutual information under the uniform prior equals
`fggsMultiInfo Q`. -/
theorem fggs_mutualInfo_uniform {K : ℕ} (hK : 0 < K) (Q : Fin K → ℝ)
    (hQ : ∀ iv, 0 < Q iv) (hQ1 : (∑ j, Q j) = 1) :
    fggsMutualInfo (fggsUniformPrior : Fin K → ℝ) Q = fggsMultiInfo Q := by
  have hP : ∀ h, fggsReportMarginal fggsUniformPrior Q h = 1 / K := by
    intro h; exact fggs_reportMarginal_uniform hK Q hQ1 h
  have hsum : (∑ iv : Fin K, (fggsUniformPrior : Fin K → ℝ) iv) = 1 := by
    have hne : (K : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hK)
    have hcard : (Finset.univ : Finset (Fin K)).card = K := Finset.card_fin _
    calc (∑ iv : Fin K, (fggsUniformPrior : Fin K → ℝ) iv)
        = ((Finset.univ : Finset (Fin K)).card : ℝ) * (1 / K) := by
          show (∑ iv : Fin K, (1 / K : ℝ)) = ((Finset.univ : Finset (Fin K)).card : ℝ) * (1 / K)
          rw [Finset.sum_const, hcard]
          simp
      _ = 1 := by
        rw [hcard]
        field_simp
  have hmain := fggs_mutualInfo_eq hK (fggsUniformPrior : Fin K → ℝ) Q
    (fun iv => by simp [fggsUniformPrior]; positivity) hQ hsum
  have hent : fggsEntropyNat (fggsReportMarginal fggsUniformPrior Q)
      = fggsEntropyNat (K := K) (fun _ => (1 / K : ℝ)) := by
    simp only [fggsEntropyNat]
    have hinner : (∑ x : Fin K, fggsReportMarginal (fggsUniformPrior : Fin K → ℝ) Q x
            * Real.log (fggsReportMarginal (fggsUniformPrior : Fin K → ℝ) Q x))
        = ∑ _x : Fin K, (1 / K : ℝ) * Real.log (1 / K) := by
      refine sum_congr' (fun h => ?_)
      rw [hP h]
    rw [hinner]
  simp only [fggsMutualInfo, fggsMultiInfo, fggsEntropy]
  rw [hmain, hent, fggs_entropy_uniform hK]
  ring

/-- FGGS entropy equals the explicit sum of `-P i * log₂ (P i)` terms. -/
theorem fggs_entropy_eq_sum {K : ℕ} (P : Fin K → ℝ) :
    fggsEntropy P = (∑ i, -(P i * (Real.log (P i) / Real.log 2))) := by
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  rw [fggsEntropy, fggsEntropyNat]
  rw [← Finset.sum_neg_distrib]
  rw [Finset.sum_div]
  refine sum_congr' (fun i => ?_)
  ring

/-- The FGGS multi-information on `Fin (k + 1)` agrees with `multiInfo`. -/
theorem fggs_multiInfo_eq_frozen {k : ℕ} (Q : Fin (k + 1) → ℝ) :
    fggsMultiInfo Q = multiInfo Q := by
  rw [fggsMultiInfo, fggs_entropy_eq_sum, multiInfo]
  have hcast : (↑(k + 1) : ℝ) = ↑k + 1 := by rw [Nat.cast_succ]
  rw [hcast]

/-- For positive normalized `Q`, the mutual information of an FGGS call with uniform prior
equals `multiInfo Q`. -/
theorem fggs_callGain_eq_frozen_multiInfo {k : ℕ} (Q : Fin (k + 1) → ℝ)
    (hQ : ∀ i, 0 < Q i) (hQ1 : (∑ i, Q i) = 1) :
    fggsMutualInfo (fggsUniformPrior : Fin (k + 1) → ℝ) Q = multiInfo Q := by
  have hK : 0 < (k + 1 : ℕ) := by omega
  rw [fggs_mutualInfo_uniform hK Q hQ hQ1, fggs_multiInfo_eq_frozen]

/-- The FGGS multi-information threshold is equivalent to an entropy upper bound of `log₂ K -
fggsInfoThreshold`. -/
theorem fggs_entropy_bound_iff {K : ℕ} (Q : Fin K → ℝ) :
    fggsInfoThreshold ≤ fggsMultiInfo Q ↔
      fggsEntropy Q ≤ (Real.log K / Real.log 2) - fggsInfoThreshold := by
  have hkey : ∀ (c s : ℝ), fggsInfoThreshold ≤ c - s ↔ s ≤ c - fggsInfoThreshold := by
    intro c s
    constructor <;> intro h <;> linarith
  show fggsInfoThreshold ≤ Real.log K / Real.log 2 - fggsEntropy Q ↔ _
  exact hkey _ _

/-- The FGGS multi-information threshold is equivalent to the corresponding upper bound on the
explicit entropy sum. -/
theorem fggs_entropy_bound_iff_sum {K : ℕ} (Q : Fin K → ℝ) :
    fggsInfoThreshold ≤ fggsMultiInfo Q ↔
      (∑ i, -(Q i * (Real.log (Q i) / Real.log 2)))
        ≤ (Real.log K / Real.log 2) - fggsInfoThreshold := by
  have h1 := fggs_entropy_bound_iff Q
  have h2 : fggsEntropy Q = (∑ i, -(Q i * (Real.log (Q i) / Real.log 2))) :=
    fggs_entropy_eq_sum Q
  constructor
  · intro h
    have h' : fggsEntropy Q ≤ (Real.log K / Real.log 2) - fggsInfoThreshold := h1.mp h
    rw [← h2]
    exact h'
  · intro h
    have h' : fggsEntropy Q ≤ (Real.log K / Real.log 2) - fggsInfoThreshold := by
      rw [h2]
      exact h
    exact h1.mpr h'

/-- On the FGGS interval space, multi-information is `23` minus the explicit entropy sum. -/
theorem fggs_multiInfo_eq_sum (Q : Fin fggsIntervals → ℝ) :
    fggsMultiInfo Q
      = (23 : ℝ) - (∑ i, -(Q i * (Real.log (Q i) / Real.log 2))) := by
  have hlog : Real.log fggsIntervals / Real.log 2 = 23 := by
    have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
    rw [fggsIntervals, Nat.cast_pow, Real.log_pow]
    rw [div_eq_iff hlog2]
    norm_num
  have hsum : fggsEntropy Q = (∑ i, -(Q i * (Real.log (Q i) / Real.log 2))) :=
    fggs_entropy_eq_sum Q
  calc fggsMultiInfo Q = Real.log fggsIntervals / Real.log 2 - fggsEntropy Q := rfl
    _ = Real.log fggsIntervals / Real.log 2
        - (∑ i, -(Q i * (Real.log (Q i) / Real.log 2))) :=
      congrArg (fun e : ℝ => Real.log fggsIntervals / Real.log 2 - e) hsum
    _ = (23 : ℝ) - (∑ i, -(Q i * (Real.log (Q i) / Real.log 2))) :=
      congrArg (fun x : ℝ => x - (∑ i, -(Q i * (Real.log (Q i) / Real.log 2)))) hlog

/-- On the FGGS interval space, the information threshold is equivalent to an entropy sum at
most `23 - fggsInfoThreshold`. -/
theorem fggs_entropy_bound_iff_block (Q : Fin fggsIntervals → ℝ) :
    fggsInfoThreshold ≤ fggsMultiInfo Q ↔
      (∑ i, -(Q i * (Real.log (Q i) / Real.log 2))) ≤ (23 : ℝ) - fggsInfoThreshold := by
  have hMI := fggs_multiInfo_eq_sum Q
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- The existence of an array whose strict positivity and normalization imply `fggsInfoThreshold
≤ fggsMultiInfo Q`. -/
def FGGSActualLawCertificate : Prop :=
  ∃ (Q : Fin fggsIntervals → ℝ),
    (∀ i, 0 < Q i) → (∑ i, Q i) = 1 → fggsInfoThreshold ≤ fggsMultiInfo Q

/-- The certificate stated using `fggsMultiInfo` is equivalent to the FGGS entropy certificate. -/
theorem fggs_actualLawCertificate_iff : FGGSActualLawCertificate ↔ FGGSInfoCertificate := by
  constructor
  · rintro ⟨Q, hQ⟩
    refine ⟨Q, ?_⟩
    intro hQ0 hQ1
    have hH := hQ hQ0 hQ1
    have hMI := fggs_multiInfo_eq_sum Q
    linarith
  · rintro ⟨Q, hQ⟩
    refine ⟨Q, ?_⟩
    intro hQ0 hQ1
    have hH := hQ hQ0 hQ1
    have hMI := fggs_multiInfo_eq_sum Q
    linarith

/-- An array with FGGS multi-information strictly above the threshold has query-to-information
ratio strictly below the corrected coefficient. -/
theorem fggs_actualLaw_certificate_rate (Q : Fin fggsIntervals → ℝ)
    (hcert : fggsInfoThreshold < fggsMultiInfo Q) :
    (fggsQueryCount : ℝ) / fggsMultiInfo Q < fggsCorrectedCoefficient :=
  fggs_certificate_gives_corrected_rate (fggsMultiInfo Q) hcert

/-- The FGGS cost expression given by the query count times `log₂ n` divided by `fggsMultiInfo
Q`. -/
noncomputable def fggsExpectedQueries {K : ℕ} (Q : Fin K → ℝ) (n : ℕ) : ℝ :=
  (fggsQueryCount : ℝ) * ((Real.log n / Real.log 2) / fggsMultiInfo Q)

/-- If the FGGS query-to-information ratio is below `rho`, its cost expression is at most `rho *
log₂ n` for `n ≥ 1`. -/
theorem fggs_rate_for_public_rho {K : ℕ} (Q : Fin K → ℝ) (hI : 0 < fggsMultiInfo Q)
    (rho : ℝ) (hrho : (fggsQueryCount : ℝ) / fggsMultiInfo Q < rho) (n : ℕ) (hn : 1 ≤ n) :
    fggsExpectedQueries Q n ≤ rho * (Real.log n / Real.log 2) := by
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hIn : fggsMultiInfo Q ≠ 0 := ne_of_gt hI
  have hnlog : 0 ≤ Real.log n / Real.log 2 := by
    have h1 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    exact div_nonneg h1 (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
  unfold fggsExpectedQueries
  have hkey : (fggsQueryCount : ℝ) * ((Real.log n / Real.log 2) / fggsMultiInfo Q)
      = ((fggsQueryCount : ℝ) / fggsMultiInfo Q) * (Real.log n / Real.log 2) := by
    field_simp
  rw [hkey]
  exact mul_le_mul_of_nonneg_right (le_of_lt hrho) hnlog

/-- The Fano numerator `log₂ n - binEntropy δ - δ * log₂ (n - 1)` divided by `queryInfo p`. -/
noncomputable def fanoCapacity {n : ℕ} (δ p : ℝ) : ℝ :=
  (Real.log n / Real.log 2 - binEntropy δ
    - δ * (Real.log (n - 1) / Real.log 2)) / queryInfo p

/-- For at least two cells and zero error, `fanoCapacity` is `log₂ n / queryInfo p`. -/
theorem fanoCapacity_zero {n : ℕ} (hn : 2 ≤ n) (p : ℝ) :
    fanoCapacity (n := n) 0 p = (Real.log n / Real.log 2) / queryInfo p := by
  have hb : binEntropy 0 = 0 := by
    simp [binEntropy]
  simp [fanoCapacity, hb]

/-- At `p = 1`, the Fano capacity expression equals its numerator for at least two cells. -/
theorem fanoCapacity_p_one {n : ℕ} (hn : 2 ≤ n) (δ : ℝ) :
    fanoCapacity (n := n) δ 1 =
      Real.log n / Real.log 2 - binEntropy δ - δ * (Real.log (n - 1) / Real.log 2) := by
  have hI : queryInfo 1 = 1 := by
    simp [queryInfo, binEntropy]
  simp [fanoCapacity, hI]

/-- For two cells and nonzero query information, the Fano capacity expression is `(1 -
binEntropy δ) / queryInfo p`. -/
theorem fanoCapacity_two_cells (δ p : ℝ) (hI : queryInfo p ≠ 0) :
    fanoCapacity (n := 2) δ p = (1 - binEntropy δ) / queryInfo p := by
  have hlog : Real.log ((2 : ℕ) - 1) = 0 := by norm_num
  have hne : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hlog2 : Real.log ((2 : ℕ)) / Real.log 2 = 1 := div_self hne
  simp only [fanoCapacity]
  rw [hlog, hlog2]
  field_simp
  simp [hne]

/-- At two cells, `p = 3 / 4`, and error `1 / 4`, the printed bound exceeds one. -/
theorem printed_capacity_form_refuted :
    1 < Qatlib.Concepts.OrderedBayes.BayesRatioCore.ConsistencyChecks.printedBound 2 (3 / 4) (1 / 4) :=
  Qatlib.Concepts.OrderedBayes.BayesRatioCore.ConsistencyChecks.printed_lower_bound_exceeds_one

/-- The base-two binary entropy is `Real.binEntropy p` divided by `Real.log 2`. -/
theorem binEntropy_eq_Real_binEntropy_div (p : ℝ) :
    binEntropy p = Real.binEntropy p / Real.log 2 := by
  rw [binEntropy, Real.binEntropy]
  have e1 : Real.log p⁻¹ = -Real.log p := Real.log_inv p
  have e2 : Real.log (1 - p)⁻¹ = -Real.log (1 - p) := Real.log_inv (1 - p)
  rw [e1, e2]
  field_simp
  ring

/-- Binary entropy is nonnegative on the unit interval. -/
theorem binEntropy_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ binEntropy p := by
  rw [binEntropy_eq_Real_binEntropy_div]
  exact div_nonneg (Real.binEntropy_nonneg hp0 hp1)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

/-- The query information is positive when `1 / 2 < p < 1`. -/
theorem queryInfo_pos {p : ℝ} (hp : (1 / 2 : ℝ) < p) (hp1 : p < 1) : 0 < queryInfo p := by
  have hb : binEntropy p < 1 := by
    rw [binEntropy_eq_Real_binEntropy_div]
    have hlt : Real.binEntropy p < Real.log 2 :=
      (Real.binEntropy_lt_log_two).2 (by linarith)
    have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    rw [div_lt_iff₀ hpos]
    linarith
  unfold queryInfo
  linarith

/-- For real `m ≥ 2`, the Fano numerator vanishes at error `1 - 1 / m`. -/
theorem fanoNumerator_zero_real (m : ℝ) (hm : 2 ≤ m) :
    Real.log m / Real.log 2 - binEntropy (1 - 1 / m)
      - (1 - 1 / m) * (Real.log (m - 1) / Real.log 2) = 0 := by
  have hm0 : m ≠ 0 := by linarith
  have hm1 : m - 1 ≠ 0 := by linarith
  have hfrac : (1 : ℝ) - 1 / m = (m - 1) / m := by
    field_simp [hm0]
  have hrest : (1 : ℝ) - (1 - 1 / m) = 1 / m := by
    field_simp [hm0]
    ring
  have hlogdiv : Real.log ((m - 1) / m) = Real.log (m - 1) - Real.log m :=
    Real.log_div hm1 hm0
  have hloginv : Real.log (1 / m) = -Real.log m := by
    rw [show (1 : ℝ) / m = m⁻¹ by rw [one_div], Real.log_inv m]
  simp only [binEntropy]
  rw [hrest, hfrac, hlogdiv, hloginv]
  field_simp
  ring

/-- For an integer cell count `n ≥ 2`, the Fano numerator vanishes at error `1 - 1 / n`. -/
theorem fanoNumerator_zero {n : ℕ} (hn : 2 ≤ n) :
    Real.log n / Real.log 2 - binEntropy (1 - 1 / n)
      - (1 - 1 / n) * (Real.log (n - 1) / Real.log 2) = 0 := by
  have h := fanoNumerator_zero_real (n : ℝ) (by exact_mod_cast hn)
  exact h

/-- For `n ≥ 2`, the Fano capacity expression is zero at error `1 - 1 / n`. -/
theorem fanoCapacity_zero_at_max_error {n : ℕ} (hn : 2 ≤ n) (p : ℝ) :
    fanoCapacity (n := n) (1 - 1 / n) p = 0 := by
  have hnum := fanoNumerator_zero hn
  unfold fanoCapacity
  rw [hnum]
  simp

/-- For two cells and nonzero query information, the Fano capacity expression vanishes at error
`1 / 2`. -/
theorem fanoCapacity_two_cells_half (p : ℝ) (hI : queryInfo p ≠ 0) :
    fanoCapacity (n := 2) (1 / 2 : ℝ) p = 0 := by
  have hhalf : binEntropy (1 / 2 : ℝ) = 1 := by
    rw [binEntropy_eq_Real_binEntropy_div]
    rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.binEntropy_two_inv]
    have hne : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
    field_simp
  have hlog : Real.log ((2 : ℕ) - 1) = 0 := by norm_num
  have hne : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hlog2 : Real.log ((2 : ℕ)) / Real.log 2 = 1 := div_self hne
  simp only [fanoCapacity]
  rw [hhalf, hlog, hlog2]
  field_simp
  simp [hne]

/-- For at most one cell and error in the unit interval, the Fano numerator is nonpositive. -/
theorem fanoNumerator_le_one_cell {n : ℕ} (hn : n ≤ 1) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    Real.log n / Real.log 2 - binEntropy δ - δ * (Real.log (n - 1) / Real.log 2) ≤ 0 := by
  have hlogn : Real.log n = 0 := by
    interval_cases n <;> simp
  have hlognm : Real.log (n - 1) = 0 := by
    rw [Real.log_eq_zero]
    interval_cases n <;> simp
  rw [hlogn, hlognm]
  have hb : 0 ≤ binEntropy δ := binEntropy_nonneg hδ0 hδ1
  simp only [zero_div]
  linarith

/-- At `p = 1`, the noisy output law is concentrated at the noiseless output. -/
theorem noisyOutputProb_p_one {n : ℕ} (j : Fin n) :
    ∀ (tree : BoolQueryTree (Fin n) (Fin n)) (o : Fin n),
      noisyOutputProb j 1 tree o = if noiselessOutput j tree = o then 1 else 0 := by
  intro tree
  induction tree with
  | halt o' =>
      intro o
      rfl
  | ask c onFalse onTrue ihFalse ihTrue =>
      intro o
      by_cases hc : (c : ℕ) ≤ (j : ℕ)
      · simp [noisyOutputProb, noiselessOutput, noisyAnswerProb, hc, ihTrue, ihFalse]
      · simp [noisyOutputProb, noiselessOutput, noisyAnswerProb, hc, ihTrue, ihFalse]

/-- At `p = 1`, the noisy expected query count equals the noiseless query count. -/
theorem noisyExpectedQueries_p_one {n : ℕ} (j : Fin n) :
    ∀ (tree : BoolQueryTree (Fin n) (Fin n)),
      noisyExpectedQueries j 1 tree = noiselessQueries j tree := by
  intro tree
  induction tree with
  | halt o =>
      simp [noisyExpectedQueries, noiselessQueries]
  | ask c onFalse onTrue ihFalse ihTrue =>
      by_cases hc : (c : ℕ) ≤ (j : ℕ)
      · simp [noisyExpectedQueries, noiselessQueries, noisyAnswerProb, hc, ihTrue, ihFalse]
      · simp [noisyExpectedQueries, noiselessQueries, noisyAnswerProb, hc, ihTrue, ihFalse]

/-- The query count of a record, defined as its length. -/
noncomputable def recordQueries {n : ℕ} (t : Record n) : ℕ := t.length

/-- The number of pending transitions, defined as the record length plus one. -/
noncomputable def pendingTransitions {n : ℕ} (t : Record n) : ℕ := t.length + 1

/-- The query count of a record equals its length. -/
theorem recordQueries_eq_length {n : ℕ} (t : Record n) : recordQueries t = t.length := rfl

/-- The pending-transition count strictly exceeds the query count of every record. -/
theorem pendingTransitions_strictly_larger {n : ℕ} (t : Record n) :
    recordQueries t < pendingTransitions t := by
  simp [recordQueries, pendingTransitions]

/-- The total query count across a list of level records, obtained by summing `recordQueries`. -/
noncomputable def recursiveQueries {n : ℕ} (levels : List (Record n)) : ℕ :=
  (levels.map recordQueries).sum

/-- The recursive query count equals the sum of the query counts of its level records. -/
theorem recursiveQueries_eq_sum {n : ℕ} (levels : List (Record n)) :
    recursiveQueries levels = (levels.map recordQueries).sum := by
  rfl

/-- The recursive query count is at most the sum of the pending-transition counts of its level
records. -/
theorem recursiveQueries_le_pending {n : ℕ} (levels : List (Record n)) :
    recursiveQueries levels ≤ (levels.map pendingTransitions).sum := by
  induction levels with
  | nil => simp [recursiveQueries, pendingTransitions]
  | cons t ts ih =>
    have h1 : recordQueries t < pendingTransitions t :=
      pendingTransitions_strictly_larger t
    have h2 : recursiveQueries ts ≤ (ts.map pendingTransitions).sum := ih
    simp only [recursiveQueries, pendingTransitions, List.map_cons, List.sum_cons]
    exact Nat.add_le_add (le_of_lt h1) ih

/-- Four rational coefficients representing a linear combination of `1`, `√p`, `√(1 - p)`, and
`√(p * (1 - p))`. -/
structure AmpRep where

  a : ℚ

  b : ℚ

  c : ℚ

  d : ℚ

/-- Evaluates an amplitude representation as `a + b * √p + c * √(1 - p) + d * √(p * (1 - p))`. -/
noncomputable def AmpRep.eval (r : AmpRep) (p : ℝ) : ℝ :=
  r.a + r.b * Real.sqrt p + r.c * Real.sqrt (1 - p) + r.d * Real.sqrt (p * (1 - p))

/-- The amplitude representation with unit coefficient on `√p` and all other coefficients zero. -/
def sqrtPRep : AmpRep := ⟨0, 1, 0, 0⟩

/-- The amplitude representation with unit coefficient on `√(1 - p)` and all other coefficients
zero. -/
def sqrtOneMinusPRep : AmpRep := ⟨0, 0, 1, 0⟩

/-- Evaluating `sqrtPRep` at `p` gives `Real.sqrt p`. -/
theorem sqrtPRep_eval (p : ℝ) : (sqrtPRep : AmpRep).eval p = Real.sqrt p := by
  simp [AmpRep.eval, sqrtPRep]

/-- Evaluating `sqrtOneMinusPRep` at `p` gives `Real.sqrt (1 - p)`. -/
theorem sqrtOneMinusPRep_eval (p : ℝ) :
    (sqrtOneMinusPRep : AmpRep).eval p = Real.sqrt (1 - p) := by
  simp [AmpRep.eval, sqrtOneMinusPRep]

/-- The product of the square root of a nonnegative real number with itself is that number. -/
theorem sqrtSelfMul {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x * Real.sqrt x = x := by
  rw [← Real.sqrt_mul hx x, Real.sqrt_mul_self_eq_abs, abs_of_nonneg hx]

/-- Adds two amplitude representations coefficientwise. -/
def AmpRep.add (r s : AmpRep) : AmpRep :=
  ⟨r.a + s.a, r.b + s.b, r.c + s.c, r.d + s.d⟩

/-- Multiplies amplitude representations using the relations `(√p)^2 = p` and `(√(1 - p))^2 = 1
- p` at a fixed rational parameter. -/
def AmpRep.mul (p : ℚ) (r s : AmpRep) : AmpRep :=
  ⟨r.a * s.a + r.b * s.b * p + r.c * s.c * (1 - p) + r.d * s.d * (p * (1 - p)),
    r.a * s.b + r.b * s.a + (r.c * s.d + r.d * s.c) * (1 - p),
    r.a * s.c + r.c * s.a + (r.b * s.d + r.d * s.b) * p,
    r.a * s.d + r.d * s.a + r.b * s.c + r.c * s.b⟩

/-- Evaluation of the sum of amplitude representations equals the sum of their evaluations. -/
theorem AmpRep.eval_add (r s : AmpRep) (p : ℝ) :
    (r.add s).eval p = r.eval p + s.eval p := by
  simp only [AmpRep.add, AmpRep.eval]
  simp only [Rat.cast_add]
  ring

/-- At a rational parameter in the unit interval, evaluation of the represented product equals
the product of evaluations. -/
theorem AmpRep.eval_mul {r s : AmpRep} {p : ℚ} (hp0 : (0 : ℚ) ≤ p) (hp1 : p ≤ 1) :
    (r.mul p s).eval (p : ℝ) = r.eval (p : ℝ) * s.eval (p : ℝ) := by
  have hp0R : (0 : ℝ) ≤ p := by exact_mod_cast hp0
  have hp1R : (p : ℝ) ≤ 1 := by exact_mod_cast hp1
  have h1pR : (0 : ℝ) ≤ 1 - (p : ℝ) := by linarith
  have hppR : (0 : ℝ) ≤ (p : ℝ) * (1 - (p : ℝ)) := by positivity
  have hXX : Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) = (p : ℝ) := sqrtSelfMul hp0R
  have hYY : Real.sqrt (1 - (p : ℝ)) * Real.sqrt (1 - (p : ℝ)) = 1 - (p : ℝ) :=
    sqrtSelfMul h1pR
  have hXY : Real.sqrt (p : ℝ) * Real.sqrt (1 - (p : ℝ))
      = Real.sqrt ((p : ℝ) * (1 - (p : ℝ))) :=
    (Real.sqrt_mul hp0R (1 - (p : ℝ))).symm
  have hYX : Real.sqrt (1 - (p : ℝ)) * Real.sqrt (p : ℝ)
      = Real.sqrt ((p : ℝ) * (1 - (p : ℝ))) := by rw [mul_comm, hXY]
  have hZZ : Real.sqrt ((p : ℝ) * (1 - (p : ℝ))) * Real.sqrt ((p : ℝ) * (1 - (p : ℝ)))
      = (p : ℝ) * (1 - (p : ℝ)) := sqrtSelfMul hppR
  have hXZ : Real.sqrt (p : ℝ) * Real.sqrt ((p : ℝ) * (1 - (p : ℝ)))
      = (p : ℝ) * Real.sqrt (1 - (p : ℝ)) := by
    rw [← hXY, ← mul_assoc, hXX]
  have hZX : Real.sqrt ((p : ℝ) * (1 - (p : ℝ))) * Real.sqrt (p : ℝ)
      = (p : ℝ) * Real.sqrt (1 - (p : ℝ)) := by rw [mul_comm, hXZ]
  have hYZ : Real.sqrt (1 - (p : ℝ)) * Real.sqrt ((p : ℝ) * (1 - (p : ℝ)))
      = (1 - (p : ℝ)) * Real.sqrt (p : ℝ) := by
    rw [← hXY, ← mul_assoc, hYX, ← Real.sqrt_mul' ((p : ℝ) * (1 - (p : ℝ))) h1pR]
    have hkey2 : ((p : ℝ) * (1 - (p : ℝ))) * (1 - (p : ℝ))
        = (p : ℝ) * (1 - (p : ℝ)) ^ 2 := by ring
    rw [hkey2, Real.sqrt_mul hp0R ((1 - (p : ℝ)) ^ 2), Real.sqrt_sq_eq_abs,
      abs_of_nonneg h1pR, mul_comm]
  have hZY : Real.sqrt ((p : ℝ) * (1 - (p : ℝ))) * Real.sqrt (1 - (p : ℝ))
      = (1 - (p : ℝ)) * Real.sqrt (p : ℝ) := by rw [mul_comm, hYZ]
  simp only [AmpRep.eval, AmpRep.mul]
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_one, Rat.cast_sub]
  generalize hX : Real.sqrt (p : ℝ) = X
  generalize hY : Real.sqrt (1 - (p : ℝ)) = Y
  generalize hZ : Real.sqrt ((p : ℝ) * (1 - (p : ℝ))) = Z
  have hX' : X = Real.sqrt (p : ℝ) := hX.symm
  have hY' : Y = Real.sqrt (1 - (p : ℝ)) := hY.symm
  have hZ' : Z = Real.sqrt ((p : ℝ) * (1 - (p : ℝ))) := hZ.symm
  have rXX : X ^ 2 = (p : ℝ) := by rw [hX']; exact Real.sq_sqrt hp0R
  have rYY : Y ^ 2 = 1 - (p : ℝ) := by rw [hY']; exact Real.sq_sqrt h1pR
  have rZZ : Z ^ 2 = (p : ℝ) * (1 - (p : ℝ)) := by rw [hZ']; exact Real.sq_sqrt hppR
  have rXY : X * Y = Z := by rw [hX', hY', hZ']; exact hXY
  have rYX : Y * X = Z := by rw [hX', hY', hZ']; exact hYX
  have rXZ : X * Z = (p : ℝ) * Y := by rw [hX', hZ', hY']; exact hXZ
  have rZX : Z * X = (p : ℝ) * Y := by rw [hX', hZ', hY']; exact hZX
  have rYZ : Y * Z = (1 - (p : ℝ)) * X := by rw [hY', hZ', hX']; exact hYZ
  have rZY : Z * Y = (1 - (p : ℝ)) * X := by rw [hY', hZ', hX']; exact hZY
  linear_combination
    (-(↑r.b * ↑s.b)) * rXX
    + (-(↑r.c * ↑s.c)) * rYY
    + (-(↑r.d * ↑s.d)) * rZZ
    + (-(↑r.b * ↑s.c + ↑r.c * ↑s.b)) * rXY
    + (-(↑r.b * ↑s.d + ↑r.d * ↑s.b)) * rXZ
    + (-(↑r.c * ↑s.d + ↑r.d * ↑s.c)) * rYZ

/-- The amplitude representation for the negative of `√(1 - p)`. -/
def negSqrtOneMinusPRep : AmpRep := ⟨0, 0, -1, 0⟩

/-- Evaluating `negSqrtOneMinusPRep` gives `-Real.sqrt (1 - p)`. -/
theorem negSqrtOneMinusPRep_eval (p : ℝ) :
    (negSqrtOneMinusPRep : AmpRep).eval p = -(Real.sqrt (1 - p)) := by
  simp [AmpRep.eval, negSqrtOneMinusPRep]

/-- Every real part of a binary symmetric channel rotation entry has an `AmpRep` representation. -/
theorem bscRotation_finite_bit {p : ℝ} (out in_ : Bool) :
    ∃ r : AmpRep, r.eval p = (bscRotation p out in_).re := by
  cases out <;> cases in_
  · exact ⟨sqrtPRep, sqrtPRep_eval p⟩
  · exact ⟨negSqrtOneMinusPRep, negSqrtOneMinusPRep_eval p⟩
  · exact ⟨sqrtOneMinusPRep, sqrtOneMinusPRep_eval p⟩
  · exact ⟨sqrtPRep, sqrtPRep_eval p⟩

/-- Every real part of a diluted-oracle entry within an input block has an `AmpRep`
representation. -/
theorem dilutedOracle_block_finite_bit {n : ℕ} (f : Fin n → Bool) {p : ℝ}
    (x : Fin n) (out in_ : Bool) :
    ∃ r : AmpRep, r.eval p = (dilutedOracle f p (x, out) (x, in_)).re := by
  obtain ⟨r, hr⟩ := bscRotation_finite_bit (out) (in_ != f x)
  refine ⟨r, ?_⟩
  have hent : (dilutedOracle f p (x, out) (x, in_)).re
      = (bscRotation p out (in_ != f x)).re := by
    simp [dilutedOracle, Blockwise]
  rw [hent]
  exact hr

/-- Products of represented amplitudes possess an amplitude representation at rational
parameters in the unit interval. -/
theorem ampRep_mul_finite_bit {r s : AmpRep} {p : ℚ} (hp0 : (0 : ℚ) ≤ p) (hp1 : p ≤ 1) :
    ∃ u : AmpRep, u.eval (p : ℝ) = r.eval (p : ℝ) * s.eval (p : ℝ) := by
  refine ⟨r.mul p s, ?_⟩
  exact AmpRep.eval_mul hp0 hp1

/-- The rational binary symmetric channel answer likelihood, equal to `p` for the ideal answer
and `1 - p` otherwise. -/
def bscAnswerRat (p : ℚ) (ideal out : Bool) : ℚ :=
  if out = ideal then p else 1 - p

/-- Casting the rational channel answer likelihood to the reals gives `bscAnswerProb`. -/
theorem bscAnswerRat_eq (p : ℚ) (ideal out : Bool) :
    (bscAnswerRat p ideal out : ℝ) = bscAnswerProb (p : ℝ) ideal out := by
  by_cases h : out = ideal
  · simp [bscAnswerRat, bscAnswerProb, h]
  · simp [bscAnswerRat, bscAnswerProb, h, Rat.cast_sub]

/-- Casting a rational record likelihood to the reals gives the real record likelihood at the
same parameter. -/
theorem recordLikelihoodRat_eq {n : ℕ} (p : ℚ) :
    ∀ (t : Record n) (m : Fin n),
      (recordLikelihoodRat p t m : ℝ) = recordLikelihood t m (p : ℝ) := by
  intro t
  induction t with
  | nil =>
    intro m
    simp [recordLikelihoodRat, recordLikelihood]
  | cons obs t ih =>
    intro m
    have hrecR : recordLikelihoodRat p (obs :: t) m
        = answerLikelihoodRat m obs.1 p obs.2 * recordLikelihoodRat p t m := by
      show (obs :: t).foldr (fun obs acc => answerLikelihoodRat m obs.1 p obs.2 * acc) 1
          = answerLikelihoodRat m obs.1 p obs.2 * recordLikelihoodRat p t m
      rw [List.foldr_cons]
      rfl
    have hrec : recordLikelihood (obs :: t) m (p : ℝ)
        = answerLikelihood m obs.1 (p : ℝ) obs.2 * recordLikelihood t m (p : ℝ) := by
      show (obs :: t).foldr (fun obs acc => answerLikelihood m obs.1 (p : ℝ) obs.2 * acc) 1
          = answerLikelihood m obs.1 (p : ℝ) obs.2 * recordLikelihood t m (p : ℝ)
      rw [List.foldr_cons]
      rfl
    have hans : (answerLikelihoodRat m obs.1 p obs.2 : ℝ)
        = answerLikelihood m obs.1 (p : ℝ) obs.2 := by
      cases hb : obs.2 with
      | false =>
        by_cases hc : (obs.1 : ℕ) ≤ (m : ℕ)
        · simp [answerLikelihoodRat, answerLikelihood, bayesFalseLikelihood, hc]
        · simp [answerLikelihoodRat, answerLikelihood, bayesFalseLikelihood, hc]
      | true =>
        by_cases hc : (obs.1 : ℕ) ≤ (m : ℕ)
        · simp [answerLikelihoodRat, answerLikelihood, bayesTrueLikelihood, hc]
        · simp [answerLikelihoodRat, answerLikelihood, bayesTrueLikelihood, hc]
    rw [hrecR, hrec]
    push_cast
    rw [ih, hans]

/-- For a nonempty search space and rational `0 < p < 1`, the rational record posterior casts to
the real record posterior. -/
theorem recordPosteriorRat_eq {n : ℕ} (hn : 0 < n) (p : ℚ) (hp : 0 < p) (hp1 : p < 1)
    (t : Record n) (m : Fin n) :
    (recordPosteriorRat p t m : ℝ) = recordPosterior t (p : ℝ) m := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hp1R : (p : ℝ) < 1 := by exact_mod_cast hp1
  have hL := recordLikelihoodRat_eq p t m
  have hsumL : (∑ m', recordLikelihoodRat p t m' : ℝ) = ∑ m', recordLikelihood t m' (p : ℝ) := by
    exact Finset.sum_congr rfl (fun m _ => recordLikelihoodRat_eq p t m)
  have hpos : 0 < ∑ m', recordLikelihood t m' (p : ℝ) := by
    apply Finset.sum_pos'
    · intro m _; exact le_of_lt (recordLikelihood_pos (p : ℝ) hpR hp1R t m)
    · exact ⟨(⟨0, hn⟩ : Fin n), Finset.mem_univ _,
        recordLikelihood_pos (p : ℝ) hpR hp1R t ⟨0, hn⟩⟩
  have hreal := recordPosterior_eq_likelihood hn (p : ℝ) hpR hp1R t m
  simp only [recordPosteriorRat]
  push_cast
  rw [hL, hsumL, hreal]

/-- The rational halting cut equals the real halting cut applied to the cast rational posterior
and threshold. -/
theorem haltCutRat_eq {n : ℕ} (hn : 0 < n) (p : ℚ) (ε : ℚ) (t : Record n) :
    haltCutRat hn p ε t = haltCut hn (fun m => (recordPosteriorRat p t m : ℝ)) (ε : ℝ) := by
  have hfilter : (Finset.univ.filter fun i : Fin n => ε ≤ recordPosteriorRat p t i)
      = Finset.univ.filter fun i : Fin n => (ε : ℝ) ≤ (recordPosteriorRat p t i : ℝ) := by
    apply Finset.filter_congr
    intro i _
    constructor
    · intro h
      exact_mod_cast h
    · intro h
      exact_mod_cast h
  unfold haltCutRat haltCut
  rw [hfilter]

/-- Collects agreement of rational and real record posteriors and agreement of the halting cut
at threshold `1 / 2`. -/
theorem clause16_readout_endpoint :
    ∀ (n : ℕ) (p : ℚ) (t : Record n),
      (hn : 0 < n) → (hp : 0 < p) → (hp1 : p < 1) →
      (∀ (m : Fin n), (recordPosteriorRat p t m : ℝ) = recordPosterior t (p : ℝ) m) ∧
      (haltCutRat hn p (1 / 2) t
        = haltCut hn (fun m => (recordPosteriorRat p t m : ℝ)) ((1 / 2 : ℚ) : ℝ)) := by
  intro n p t hn hp hp1
  refine ⟨?_, ?_⟩
  · intro m
    exact recordPosteriorRat_eq hn p hp hp1 t m
  · exact haltCutRat_eq hn p (1 / 2) t

/-- Collects the corrected posterior formula, transport consistency, posterior normalization and
positivity, and discrepancies with the printed update at the cut. -/
theorem clause12_endpoint :
    ∀ (n : ℕ) (p : ℝ) (t : Record n),
      0 < n → 1 / 2 < p → p < 1 →
      (∀ (a : Fin n → ℝ) (c : Fin n) (b : Bool) (m : Fin n),
        correctPost a c p b m
          = (a m * answerLikelihood m c p b)
            / (∑ m', a m' * answerLikelihood m' c p b)) ∧
      (∀ m, transportFold t p m = recordPosterior t p m) ∧
      (∑ m, recordPosterior t p m = 1) ∧
      (∀ m, 0 < recordPosterior t p m) ∧
      (∀ (r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n),
        transportFold t p (rankIndex r hr hrn)
          = recordPosterior t p (rankIndex r hr hrn)) ∧
      (∀ (a : Fin n → ℝ) (c : Fin n),
        (∑ m, a m) = 1 → (∀ m, 0 < a m) → 2 ≤ n →
          updateTrue a c p c ≠ bayesTruePost a c p c) ∧
      (∀ (c m : Fin n), m ≠ c →
        printedTrueLikelihood c m p = bayesTrueLikelihood c m p) ∧
      (∀ c : Fin n, printedTrueLikelihood c c p ≠ bayesTrueLikelihood c c p) := by
  intro n p t hn hp hp1
  have hp0 : 0 < p := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a c b m
    exact correctPost_eq a c p b m
  · intro m
    exact transportFold_eq_recordPosterior hn p hp0 hp1 t m
  · exact recordPosterior_sum hn p hp0 hp1 t
  · intro m
    exact recordPosterior_pos hn p hp0 hp1 t m
  · intro r hr hrn
    exact transportFold_rank_eq hn p hp0 hp1 t r hr hrn
  · intro a c hsum hpos hn2
    obtain ⟨m', hne⟩ := exists_ne_cell hn2 c
    exact printed_updateTrue_ne_bayesTruePost_at_equal a c p hsum (hpos c)
      (fun m => le_of_lt (hpos m)) ⟨m', hne, hpos m'⟩ hp hp1
  · intro c m hne
    exact printedTrueLikelihood_eq_bayesTrueLikelihood p hne
  · intro c
    exact printedTrueLikelihood_ne_bayesTrueLikelihood_at_equal c p (by linarith)

/-- Collects the corrected FGGS rate constants, equivalent information certificates, cyclic
shift identities, and a counterexample to the printed shift. -/
theorem clause14_endpoint :
    (fggsQueryCount : ℝ) / fggsReportedInfo > fggsPrintedCoefficient ∧
      fggsInfoThreshold < fggsReportedInfo ∧
      (fggsQueryCount : ℝ) / fggsInfoThreshold ≤ fggsCorrectedCoefficient ∧
      (∀ (I : ℝ), fggsInfoThreshold < I →
        (fggsQueryCount : ℝ) / I < fggsCorrectedCoefficient) ∧
      (FGGSInfoCertificate ↔ FGGSMultiInfoCertificate) ∧
      (∀ {N : ℕ} (hN : 0 < N) (j : ℕ) (_hj : j < N) (x : Fin (2 * N)),
        fggsFull (j + 1) x = fggsFull j (fggsPred hN x)) ∧
      (∀ {N : ℕ} (hN : 0 < N) (x : Fin (2 * N)),
        (fggsPred hN x).val = if 0 < x.val then x.val - 1 else 2 * N - 1) ∧
      (fggsFull (N := 2) 1 ⟨3, by decide⟩ ≠ fggsFull (N := 2) 0 ⟨0, by decide⟩) ∧
      (∀ {N : ℕ} (_hN : 0 < N) (j : ℕ) (_hj : j < N) (x : Fin N),
        fggsFull (N := N) j ⟨x.val, lt_trans x.is_lt (by omega)⟩ = fggsThreshold j x) := by
  refine ⟨fggs_printed_not_implied, fggs_reported_beats_threshold,
    fggs_corrected_rate, ?_, fggs_certificate_multiInfo_iff, ?_, ?_, ?_, ?_⟩
  · intro I hI
    exact fggs_certificate_gives_corrected_rate I hI
  · intro N hN j hj x
    exact fggsFull_succ_pred hN j hj x
  · intro N hN x
    exact fggs_pred_val hN x
  · exact fggs_conj_printed_refuted
  · intro N hN j hj x
    exact fggsFull_first_half hN j hj x

/-- Collects the defining Fano capacity formula, its zero-error and noiseless specializations,
and a numerical counterexample to the printed bound. -/
theorem walkGoal_endpoint :
    (∀ {n : ℕ} (δ p : ℝ),
      fanoCapacity (n := n) δ p =
        (Real.log n / Real.log 2 - binEntropy δ - δ * (Real.log (n - 1) / Real.log 2))
          / queryInfo p) ∧
      (∀ {n : ℕ} (hn : 2 ≤ n) (p : ℝ),
        fanoCapacity (n := n) 0 p = (Real.log n / Real.log 2) / queryInfo p) ∧
      (∀ {n : ℕ} (hn : 2 ≤ n) (δ : ℝ),
        fanoCapacity (n := n) δ 1 =
          Real.log n / Real.log 2 - binEntropy δ - δ * (Real.log (n - 1) / Real.log 2)) ∧
      (∀ (δ p : ℝ), queryInfo p ≠ 0 →
        fanoCapacity (n := 2) δ p = (1 - binEntropy δ) / queryInfo p) ∧
      (1 < Qatlib.Concepts.OrderedBayes.BayesRatioCore.ConsistencyChecks.printedBound
        2 (3 / 4) (1 / 4)) := by
  refine ⟨?_, ?_, ?_, ?_, printed_capacity_form_refuted⟩
  · intro n δ p; rfl
  · intro n hn p; exact fanoCapacity_zero hn p
  · intro n hn δ; exact fanoCapacity_p_one hn δ
  · intro δ p hI; exact fanoCapacity_two_cells δ p hI

/-- When `c ≤ j`, the noiseless query count at an ask node is one plus that of its true branch. -/
theorem noiselessQueries_ask {n : ℕ} (j c : Fin n) (onFalse onTrue : BoolQueryTree (Fin n) (Fin n))
    (hc : (c : ℕ) ≤ (j : ℕ)) :
    noiselessQueries j (.ask c onFalse onTrue) = 1 + noiselessQueries j onTrue := by
  simp [noiselessQueries, hc]

/-- When `c ≤ j` fails, the noiseless query count at an ask node is one plus that of its false
branch. -/
theorem noiselessQueries_ask_neg {n : ℕ} (j c : Fin n) (onFalse onTrue : BoolQueryTree (Fin n) (Fin n))
    (hc : ¬((c : ℕ) ≤ (j : ℕ))) :
    noiselessQueries j (.ask c onFalse onTrue) = 1 + noiselessQueries j onFalse := by
  simp [noiselessQueries, hc]

/-- When `c ≤ j`, the noiseless output at an ask node is the output of its true branch. -/
theorem noiselessOutput_ask {n : ℕ} (j c : Fin n) (onFalse onTrue : BoolQueryTree (Fin n) (Fin n))
    (hc : (c : ℕ) ≤ (j : ℕ)) :
    noiselessOutput j (.ask c onFalse onTrue) = noiselessOutput j onTrue := by
  simp [noiselessOutput, hc]

/-- When `c ≤ j` fails, the noiseless output at an ask node is the output of its false branch. -/
theorem noiselessOutput_ask_neg {n : ℕ} (j c : Fin n) (onFalse onTrue : BoolQueryTree (Fin n) (Fin n))
    (hc : ¬((c : ℕ) ≤ (j : ℕ))) :
    noiselessOutput j (.ask c onFalse onTrue) = noiselessOutput j onFalse := by
  simp [noiselessOutput, hc]

/-- The cells in `S` on which the program returns the correct cell using at most `D` noiseless
queries. -/
noncomputable def correctCellsIn {n : ℕ} (S : Finset (Fin n))
    (program : BoolQueryTree (Fin n) (Fin n)) (D : ℕ) : Finset (Fin n) :=
  S.filter fun j => noiselessQueries j program ≤ D ∧ noiselessOutput j program = j

/-- If a program is correct on `S`, at most `2 ^ D` cells in `S` are identified within `D`
noiseless queries. -/
theorem correctCellsIn_card_le {n : ℕ} :
    ∀ (program : BoolQueryTree (Fin n) (Fin n)) (S : Finset (Fin n)) (D : ℕ),
      (∀ j ∈ S, noiselessOutput j program = j) →
      (correctCellsIn S program D).card ≤ 2 ^ D := by
  intro program
  induction program with
  | halt o =>
      intro S D hcorrect
      have hsub : S ⊆ ({o} : Finset (Fin n)) := by
        intro j hj
        have h1 : o = j := hcorrect j hj
        rw [h1]
        exact Finset.mem_singleton.mpr rfl
      have hfilter : S.filter (fun j => noiselessQueries j (.halt o) ≤ D
          ∧ noiselessOutput j (.halt o) = j) = S := by
        ext j
        constructor
        · intro hj
          exact (Finset.mem_filter.mp hj).1
        · intro hj
          refine Finset.mem_filter.mpr ⟨hj, ?_⟩
          have h1 : o = j := hcorrect j hj
          simp [noiselessOutput, noiselessQueries, h1]
      simp only [correctCellsIn]
      rw [hfilter]
      calc S.card ≤ ({o} : Finset (Fin n)).card := Finset.card_le_card hsub
        _ ≤ 1 := by simp
        _ ≤ 2 ^ D := Nat.one_le_two_pow
  | ask c onFalse onTrue ihFalse ihTrue =>
      intro S D hcorrect
      cases D with
      | zero =>
          have hpos : ∀ j : Fin n, 0 < noiselessQueries j (.ask c onFalse onTrue) := by
            intro j
            simp [noiselessQueries]
          have hempty : S.filter (fun j => noiselessQueries j (.ask c onFalse onTrue) ≤ 0
              ∧ noiselessOutput j (.ask c onFalse onTrue) = j) = ∅ := by
            refine Finset.filter_eq_empty_iff.mpr ?_
            intro j hj hconj
            have hposj : 0 < noiselessQueries j (.ask c onFalse onTrue) := hpos j
            have hne : ¬ noiselessQueries j (.ask c onFalse onTrue) ≤ 0 := by omega
            exact hne hconj.1
          simp only [correctCellsIn]
          rw [hempty]
          simp
      | succ k =>
          have hcorrectA : ∀ j ∈ S.filter (fun j : Fin n => (c : ℕ) ≤ (j : ℕ)),
              noiselessOutput j onTrue = j := by
            intro j hj
            have hj' := Finset.mem_filter.mp hj
            have hjS : j ∈ S := hj'.1
            have hc : (c : ℕ) ≤ (j : ℕ) := hj'.2
            have hout := hcorrect j hjS
            rw [noiselessOutput_ask j c onFalse onTrue hc] at hout
            exact hout
          have hcorrectB : ∀ j ∈ S.filter (fun j : Fin n => ¬((c : ℕ) ≤ (j : ℕ))),
              noiselessOutput j onFalse = j := by
            intro j hj
            have hj' := Finset.mem_filter.mp hj
            have hjS : j ∈ S := hj'.1
            have hc : ¬((c : ℕ) ≤ (j : ℕ)) := hj'.2
            have hout := hcorrect j hjS
            rw [noiselessOutput_ask_neg j c onFalse onTrue hc] at hout
            exact hout
          have hsplit : correctCellsIn S (.ask c onFalse onTrue) (Nat.succ k)
              = correctCellsIn (S.filter (fun j : Fin n => (c : ℕ) ≤ (j : ℕ))) onTrue k
                ∪ correctCellsIn (S.filter (fun j : Fin n => ¬((c : ℕ) ≤ (j : ℕ)))) onFalse k := by
            ext j
            simp only [correctCellsIn, Finset.mem_filter, Finset.mem_union]
            by_cases hc : (c : ℕ) ≤ (j : ℕ)
            · constructor
              · rintro ⟨hS, hq, ho⟩
                refine Or.inl ⟨⟨hS, ?_⟩, ?_⟩
                · exact hc
                · rw [noiselessQueries_ask j c onFalse onTrue hc] at hq
                  rw [noiselessOutput_ask j c onFalse onTrue hc] at ho
                  exact ⟨by omega, ho⟩
              · rintro (⟨⟨hS, hc'⟩, ⟨hq, ho⟩⟩ | ⟨⟨hS, hc'⟩, ⟨hq, ho⟩⟩)
                · refine ⟨hS, ⟨?_, ?_⟩⟩
                  · calc noiselessQueries j (.ask c onFalse onTrue)
                      = 1 + noiselessQueries j onTrue := noiselessQueries_ask j c onFalse onTrue hc'
                    _ ≤ 1 + k := by omega
                    _ ≤ Nat.succ k := by omega
                  · calc noiselessOutput j (.ask c onFalse onTrue)
                      = noiselessOutput j onTrue := noiselessOutput_ask j c onFalse onTrue hc'
                    _ = j := ho
                · exact (hc' hc).elim
            · constructor
              · rintro ⟨hS, hq, ho⟩
                refine Or.inr ⟨⟨hS, ?_⟩, ?_⟩
                · exact hc
                · rw [noiselessQueries_ask_neg j c onFalse onTrue hc] at hq
                  rw [noiselessOutput_ask_neg j c onFalse onTrue hc] at ho
                  exact ⟨by omega, ho⟩
              · rintro (⟨⟨hS, hc'⟩, ⟨hq, ho⟩⟩ | ⟨⟨hS, hc'⟩, ⟨hq, ho⟩⟩)
                · exact (hc hc').elim
                · refine ⟨hS, ⟨?_, ?_⟩⟩
                  · calc noiselessQueries j (.ask c onFalse onTrue)
                      = 1 + noiselessQueries j onFalse := noiselessQueries_ask_neg j c onFalse onTrue hc'
                    _ ≤ 1 + k := by omega
                    _ ≤ Nat.succ k := by omega
                  · calc noiselessOutput j (.ask c onFalse onTrue)
                      = noiselessOutput j onFalse := noiselessOutput_ask_neg j c onFalse onTrue hc'
                    _ = j := ho
          rw [hsplit]
          have hcardA : (correctCellsIn (S.filter (fun j : Fin n => (c : ℕ) ≤ (j : ℕ))) onTrue k).card ≤ 2 ^ k :=
            ihTrue _ k hcorrectA
          have hcardB : (correctCellsIn (S.filter (fun j : Fin n => ¬((c : ℕ) ≤ (j : ℕ)))) onFalse k).card ≤ 2 ^ k :=
            ihFalse _ k hcorrectB
          calc (correctCellsIn (S.filter (fun j : Fin n => (c : ℕ) ≤ (j : ℕ))) onTrue k
                ∪ correctCellsIn (S.filter (fun j : Fin n => ¬((c : ℕ) ≤ (j : ℕ)))) onFalse k).card
              ≤ (correctCellsIn (S.filter (fun j : Fin n => (c : ℕ) ≤ (j : ℕ))) onTrue k).card
                  + (correctCellsIn (S.filter (fun j : Fin n => ¬((c : ℕ) ≤ (j : ℕ)))) onFalse k).card :=
                Finset.card_union_le _ _
            _ ≤ 2 ^ k + 2 ^ k := by omega
            _ = 2 ^ (Nat.succ k) := by rw [Nat.pow_succ]; ring

/-- A noiseless program correct on all `n ≥ 2` cells uses at least `log₂ n` queries on some
cell. -/
theorem noiseless_counting_lower_bound {n : ℕ} (hn : 2 ≤ n)
    (program : BoolQueryTree (Fin n) (Fin n))
    (hcorrect : ∀ j : Fin n, noiselessOutput j program = j) :
    ∃ j : Fin n, Real.log n / Real.log 2 ≤ noiselessQueries j program := by
  classical
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_two hn
  have hn0R : (0 : ℝ) < n := by exact_mod_cast hn0
  letI : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
  have huniv : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty
  set depths : Finset ℕ :=
    (Finset.univ : Finset (Fin n)).image (fun j => noiselessQueries j program) with hdepths
  have hne : depths.Nonempty := Finset.image_nonempty.mpr huniv
  set D : ℕ := depths.max' hne with hD
  have hDmem : D ∈ depths := by
    rw [hD]
    exact Finset.max'_mem depths hne
  obtain ⟨j, hjmem, hj⟩ := Finset.mem_image.mp (hdepths ▸ hDmem)
  have hle_all : ∀ j' : Fin n, noiselessQueries j' program ≤ D := by
    intro j'
    have hmem' : noiselessQueries j' program ∈ depths := by
      rw [hdepths]
      exact Finset.mem_image.mpr ⟨j', Finset.mem_univ j', rfl⟩
    have h2 := Finset.le_max' depths (noiselessQueries j' program) hmem'
    rwa [show depths.max' ⟨noiselessQueries j' program, hmem'⟩ = depths.max' hne from rfl] at h2
  have hfilter : correctCellsIn (Finset.univ : Finset (Fin n)) program D = Finset.univ := by
    ext j'
    simp only [correctCellsIn, Finset.mem_filter]
    constructor
    · intro hj'
      exact Finset.mem_univ j'
    · intro _
      exact ⟨Finset.mem_univ j', hle_all j', hcorrect j'⟩
  have hcardle : (correctCellsIn (Finset.univ : Finset (Fin n)) program D).card ≤ 2 ^ D :=
    correctCellsIn_card_le program (Finset.univ : Finset (Fin n)) D (fun j _ => hcorrect j)
  have hcard : (correctCellsIn (Finset.univ : Finset (Fin n)) program D).card = n := by
    rw [hfilter]
    simp
  have hpow : (n : ℝ) ≤ (2 : ℝ) ^ D := by
    have h : n ≤ 2 ^ D := by
      have hh := hcardle
      rw [hcard] at hh
      exact hh
    have h' : ((n : ℕ) : ℝ) ≤ ((2 ^ D : ℕ) : ℝ) := by exact_mod_cast h
    simpa using! h'
  have hlog : Real.log (n : ℝ) ≤ Real.log ((2 : ℝ) ^ D) :=
    (Real.log_le_log_iff hn0R (by positivity)).mpr hpow
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hmul : Real.log (n : ℝ) ≤ D * Real.log 2 := by
    rw [Real.log_pow] at hlog
    exact hlog
  have hdiv : Real.log n / Real.log 2 ≤ D := by
    rw [div_le_iff₀ hlog2]
    exact hmul
  refine ⟨j, ?_⟩
  rw [hj]
  exact hdiv

/-- A noiseless program correct on all `n ≥ 2` cells has some input whose expected cost at `p =
1` is at least `fanoCapacity 0 1`. -/
theorem fano_capacity_lower_bound_noiseless {n : ℕ} (hn : 2 ≤ n)
    (program : BoolQueryTree (Fin n) (Fin n))
    (hcorrect : ∀ j : Fin n, noiselessOutput j program = j) :
    ∃ j : Fin n, fanoCapacity (n := n) 0 1 ≤ noisyExpectedQueries j 1 program := by
  obtain ⟨j, hj⟩ := noiseless_counting_lower_bound hn program hcorrect
  refine ⟨j, ?_⟩
  have hcap : fanoCapacity (n := n) 0 1 = Real.log n / Real.log 2 := by
    have hz : fanoCapacity (n := n) 0 1 = (Real.log n / Real.log 2) / queryInfo 1 :=
      fanoCapacity_zero hn 1
    have hI : queryInfo 1 = 1 := by
      simp [queryInfo, binEntropy]
    rw [hz, hI, div_one]
  have hne : noisyExpectedQueries j 1 program = noiselessQueries j program :=
    noisyExpectedQueries_p_one j program
  rw [hne, hcap]
  exact hj

/-- Every binary symmetric channel rotation entry is fixed by complex conjugation. -/
theorem bscRotation_star (p : ℝ) (out ideal : Bool) :
    star (bscRotation p out ideal) = bscRotation p out ideal := by
  cases out <;> cases ideal <;>
    simp [bscRotation, Complex.star_def, Complex.conj_ofReal, map_neg]

/-- For `p` in the unit interval, the columns of the binary symmetric channel rotation are
orthonormal. -/
theorem bscRotation_inner (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (a b : Bool) :
    (∑ z : Bool, star (bscRotation p z a) * bscRotation p z b)
      = if a = b then 1 else 0 := by
  have hsq1 : ((Real.sqrt p : ℝ) : ℂ) * ((Real.sqrt p : ℝ) : ℂ) = (p : ℂ) := by
    rw [← Complex.ofReal_mul]; exact_mod_cast Real.mul_self_sqrt hp0
  have hsq2 : ((Real.sqrt (1 - p) : ℝ) : ℂ) * ((Real.sqrt (1 - p) : ℝ) : ℂ) = (1 - p : ℂ) := by
    rw [← Complex.ofReal_mul]; exact_mod_cast Real.mul_self_sqrt (by linarith)
  cases a <;> cases b <;>
    simp [bscRotation, Fintype.sum_bool, Complex.star_def, Complex.conj_ofReal, map_neg] <;>
    first
    | rw [hsq1, hsq2]; norm_num
    | ring

/-- The binary symmetric channel rotation matrix is unitary for `p` in the unit interval. -/
theorem bscRotationMatrix_unitary (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    bscRotationMatrix p ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have hsq1 : ((Real.sqrt p : ℝ) : ℂ) * ((Real.sqrt p : ℝ) : ℂ) = (p : ℂ) := by
    rw [← Complex.ofReal_mul]; exact_mod_cast Real.mul_self_sqrt hp0
  have hsq2 : ((Real.sqrt (1 - p) : ℝ) : ℂ) * ((Real.sqrt (1 - p) : ℝ) : ℂ) = (1 - p : ℂ) := by
    rw [← Complex.ofReal_mul]; exact_mod_cast Real.mul_self_sqrt (by linarith)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bscRotationMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two] <;>
    first
    | rw [hsq1, hsq2]; norm_num
    | ring

/-- The star operation on a complex square matrix is its conjugate transpose. -/
theorem star_eq_conjTranspose {n : Type} (M : Matrix n n ℂ) :
    star M = Matrix.conjTranspose M := rfl

/-- The column inner-product sum of a blockwise matrix reduces to the block indexed by the first
column's input. -/
theorem Blockwise_sum_block {n : ℕ} (g : Fin n → Bool → Bool → ℂ) (i j : Fin n × Bool) :
    (∑ k : Fin n × Bool, star (Blockwise g k i) * Blockwise g k j)
      = ∑ z : Bool, star (Blockwise g (i.1, z) i) * Blockwise g (i.1, z) j := by
  classical
  rw [Fintype.sum_prod_type]
  refine Finset.sum_eq_single i.1 (fun x _ hx => ?_)
    (fun ha => (ha (Finset.mem_univ i.1)).elim)
  refine Finset.sum_eq_zero (fun z _ => ?_)
  by_cases hk : x = i.1
  · exact absurd hk hx
  · have hz : Blockwise g (x, z) i = 0 := by simp [Blockwise, hk]
    rw [hz]; simp

/-- Within a common input block, the conjugate-transpose product of `Blockwise g` is the inner
product of the corresponding block columns. -/
theorem Blockwise_conjTranspose_mul_apply {n : ℕ} (g : Fin n → Bool → Bool → ℂ)
    (i j : Fin n × Bool) (h : i.1 = j.1) :
    (Matrix.conjTranspose (Blockwise g) * (Blockwise g)) i j
      = ∑ z : Bool, star (g i.1 z i.2) * g i.1 z j.2 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply]
  rw [Blockwise_sum_block]
  refine sum_congr' (fun z => ?_)
  have hb1 : Blockwise g (i.1, z) i = g i.1 z i.2 := by
    unfold Blockwise
    rw [if_pos rfl]
  have hb2 : Blockwise g (i.1, z) j = g i.1 z j.2 := by
    have hfst : (i.1, z).1 = j.1 := h
    have hgj : g j.1 z j.2 = g i.1 z j.2 := by rw [h]
    unfold Blockwise
    rw [if_pos hfst, hgj]
  rw [hb1, hb2]

/-- Between different input blocks, the conjugate-transpose product of `Blockwise g` has zero
entries. -/
theorem Blockwise_conjTranspose_mul_apply_ne {n : ℕ} (g : Fin n → Bool → Bool → ℂ)
    (i j : Fin n × Bool) (h : i.1 ≠ j.1) :
    (Matrix.conjTranspose (Blockwise g) * (Blockwise g)) i j = 0 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply]
  rw [Blockwise_sum_block]
  refine Finset.sum_eq_zero (fun z _ => ?_)
  have hz : Blockwise g (i.1, z) j = 0 := by
    have hfst : (i.1, z).1 ≠ j.1 := fun heq => h heq
    unfold Blockwise
    rw [if_neg hfst]
  rw [hz]; simp

/-- Equality after Boolean exclusive-or with a fixed right operand implies equality of the
original operands. -/
theorem xor_inj_right (f : Bool) (a b : Bool) (h : (a != f) = (b != f)) : a = b := by
  cases a <;> cases b <;> cases f <;> simp_all

/-- The diluted oracle is unitary for every Boolean function when `p` lies in the unit interval. -/
theorem dilutedOracle_unitary {n : ℕ} (f : Fin n → Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    dilutedOracle f p ∈ Matrix.unitaryGroup (Fin n × Bool) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose]
  have hd : dilutedOracle f p = Blockwise (fun x out in_ => bscRotation p out (in_ != f x)) := rfl
  rw [hd]
  ext i j
  by_cases hxy : i.1 = j.1
  · have hblk := Blockwise_conjTranspose_mul_apply
      (fun x out in_ => bscRotation p out (in_ != f x)) i j hxy
    rw [hblk]
    rw [bscRotation_inner p hp0 hp1 (i.2 != f i.1) (j.2 != f i.1), Matrix.one_apply]
    by_cases hij2 : i.2 = j.2
    · have hij : i = j := Prod.ext hxy hij2
      simp [hij]
    · have hij : i ≠ j := by
        intro heq
        exact hij2 (congrArg Prod.snd heq)
      have hne : (i.2 != f i.1) ≠ (j.2 != f i.1) := fun h => hij2 (xor_inj_right _ _ _ h)
      simp [hne, hij]
  · have hblk := Blockwise_conjTranspose_mul_apply_ne
      (fun x out in_ => bscRotation p out (in_ != f x)) i j hxy
    rw [hblk, Matrix.one_apply]
    have hij : i ≠ j := by
      intro heq
      exact hxy (congrArg Prod.fst heq)
    simp [hij]

/-- The squared norm of a binary symmetric channel rotation entry equals the corresponding
answer probability for `0 ≤ p ≤ 1`. -/
theorem bscRotation_prob (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (out ideal : Bool) :
    (bscRotation p out ideal).normSq = bscAnswerProb p ideal out := by
  cases out <;> cases ideal <;>
    simp [bscRotation, bscAnswerProb, Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im,
      Real.sq_sqrt hp0, Real.sq_sqrt (show (0 : ℝ) ≤ 1 - p by linarith [hp0, hp1]),
      Real.mul_self_sqrt hp0,
      Real.mul_self_sqrt (show (0 : ℝ) ≤ 1 - p by linarith [hp0, hp1])]

/-- Within an input block, the squared norm of a diluted-oracle entry equals the binary
symmetric channel probability of the exclusive-or answer. -/
theorem dilutedOracle_prob {n : ℕ} (f : Fin n → Bool) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : Fin n) (out in_ : Bool) :
    (dilutedOracle f p (x, out) (x, in_)).normSq = bscAnswerProb p (in_ != f x) out := by
  have hd : dilutedOracle f p = Blockwise (fun x out in_ => bscRotation p out (in_ != f x)) := rfl
  rw [hd]
  simp [Blockwise]
  exact bscRotation_prob p hp0 hp1 out (in_ != f x)

/-- The block of the printed noisy oracle with positive square-root amplitudes for the ideal and
complementary answers. -/
noncomputable def frozenBlock {n : ℕ} (f : Fin n → Bool) (p : ℝ) (x : Fin n)
    (out in_ : Bool) : ℂ :=
  if out = (in_ != f x) then (Real.sqrt p : ℂ)
  else if out = !(in_ != f x) then (Real.sqrt (1 - p) : ℂ)
  else 0

/-- The printed noisy oracle is the blockwise matrix assembled from `frozenBlock`. -/
theorem noisyOracle_eq_blockwise {n : ℕ} (f : Fin n → Bool) (p : ℝ) :
    noisyOracle f p = Blockwise (frozenBlock f p) := rfl

/-- The inner product of the two columns of a frozen block is `2 * √p * √(1 - p)`. -/
theorem frozenBlock_offdiag {n : ℕ} (f : Fin n → Bool) (p : ℝ) (x : Fin n) :
    (∑ z : Bool, star (frozenBlock f p x z false) * frozenBlock f p x z true)
      = 2 * ((Real.sqrt p : ℝ) : ℂ) * ((Real.sqrt (1 - p) : ℝ) : ℂ) := by
  cases hff : f x <;>
    simp [frozenBlock, Fintype.sum_bool, hff, Complex.star_def, Complex.conj_ofReal] <;>
    ring

/-- For a nonempty input space and `1 / 2 < p < 1`, the printed noisy oracle is not unitary. -/
theorem noisyOracle_not_unitary {n : ℕ} (hn : 0 < n) (f : Fin n → Bool) (p : ℝ)
    (hp : (1 / 2 : ℝ) < p) (hp1 : p < 1) :
    noisyOracle f p ∉ Matrix.unitaryGroup (Fin n × Bool) ℂ := by
  haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn⟩
  have hp0 : (0 : ℝ) ≤ p := by linarith
  have hp1' : p ≤ 1 := by linarith
  intro hU
  have hGram : star (noisyOracle f p) * (noisyOracle f p) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp hU
  rw [star_eq_conjTranspose, noisyOracle_eq_blockwise] at hGram
  have hentry :
      (Matrix.conjTranspose (Blockwise (frozenBlock f p)) * (Blockwise (frozenBlock f p)))
          (0, false) (0, true)
        = (1 : Matrix (Fin n × Bool) (Fin n × Bool) ℂ) (0, false) (0, true) := by
    exact congrArg (fun A : Matrix (Fin n × Bool) (Fin n × Bool) ℂ => A (0, false) (0, true)) hGram
  have hblk := Blockwise_conjTranspose_mul_apply (frozenBlock f p) (0, false) (0, true) rfl
  have hfrz := frozenBlock_offdiag f p (0 : Fin n)
  rw [hblk, hfrz] at hentry
  have hne : (2 : ℂ) * ((Real.sqrt p : ℝ) : ℂ) * ((Real.sqrt (1 - p) : ℝ) : ℂ) ≠ 0 := by
    intro hz
    have hz' : (2 : ℝ) * Real.sqrt p * Real.sqrt (1 - p) = 0 := by exact_mod_cast hz
    have hpos' : (0 : ℝ) < 2 * Real.sqrt p * Real.sqrt (1 - p) := by
      have h1 : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.2 (by linarith)
      have h2 : (0 : ℝ) < Real.sqrt (1 - p) := Real.sqrt_pos.2 (by linarith)
      positivity
    linarith
  have hone : (1 : Matrix (Fin n × Bool) (Fin n × Bool) ℂ) (0, false) (0, true) = 0 := by
    simp [Matrix.one_apply]
  rw [hone] at hentry
  exact hne hentry

/-- Collects Fano boundary values, positivity of query information, noiseless output and cost
identities, and the noiseless capacity lower bound. -/
theorem walkGoal_boundary_endpoint :
    (∀ {n : ℕ} (hn : 2 ≤ n),
        Real.log n / Real.log 2 - binEntropy (1 - 1 / n)
          - (1 - 1 / n) * (Real.log (n - 1) / Real.log 2) = 0) ∧
      (∀ {n : ℕ} (hn : 2 ≤ n) (p : ℝ), fanoCapacity (n := n) (1 - 1 / n) p = 0) ∧
      (∀ (p : ℝ) (hI : queryInfo p ≠ 0), fanoCapacity (n := 2) (1 / 2 : ℝ) p = 0) ∧
      (∀ {n : ℕ} (hn : n ≤ 1) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1),
        Real.log n / Real.log 2 - binEntropy δ - δ * (Real.log (n - 1) / Real.log 2) ≤ 0) ∧
      (∀ {p : ℝ} (hp : (1 / 2 : ℝ) < p) (hp1 : p < 1), 0 < queryInfo p) ∧
      (∀ {n : ℕ} (j : Fin n) (tree : BoolQueryTree (Fin n) (Fin n)) (o : Fin n),
        noisyOutputProb j 1 tree o = if noiselessOutput j tree = o then 1 else 0) ∧
      (∀ {n : ℕ} (j : Fin n) (tree : BoolQueryTree (Fin n) (Fin n)),
        noisyExpectedQueries j 1 tree = noiselessQueries j tree) ∧
      (∀ {n : ℕ} (hn : 2 ≤ n) (program : BoolQueryTree (Fin n) (Fin n))
        (hcorrect : ∀ j : Fin n, noiselessOutput j program = j),
        ∃ j : Fin n, fanoCapacity (n := n) 0 1 ≤ noisyExpectedQueries j 1 program) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn; exact fanoNumerator_zero hn
  · intro n hn p; exact fanoCapacity_zero_at_max_error hn p
  · intro p hI; exact fanoCapacity_two_cells_half p hI
  · intro n hn δ hδ0 hδ1; exact fanoNumerator_le_one_cell hn δ hδ0 hδ1
  · intro p hp hp1; exact queryInfo_pos hp hp1
  · intro n j tree o; exact noisyOutputProb_p_one j tree o
  · intro n j tree; exact noisyExpectedQueries_p_one j tree
  · intro n hn program hcorrect; exact fano_capacity_lower_bound_noiseless hn program hcorrect

/-- The recursive oracle-application count equals the recursive query count. -/
theorem recursiveOracleApplications_eq (n : ℕ) (levels : List (Record n)) :
    recursiveOracleApplications levels = recursiveQueries levels := by
  have hmap : levels.map oracleApplications = levels.map recordQueries := by
    induction levels with
    | nil => rfl
    | cons t ts ih =>
        show (t :: ts).map oracleApplications = (t :: ts).map recordQueries
        simp only [List.map_cons]
        have hor : oracleApplications t = recordQueries t := rfl
        rw [hor, ih]
  rw [recursiveOracleApplications, recursiveQueries_eq_sum, hmap]

/-- A successful run at an ask node matches the recorded cut and continues along the recorded
answer branch with one fewer query. -/
theorem programRun_ask {n : ℕ} (c : Fin n) (onFalse onTrue : BoolQueryTree (Fin n) (Fin n))
    (c' : Fin n) (b : Bool) (rest : Record n) (o : Fin n) (k : ℕ)
    (h : programRun (.ask c onFalse onTrue) ((c', b) :: rest) = some (o, k)) :
    (c' = c ∧ b = true ∧ ∃ o' k', programRun onTrue rest = some (o', k') ∧ k' + 1 = k) ∨
    (c' = c ∧ b = false ∧ ∃ o' k', programRun onFalse rest = some (o', k') ∧ k' + 1 = k) := by
  by_cases hc : c' = c
  · cases b with
    | true =>
        have h' : (programRun onTrue rest).map (fun (o, k) => (o, k + 1)) = some (o, k) := by
          simpa [programRun, hc] using! h
        cases hrun : programRun onTrue rest with
        | none => simp [hrun] at h'
        | some v =>
            obtain ⟨o', k'⟩ := v
            have heq : some (o', k' + 1) = some (o, k) := by simpa [hrun] using! h'
            have heq' : o' = o ∧ k' + 1 = k := Prod.ext_iff.mp (Option.some.inj heq)
            exact Or.inl ⟨hc, rfl, o', k', rfl, heq'.2⟩
    | false =>
        have h' : (programRun onFalse rest).map (fun (o, k) => (o, k + 1)) = some (o, k) := by
          simpa [programRun, hc] using! h
        cases hrun : programRun onFalse rest with
        | none => simp [hrun] at h'
        | some v =>
            obtain ⟨o', k'⟩ := v
            have heq : some (o', k' + 1) = some (o, k) := by simpa [hrun] using! h'
            have heq' : o' = o ∧ k' + 1 = k := Prod.ext_iff.mp (Option.some.inj heq)
            exact Or.inr ⟨hc, rfl, o', k', rfl, heq'.2⟩
  · simp [programRun, hc] at h

/-- The query count returned by a successful program run equals the length of its record. -/
theorem programRun_length {n : ℕ} (tr : BoolQueryTree (Fin n) (Fin n)) (t : Record n)
    (o : Fin n) (k : ℕ) (h : programRun tr t = some (o, k)) : k = t.length := by
  induction tr generalizing t o k with
  | halt r =>
      cases t with
      | nil =>
          simp [programRun] at h
          simp only [List.length_nil]
          omega
      | cons x xs => simp [programRun] at h
  | ask c onFalse onTrue ihFalse ihTrue =>
      cases t with
      | nil => simp [programRun] at h
      | cons x xs =>
          rcases x with ⟨c', b⟩
          rcases programRun_ask c onFalse onTrue c' b xs o k h with hT | hF
          · obtain ⟨-, -, o', k', hrun, hk⟩ := hT
            have hlen := ihTrue xs o' k' hrun
            simp only [List.length_cons]
            omega
          · obtain ⟨-, -, o', k', hrun, hk⟩ := hF
            have hlen := ihFalse xs o' k' hrun
            simp only [List.length_cons]
            omega

/-- The query count returned by a successful program run is at most the tree's `MaxQueries`. -/
theorem programRun_le_maxQueries {n : ℕ} (tr : BoolQueryTree (Fin n) (Fin n))
    (t : Record n) (o : Fin n) (k : ℕ) (h : programRun tr t = some (o, k)) :
    k ≤ Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries tr := by
  induction tr generalizing t o k with
  | halt r =>
      cases t with
      | nil =>
          simp [programRun] at h
          simp only [Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries]
          omega
      | cons x xs => simp [programRun] at h
  | ask c onFalse onTrue ihFalse ihTrue =>
      cases t with
      | nil => simp [programRun] at h
      | cons x xs =>
          rcases x with ⟨c', b⟩
          rcases programRun_ask c onFalse onTrue c' b xs o k h with hT | hF
          · obtain ⟨-, -, o', k', hrun, hk⟩ := hT
            have hmq := ihTrue xs o' k' hrun
            simp only [Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries]
            omega
          · obtain ⟨-, -, o', k', hrun, hk⟩ := hF
            have hmq := ihFalse xs o' k' hrun
            simp only [Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries]
            omega

/-- Every finite Boolean query tree has a record producing a successful program run. -/
theorem programRun_exists {n : ℕ} (tr : BoolQueryTree (Fin n) (Fin n)) :
    ∃ (t : Record n) (o : Fin n) (k : ℕ), programRun tr t = some (o, k) := by
  induction tr with
  | halt r => exact ⟨[], r, 0, rfl⟩
  | ask c onFalse onTrue ihFalse ihTrue =>
      obtain ⟨tF, oF, kF, hF⟩ := ihFalse
      exact ⟨(c, false) :: tF, oF, kF + 1, by simp [programRun, hF]⟩

/-- The oracle-application count of a recursive run equals the recursive count of its level
records. -/
theorem recursivePathOracleApplications_eq {n : ℕ} (run : RecursiveRun n) :
    recursivePathOracleApplications run = recursiveOracleApplications (run.map Level.record) := by
  simp only [recursivePathOracleApplications, recursiveOracleApplications, List.map_map]
  apply congrArg (fun l : List ℕ => l.sum)
  apply List.map_congr_left
  intro l hl
  rfl

/-- The expected oracle-application cost of a recursive run equals the recursive expected cost
of its level programs. -/
theorem recursivePathExpected_eq {n : ℕ} (p : ℝ) (run : RecursiveRun n) :
    recursivePathExpectedOracleApplications p run
      = recursiveExpectedOracleApplications p (run.map Level.program) := by
  induction run with
  | nil => rfl
  | cons l ls ih =>
      have h1 : recursivePathExpectedOracleApplications p (l :: ls)
          = uniformExpectedQueries p l.program + recursivePathExpectedOracleApplications p ls := by
        simp [recursivePathExpectedOracleApplications]
      have h2 : recursiveExpectedOracleApplications p (List.map Level.program (l :: ls))
          = uniformExpectedQueries p l.program
            + recursiveExpectedOracleApplications p (List.map Level.program ls) := by
        simp [recursiveExpectedOracleApplications, List.map_cons, List.foldr_cons]
      rw [h1, h2, ih]

/-- If every level is executed, the recursive path cost is the sum of the query counts returned
by its level runs. -/
theorem recursivePath_levelwise {n : ℕ} (run : RecursiveRun n)
    (h : ∀ l ∈ run, LevelExecuted l) :
    recursivePathOracleApplications run
      = (run.map fun l => (programRun l.program l.record).map Prod.snd |>.getD 0).sum := by
  have hmap : (run.map fun l => (programRun l.program l.record).map Prod.snd |>.getD 0)
      = run.map fun l => l.record.length := by
    apply List.map_congr_left
    intro l hl
    obtain ⟨o, ho⟩ := h l hl
    simp [ho]
  rw [hmap]
  simp [recursivePathOracleApplications]

/-- If every level is executed, the recursive path cost is at most the sum of the `MaxQueries`
bounds of its level programs. -/
theorem recursivePath_le_maxQueries {n : ℕ} (run : RecursiveRun n)
    (h : ∀ l ∈ run, LevelExecuted l) :
    recursivePathOracleApplications run
      ≤ (run.map fun l => Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries l.program).sum := by
  have hle : ∀ l ∈ run, l.record.length ≤ Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries l.program := by
    intro l hl
    obtain ⟨o, ho⟩ := h l hl
    have hlen := programRun_length l.program l.record o l.record.length ho
    have hmq := programRun_le_maxQueries l.program l.record o l.record.length ho
    rw [hlen] at hmq
    exact hmq
  have hsum : ∀ (xs : List (Level n)),
      (∀ l ∈ xs, l.record.length ≤ Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries l.program) →
      (xs.map fun l => l.record.length).sum
        ≤ (xs.map fun l => Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries l.program).sum := by
    intro xs
    induction xs with
    | nil => intro _; exact le_of_eq (by simp)
    | cons x xs ih =>
        intro hxs
        have hx := hxs x List.mem_cons_self
        have hrest : ∀ l ∈ xs, l.record.length ≤ Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries l.program := by
          intro l hl
          exact hxs l (List.mem_cons_of_mem x hl)
        have hrec := ih hrest
        simp only [List.map_cons, List.sum_cons]
        omega
  rw [recursivePathOracleApplications]
  exact hsum run hle

/-- Collects query accounting, amplitude representation identities, diluted-oracle unitarity,
printed-oracle nonunitarity, and execution cost bounds for recursive runs. -/
theorem clause16_endpoint :
    (∀ {n : ℕ} (t : Record n), recordQueries t = t.length) ∧
      (∀ {n : ℕ} (t : Record n), recordQueries t < pendingTransitions t) ∧
      (∀ {n : ℕ} (levels : List (Record n)),
        recursiveQueries levels = (levels.map recordQueries).sum) ∧
      (∀ {n : ℕ} (levels : List (Record n)),
        recursiveQueries levels ≤ (levels.map pendingTransitions).sum) ∧
      (∀ (p : ℝ), (sqrtPRep : AmpRep).eval p = Real.sqrt p ∧
        (sqrtOneMinusPRep : AmpRep).eval p = Real.sqrt (1 - p)) ∧
      (∀ {n : ℕ} (f : Fin n → Bool) (p : ℝ), 0 ≤ p → p ≤ 1 →
        dilutedOracle f p ∈ Matrix.unitaryGroup (Fin n × Bool) ℂ) ∧
      (∀ {n : ℕ} (f : Fin n → Bool) (p : ℝ), (1 / 2 : ℝ) < p → p < 1 → 0 < n →
        noisyOracle f p ∉ Matrix.unitaryGroup (Fin n × Bool) ℂ) ∧
      (∀ {n : ℕ} (levels : List (Record n)),
        recursiveOracleApplications levels = recursiveQueries levels) ∧
      (∀ (r s : AmpRep) (p : ℝ), (r.add s).eval p = r.eval p + s.eval p) ∧
      (∀ (r s : AmpRep) (p : ℚ), (0 : ℚ) ≤ p → p ≤ 1 →
        (r.mul p s).eval (p : ℝ) = r.eval (p : ℝ) * s.eval (p : ℝ)) ∧
      (∀ {n : ℕ} (f : Fin n → Bool) (p : ℝ) (x : Fin n) (out in_ : Bool),
        ∃ r : AmpRep, r.eval p = (dilutedOracle f p (x, out) (x, in_)).re) ∧
      (∀ (p : ℚ) (ideal out : Bool),
        (bscAnswerRat p ideal out : ℝ) = bscAnswerProb (p : ℝ) ideal out) ∧
      (∀ {n : ℕ} (tr : BoolQueryTree (Fin n) (Fin n)) (t : Record n) (o : Fin n) (k : ℕ),
        programRun tr t = some (o, k) → k = t.length) ∧
      (∀ {n : ℕ} (tr : BoolQueryTree (Fin n) (Fin n)) (t : Record n) (o : Fin n) (k : ℕ),
        programRun tr t = some (o, k) → k ≤ Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries tr) ∧
      (∀ {n : ℕ} (tr : BoolQueryTree (Fin n) (Fin n)),
        ∃ (t : Record n) (o : Fin n) (k : ℕ), programRun tr t = some (o, k)) ∧
      (∀ {n : ℕ} (run : RecursiveRun n),
        recursivePathOracleApplications run = recursiveOracleApplications (run.map Level.record)) ∧
      (∀ {n : ℕ} (p : ℝ) (run : RecursiveRun n),
        recursivePathExpectedOracleApplications p run
          = recursiveExpectedOracleApplications p (run.map Level.program)) ∧
      (∀ {n : ℕ} (run : RecursiveRun n) (h : ∀ l ∈ run, LevelExecuted l),
        recursivePathOracleApplications run
          = (run.map fun l => (programRun l.program l.record).map Prod.snd |>.getD 0).sum) ∧
      (∀ {n : ℕ} (run : RecursiveRun n) (h : ∀ l ∈ run, LevelExecuted l),
        recursivePathOracleApplications run
          ≤ (run.map fun l => Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries l.program).sum) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n t; exact recordQueries_eq_length t
  · intro n t; exact pendingTransitions_strictly_larger t
  · intro n levels; exact recursiveQueries_eq_sum levels
  · intro n levels; exact recursiveQueries_le_pending levels
  · intro p; exact ⟨sqrtPRep_eval p, sqrtOneMinusPRep_eval p⟩
  · intro n f p hp0 hp1; exact dilutedOracle_unitary f p hp0 hp1
  · intro n f p hp hp1 hn; exact noisyOracle_not_unitary hn f p hp hp1
  · intro n levels; exact recursiveOracleApplications_eq n levels
  · intro r s p; exact AmpRep.eval_add r s p
  · intro r s p hp0 hp1; exact AmpRep.eval_mul hp0 hp1
  · intro n f p x out in_; exact dilutedOracle_block_finite_bit f x out in_
  · intro p ideal out; exact bscAnswerRat_eq p ideal out
  · intro n tr t o k h; exact programRun_length tr t o k h
  · intro n tr t o k h; exact programRun_le_maxQueries tr t o k h
  · intro n tr; exact programRun_exists tr
  · intro n run; exact recursivePathOracleApplications_eq run
  · intro n p run; exact recursivePathExpected_eq p run
  · intro n run h; exact recursivePath_levelwise run h
  · intro n run h; exact recursivePath_le_maxQueries run h

/-- For a nonnegative function on a finite set, restricting the sum to its positive terms leaves
the sum unchanged. -/
theorem sum_eq_sum_filter_pos {α : Type*} (S : Finset α) (f : α → ℝ)
    (hf : ∀ i ∈ S, 0 ≤ f i) :
    (∑ i ∈ S, f i) = ∑ i ∈ S.filter (fun i => 0 < f i), f i := by
  classical
  calc
    (∑ i ∈ S, f i) = ∑ i ∈ S, if 0 < f i then f i else 0 := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      by_cases h : 0 < f i
      · simp [h]
      · have hz : f i = 0 := by
          linarith [hf i hi]
        simp [hz]
    _ = ∑ i ∈ S.filter (fun i => 0 < f i), f i := by
      rw [Finset.sum_filter]

/-- The log-sum inequality holds for nonnegative `a`, positive `b`, and positive total mass of
`a` on a finite set. -/
theorem log_sum_ineq {α : Type*} (S : Finset α) (a b : α → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) (hb : ∀ i ∈ S, 0 < b i)
    (hA : 0 < ∑ i ∈ S, a i) :
    (∑ i ∈ S, a i * Real.log (a i / b i)) ≥ (∑ i ∈ S, a i) *
      Real.log ((∑ i ∈ S, a i) / (∑ i ∈ S, b i)) := by
  classical
  have hSne : S.Nonempty := by
    by_contra h
    have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [hempty] at hA
  have hB : 0 < ∑ i ∈ S, b i := Finset.sum_pos (fun i hi => hb i hi) hSne
  have hterm (i : α) (hiS : i ∈ S) :
      a i * Real.log ((∑ j ∈ S, a j) / (∑ j ∈ S, b j))
          - b i * ((∑ j ∈ S, a j) / (∑ j ∈ S, b j)) + a i
          ≤ a i * Real.log (a i / b i) := by
    by_cases hzero : a i = 0
    · rw [hzero]
      simp only [zero_mul, zero_sub]
      have hbi : 0 < b i := hb i hiS
      have hpos : 0 ≤ b i * ((∑ j ∈ S, a j) / (∑ j ∈ S, b j)) := by
        have hApos : 0 < ∑ j ∈ S, a j := hA
        have hBpos : 0 < ∑ j ∈ S, b j := hB
        have h1' : 0 < b i * (∑ j ∈ S, a j) := mul_pos hbi hApos
        have h2' : 0 < ∑ j ∈ S, b j := hBpos
        positivity
      linarith
    · have hapos : 0 < a i := lt_of_le_of_ne (ha i hiS) (Ne.symm hzero)
      have hbi : 0 < b i := hb i hiS
      have h1 : Real.log (b i * (∑ j ∈ S, a j) / (a i * (∑ j ∈ S, b j)))
          ≤ b i * (∑ j ∈ S, a j) / (a i * (∑ j ∈ S, b j)) - 1 :=
        Real.log_le_sub_one_of_pos (by
          have hApos : 0 < ∑ j ∈ S, a j := hA
          have hBpos : 0 < ∑ j ∈ S, b j := hB
          have h1' : 0 < b i * (∑ j ∈ S, a j) := mul_pos hbi hApos
          have h2' : 0 < a i * (∑ j ∈ S, b j) := mul_pos hapos hBpos
          exact div_pos h1' h2')
      have hmul : a i * Real.log (b i * (∑ j ∈ S, a j) / (a i * (∑ j ∈ S, b j)))
          ≤ a i * (b i * (∑ j ∈ S, a j) / (a i * (∑ j ∈ S, b j)) - 1) :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt hapos)
      have hdiv : a i * (b i * (∑ j ∈ S, a j) / (a i * (∑ j ∈ S, b j)) - 1)
          = b i * ((∑ j ∈ S, a j) / (∑ j ∈ S, b j)) - a i := by
        have hne : (∑ j ∈ S, b j) ≠ 0 := ne_of_gt hB
        field_simp
      have hlog : Real.log (b i * (∑ j ∈ S, a j) / (a i * (∑ j ∈ S, b j)))
          = Real.log ((∑ j ∈ S, a j) / (∑ j ∈ S, b j)) - Real.log (a i / b i) := by
        have hb0 : b i ≠ 0 := ne_of_gt hbi
        have hb1 : (∑ j ∈ S, b j) ≠ 0 := ne_of_gt hB
        have ha0 : a i ≠ 0 := ne_of_gt hapos
        have ha1 : (∑ j ∈ S, a j) ≠ 0 := ne_of_gt hA
        rw [Real.log_div (mul_ne_zero hb0 ha1) (mul_ne_zero ha0 hb1),
          Real.log_mul hb0 ha1, Real.log_mul ha0 hb1,
          Real.log_div ha1 hb1, Real.log_div ha0 hb0]
        ring
      have hle := hmul.trans (le_of_eq hdiv)
      rw [hlog] at hle
      linear_combination hle
  have hkey : (∑ i ∈ S, b i) * ((∑ j ∈ S, a j) / (∑ j ∈ S, b j))
      = ∑ j ∈ S, a j := by
    have hb1 : (∑ j ∈ S, b j) ≠ 0 := ne_of_gt hB
    field_simp
  have hle := Finset.sum_le_sum fun i hiS => hterm i hiS
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul] at hle
  rw [hkey] at hle
  have hsum : (∑ i ∈ S, a i * Real.log (a i / b i))
      ≥ (∑ i ∈ S, a i) * Real.log ((∑ j ∈ S, a j) / (∑ j ∈ S, b j)) := by
    have : (∑ i ∈ S, a i) * Real.log ((∑ j ∈ S, a j) / (∑ j ∈ S, b j))
        - ∑ j ∈ S, a j + ∑ j ∈ S, a j
        = (∑ i ∈ S, a i) * Real.log ((∑ j ∈ S, a j) / (∑ j ∈ S, b j)) := by ring
    rw [this] at hle
    exact hle
  exact hsum

/-- Expands the entropy of `c j * a j / d`, multiplied by positive `d`, into a sum of logarithms
for nonnegative `a` and positive `c`. -/
theorem weighted_entropy_update {n : ℕ} (a c : Fin n → ℝ) (d : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hc : ∀ j, 0 < c j) (hd : 0 < d) :
    d * entropy (fun j => c j * a j / d) =
      -(∑ j, c j * a j *
        (Real.log (c j) / Real.log 2 + Real.log (a j) / Real.log 2 - Real.log d / Real.log 2)) := by
  unfold entropy
  rw [mul_neg, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _hj
  rcases eq_or_lt_of_le (ha j) with hz | hx
  · simp [← hz]
  · rw [Real.log_div (mul_ne_zero (hc j).ne' hx.ne') hd.ne',
      Real.log_mul (hc j).ne' hx.ne']
    field_simp [hd.ne', (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']

/-- For a normalized nonnegative prior and `0 < p < 1`, the two Bayesian answer normalizers are
positive and sum to one. -/
theorem bayes_answer_probabilities {n : ℕ} (a : Fin n → ℝ) (c : Fin n) (p : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hsum : ∑ j, a j = 1) (hp : 0 < p) (hp1 : p < 1) :
    0 < bayesFalseNorm a c p ∧ 0 < bayesTrueNorm a c p ∧
      bayesFalseNorm a c p + bayesTrueNorm a c p = 1 := by
  have hpos : ∃ j, 0 < a j := by
    by_contra h
    have hj : ∀ j, ¬ 0 < a j := not_exists.mp h
    have hz : ∑ j, a j = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      exact le_antisymm (not_lt.mp (hj j)) (ha j)
    linarith [hsum]
  obtain ⟨j, hj⟩ := hpos
  have hct : ∀ m : Fin n, 0 < bayesTrueLikelihood c m p := by
    intro m
    unfold bayesTrueLikelihood
    split_ifs <;> linarith
  have hcf : ∀ m : Fin n, 0 < bayesFalseLikelihood c m p := by
    intro m
    unfold bayesFalseLikelihood
    split_ifs <;> linarith
  have hleF : a j * bayesFalseLikelihood c j p ≤ ∑ m, a m * bayesFalseLikelihood c m p :=
    Finset.single_le_sum (fun m _ => mul_nonneg (ha m) (hcf m).le) (Finset.mem_univ j)
  have hleT : a j * bayesTrueLikelihood c j p ≤ ∑ m, a m * bayesTrueLikelihood c m p :=
    Finset.single_le_sum (fun m _ => mul_nonneg (ha m) (hct m).le) (Finset.mem_univ j)
  refine ⟨?_, ?_, ?_⟩
  · have h1 : 0 < ∑ m, a m * bayesFalseLikelihood c m p := by
      have h2 : 0 < a j * bayesFalseLikelihood c j p := mul_pos hj (hcf j)
      linarith
    simpa [bayesFalseNorm] using! h1
  · have h1 : 0 < ∑ m, a m * bayesTrueLikelihood c m p := by
      have h2 : 0 < a j * bayesTrueLikelihood c j p := mul_pos hj (hct j)
      linarith
    simpa [bayesTrueNorm] using! h1
  · unfold bayesFalseNorm bayesTrueNorm
    rw [← Finset.sum_add_distrib]
    have hkey : ∀ m : Fin n,
        a m * bayesFalseLikelihood c m p + a m * bayesTrueLikelihood c m p = a m * 1 := by
      intro m
      unfold bayesFalseLikelihood bayesTrueLikelihood
      split_ifs <;> ring
    simp_rw [hkey, mul_one]
    rw [hsum]

/-- For a normalized nonnegative prior and `1 / 2 < p < 1`, the expected posterior information
gain is `binEntropy (bayesFalseNorm a c p) - binEntropy p`. -/
theorem corrected_expected_info_identity {n : ℕ} (a : Fin n → ℝ) (c : Fin n) (p : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hsum : ∑ j, a j = 1) (hp : 1 / 2 < p) (hp1 : p < 1) :
    bayesFalseNorm a c p * (postInfo (bayesFalsePost a c p) - postInfo a) +
      bayesTrueNorm a c p * (postInfo (bayesTruePost a c p) - postInfo a) =
        binEntropy (bayesFalseNorm a c p) - binEntropy p := by
  obtain ⟨hF, hT, hsum1⟩ :=
    bayes_answer_probabilities a c p ha hsum (show 0 < p by linarith) hp1
  have hct : ∀ j : Fin n, 0 < bayesTrueLikelihood c j p := by
    intro j; unfold bayesTrueLikelihood; split_ifs <;> linarith
  have hcf : ∀ j : Fin n, 0 < bayesFalseLikelihood c j p := by
    intro j; unfold bayesFalseLikelihood; split_ifs <;> linarith
  set cF : Fin n → ℝ := fun j => bayesFalseLikelihood c j p with hcFdef
  set cT : Fin n → ℝ := fun j => bayesTrueLikelihood c j p with hcTdef
  have hcF : ∀ j, 0 < cF j := by intro j; dsimp [cF]; exact hcf j
  have hcT : ∀ j, 0 < cT j := by intro j; dsimp [cT]; exact hct j
  have hUF : bayesFalsePost a c p = fun j => cF j * a j / bayesFalseNorm a c p := by
    ext j; dsimp [bayesFalsePost, cF]; ring
  have hUT : bayesTruePost a c p = fun j => cT j * a j / bayesTrueNorm a c p := by
    ext j; dsimp [bayesTruePost, cT]; ring
  have hFs : ∑ j, cF j * a j = bayesFalseNorm a c p := by
    have hfun : (fun j => cF j * a j) = fun j => a j * bayesFalseLikelihood c j p := by
      funext j; dsimp [cF]; ring
    rw [hfun]
    unfold bayesFalseNorm
    rfl
  have hTs : ∑ j, cT j * a j = bayesTrueNorm a c p := by
    have hfun : (fun j => cT j * a j) = fun j => a j * bayesTrueLikelihood c j p := by
      funext j; dsimp [cT]; ring
    rw [hfun]
    unfold bayesTrueNorm
    rfl
  have hrow (j : Fin n) :
      cF j * a j * (Real.log (cF j) / Real.log 2 + Real.log (a j) / Real.log 2 -
          Real.log (bayesFalseNorm a c p) / Real.log 2) +
        cT j * a j * (Real.log (cT j) / Real.log 2 + Real.log (a j) / Real.log 2 -
          Real.log (bayesTrueNorm a c p) / Real.log 2) =
      a j * (Real.log (a j) / Real.log 2) +
        a j * (p * (Real.log p / Real.log 2) + (1 - p) * (Real.log (1 - p) / Real.log 2)) -
        (cF j * a j) * (Real.log (bayesFalseNorm a c p) / Real.log 2) -
        (cT j * a j) * (Real.log (bayesTrueNorm a c p) / Real.log 2) := by
    dsimp [cF, cT, bayesFalseLikelihood, bayesTrueLikelihood]
    split_ifs <;> ring
  have hcomp : bayesTrueNorm a c p = 1 - bayesFalseNorm a c p := by linarith
  have hraw : bayesFalseNorm a c p * entropy (bayesFalsePost a c p) +
      bayesTrueNorm a c p * entropy (bayesTruePost a c p) =
        entropy a + binEntropy p - binEntropy (bayesFalseNorm a c p) := by
    rw [hUF, hUT, weighted_entropy_update a cF _ ha hcF hF,
      weighted_entropy_update a cT _ ha hcT hT, ← neg_add, ← Finset.sum_add_distrib]
    simp_rw [hrow]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, hsum, hFs, hTs]
    unfold entropy binEntropy
    rw [hcomp]
    ring
  unfold postInfo
  rw [hcomp] at hraw ⊢
  linear_combination -hraw

/-- The real-valued binary entropy expression is at most one. -/
theorem binEntropy_le_one {x : ℝ} : binEntropy x ≤ 1 := by
  have hconv : binEntropy x = Real.binEntropy x / Real.log 2 := by
    simp only [binEntropy, Real.binEntropy, Real.log_inv]
    ring
  rw [hconv]
  have h := Real.binEntropy_le_log_two (p := x)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_le_iff₀ hlog2]
  linarith

/-- For a normalized nonnegative prior and `1 / 2 < p < 1`, the expected information gain of one
corrected Bayesian query is at most `queryInfo p`. -/
theorem channel_bound {n : ℕ} (a : Fin n → ℝ) (c : Fin n) (p : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hsum : ∑ j, a j = 1) (hp : 1 / 2 < p) (hp1 : p < 1) :
    bayesFalseNorm a c p * (postInfo (bayesFalsePost a c p) - postInfo a) +
      bayesTrueNorm a c p * (postInfo (bayesTruePost a c p) - postInfo a) ≤ queryInfo p := by
  rw [corrected_expected_info_identity a c p ha hsum hp hp1]
  have h1 : binEntropy (bayesFalseNorm a c p) ≤ 1 := binEntropy_le_one
  have h2 : binEntropy p ≤ 1 := binEntropy_le_one
  have hq : queryInfo p = 1 - binEntropy p := by simp [queryInfo]
  rw [hq]
  linarith

/-- The true-answer Bayesian posterior is pointwise nonnegative for a nonnegative prior and `p`
in the unit interval. -/
theorem bayesTruePost_nonneg {n : ℕ} (a : Fin n → ℝ) (c : Fin n) (p : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ j, 0 ≤ bayesTruePost a c p j := by
  intro j
  unfold bayesTruePost
  have hnorm : 0 ≤ bayesTrueNorm a c p := by
    unfold bayesTrueNorm
    exact Finset.sum_nonneg fun j _ => mul_nonneg (ha j) (by
      unfold bayesTrueLikelihood; split_ifs <;> linarith)
  have hnum : 0 ≤ a j * bayesTrueLikelihood c j p := by
    exact mul_nonneg (ha j) (by
      unfold bayesTrueLikelihood; split_ifs <;> linarith)
  exact div_nonneg hnum hnorm

/-- The false-answer Bayesian posterior is pointwise nonnegative for a nonnegative prior and `p`
in the unit interval. -/
theorem bayesFalsePost_nonneg {n : ℕ} (a : Fin n → ℝ) (c : Fin n) (p : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ j, 0 ≤ bayesFalsePost a c p j := by
  intro j
  unfold bayesFalsePost
  have hnorm : 0 ≤ bayesFalseNorm a c p := by
    unfold bayesFalseNorm
    exact Finset.sum_nonneg fun j _ => mul_nonneg (ha j) (by
      unfold bayesFalseLikelihood; split_ifs <;> linarith)
  have hnum : 0 ≤ a j * bayesFalseLikelihood c j p := by
    exact mul_nonneg (ha j) (by
      unfold bayesFalseLikelihood; split_ifs <;> linarith)
  exact div_nonneg hnum hnorm

/-- For a normalized nonnegative prior and `0 < p < 1`, the true-answer Bayesian posterior has
total mass one. -/
theorem bayesTruePost_sum {n : ℕ} (a : Fin n → ℝ) (c : Fin n) (p : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hsum : (∑ j, a j) = 1) (hp : 0 < p) (hp1 : p < 1) :
    (∑ j, bayesTruePost a c p j) = 1 := by
  obtain ⟨_, hT, _⟩ := bayes_answer_probabilities a c p ha hsum hp hp1
  have hdiv : (∑ j, bayesTruePost a c p j)
      = (∑ j, a j * bayesTrueLikelihood c j p) / bayesTrueNorm a c p := by
    unfold bayesTruePost
    rw [← Finset.sum_div]
  rw [hdiv]
  have : (∑ j, a j * bayesTrueLikelihood c j p) = bayesTrueNorm a c p := rfl
  rw [this]
  exact div_self hT.ne'

/-- For a normalized nonnegative prior and `0 < p < 1`, the false-answer Bayesian posterior has
total mass one. -/
theorem bayesFalsePost_sum {n : ℕ} (a : Fin n → ℝ) (c : Fin n) (p : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hsum : (∑ j, a j) = 1) (hp : 0 < p) (hp1 : p < 1) :
    (∑ j, bayesFalsePost a c p j) = 1 := by
  obtain ⟨hF, _, _⟩ := bayes_answer_probabilities a c p ha hsum hp hp1
  have hdiv : (∑ j, bayesFalsePost a c p j)
      = (∑ j, a j * bayesFalseLikelihood c j p) / bayesFalseNorm a c p := by
    unfold bayesFalsePost
    rw [← Finset.sum_div]
  rw [hdiv]
  have : (∑ j, a j * bayesFalseLikelihood c j p) = bayesFalseNorm a c p := rfl
  rw [this]
  exact div_self hF.ne'

/-- For a normalized nonnegative prior, nonnegative weight, and `1 / 2 < p < 1`, tree
information gain is at most `queryInfo p` times weighted tree depth. -/
theorem treeInfo_le {n : ℕ} (p : ℝ) (tr : BoolQueryTree (Fin n) (Fin n))
    (a : Fin n → ℝ) (W : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hsum : (∑ j, a j) = 1) (hW : 0 ≤ W)
    (hp : 1 / 2 < p) (hp1 : p < 1) :
    treeInfo p tr a W ≤ queryInfo p * treeDepth p tr a W := by
  induction tr generalizing a W with
  | halt o => simp [treeInfo, treeDepth]
  | ask c onFalse onTrue ihFalse ihTrue =>
    obtain ⟨hF, hT, hcomp⟩ :=
      bayes_answer_probabilities a c p ha hsum (show 0 < p by linarith) hp1
    have haF : ∀ j, 0 ≤ bayesFalsePost a c p j :=
      bayesFalsePost_nonneg a c p ha (show 0 ≤ p by linarith) hp1.le
    have haT : ∀ j, 0 ≤ bayesTruePost a c p j :=
      bayesTruePost_nonneg a c p ha (show 0 ≤ p by linarith) hp1.le
    have hsF : (∑ j, bayesFalsePost a c p j) = 1 :=
      bayesFalsePost_sum a c p ha hsum (show 0 < p by linarith) hp1
    have hsT : (∑ j, bayesTruePost a c p j) = 1 :=
      bayesTruePost_sum a c p ha hsum (show 0 < p by linarith) hp1
    have h1 := ihFalse (bayesFalsePost a c p) (W * bayesFalseNorm a c p) haF hsF
      (mul_nonneg hW hF.le)
    have h2 := ihTrue (bayesTruePost a c p) (W * bayesTrueNorm a c p) haT hsT
      (mul_nonneg hW hT.le)
    have hchan := channel_bound a c p ha hsum hp hp1
    have hstep :
        W * bayesFalseNorm a c p * (postInfo (bayesFalsePost a c p) - postInfo a) +
          W * bayesTrueNorm a c p * (postInfo (bayesTruePost a c p) - postInfo a)
          ≤ W * queryInfo p := by
      have hmul := mul_le_mul_of_nonneg_left hchan hW
      calc
        W * bayesFalseNorm a c p * (postInfo (bayesFalsePost a c p) - postInfo a) +
            W * bayesTrueNorm a c p * (postInfo (bayesTruePost a c p) - postInfo a)
            = W * (bayesFalseNorm a c p * (postInfo (bayesFalsePost a c p) - postInfo a) +
                bayesTrueNorm a c p * (postInfo (bayesTruePost a c p) - postInfo a)) := by ring
        _ ≤ W * queryInfo p := hmul
    rw [treeInfo, treeDepth]
    calc
      W * bayesFalseNorm a c p * (postInfo (bayesFalsePost a c p) - postInfo a) +
          W * bayesTrueNorm a c p * (postInfo (bayesTruePost a c p) - postInfo a) +
          treeInfo p onFalse (bayesFalsePost a c p) (W * bayesFalseNorm a c p) +
          treeInfo p onTrue (bayesTruePost a c p) (W * bayesTrueNorm a c p)
        ≤ W * queryInfo p +
          queryInfo p * treeDepth p onFalse (bayesFalsePost a c p) (W * bayesFalseNorm a c p) +
          queryInfo p * treeDepth p onTrue (bayesTruePost a c p) (W * bayesTrueNorm a c p) := by
            linarith [hstep, h1, h2]
      _ = queryInfo p * (W +
            treeDepth p onFalse (bayesFalsePost a c p) (W * bayesFalseNorm a c p) +
            treeDepth p onTrue (bayesTruePost a c p) (W * bayesTrueNorm a c p)) := by ring
      _ = queryInfo p * treeDepth p (.ask c onFalse onTrue) a W := by rfl

/-- For a nonempty search space with uniform prior, tree information gain is at most `queryInfo
p` times expected queries when `1 / 2 < p < 1`. -/
theorem walkGoal_information_accounting {n : ℕ} (p : ℝ) (tr : BoolQueryTree (Fin n) (Fin n))
    (hp : 1 / 2 < p) (hp1 : p < 1) (hn : 0 < n) :
    treeInfo p tr (uniformPosterior (n := n)) 1 ≤ queryInfo p * uniformExpectedQueries p tr := by
  have ha : ∀ j : Fin n, 0 ≤ uniformPosterior (n := n) j := by
    intro j
    simp [uniformPosterior]
  have hsum : (∑ j, uniformPosterior (n := n) j) = 1 := uniform_sum hn
  exact treeInfo_le p tr (uniformPosterior (n := n)) 1 ha hsum (by norm_num) hp hp1

/-- Collects the one-query information bound and its extensions to weighted trees and the
uniform prior. -/
theorem walkGoal_channel_endpoint :
    (∀ {n : ℕ} (a : Fin n → ℝ) (c : Fin n) (p : ℝ),
      (∀ j, 0 ≤ a j) → (∑ j, a j = 1) → (1 / 2 : ℝ) < p → p < 1 →
      bayesFalseNorm a c p * (postInfo (bayesFalsePost a c p) - postInfo a) +
        bayesTrueNorm a c p * (postInfo (bayesTruePost a c p) - postInfo a) ≤ queryInfo p) ∧
    (∀ {n : ℕ} (p : ℝ) (tr : BoolQueryTree (Fin n) (Fin n)),
      (1 / 2 : ℝ) < p → p < 1 → 0 < n →
      treeInfo p tr (uniformPosterior (n := n)) 1 ≤
        queryInfo p * uniformExpectedQueries p tr) ∧
    (∀ {n : ℕ} (p : ℝ) (tr : BoolQueryTree (Fin n) (Fin n)) (a : Fin n → ℝ) (W : ℝ),
      (∀ j, 0 ≤ a j) → (∑ j, a j = 1) → 0 ≤ W → (1 / 2 : ℝ) < p → p < 1 →
      treeInfo p tr a W ≤ queryInfo p * treeDepth p tr a W) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n a c p ha hsum hp hp1; exact channel_bound a c p ha hsum hp hp1
  · intro n p tr hp hp1 hn; exact walkGoal_information_accounting p tr hp hp1 hn
  · intro n p tr a W ha hsum hW hp hp1; exact treeInfo_le p tr a W ha hsum hW hp hp1

/-- Entropy is the negative sum of `a j * Real.log (a j)` divided by `Real.log 2`. -/
theorem entropy_eq_neg_slog {n : ℕ} (a : Fin n → ℝ) :
    entropy a = -(∑ j, a j * Real.log (a j)) / Real.log 2 := by
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  unfold entropy
  have hpoint (j : Fin n) :
      a j * (Real.log (a j) / Real.log 2) = (a j * Real.log (a j)) / Real.log 2 := by
    field_simp
  have hconv : (∑ j, a j * (Real.log (a j) / Real.log 2))
      = (∑ j, a j * Real.log (a j)) / Real.log 2 := by
    calc (∑ j, a j * (Real.log (a j) / Real.log 2))
        = ∑ j, (a j * Real.log (a j)) / Real.log 2 := by
          apply Finset.sum_congr rfl
          intro j _
          exact hpoint j
      _ = (∑ j, a j * Real.log (a j)) / Real.log 2 := by
          rw [← Finset.sum_div]
  rw [hconv]
  ring

/-- For normalized nonnegative weights on a nonempty finite set, natural entropy is at most the
logarithm of its cardinality. -/
theorem maxEntropy_log_le {n : ℕ} (S : Finset (Fin n)) (w : Fin n → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hsum : (∑ i ∈ S, w i) = 1) (hcard : 0 < S.card) :
    -(∑ i ∈ S, w i * Real.log (w i)) ≤ Real.log S.card := by
  classical
  have hcardne : (S.card : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hcard
  have hcardpos : (0 : ℝ) < S.card := by exact_mod_cast hcard
  have hone : (1 : ℝ) / S.card ≠ 0 := by positivity
  have hb : ∀ i ∈ S, 0 < (1 : ℝ) / S.card := by
    intro i hi
    positivity
  have hbsum : (∑ i ∈ S, (1 : ℝ) / S.card) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp
  have hineq := log_sum_ineq S w (fun _ => 1 / S.card) hw hb (by rw [hsum]; norm_num)
  have hmain : (∑ i ∈ S, w i * Real.log (w i / (1 / S.card))) ≥ 0 := by
    rw [hsum, hbsum] at hineq
    have hone : (1 : ℝ) / 1 = 1 := by norm_num
    rw [hone, Real.log_one, mul_zero] at hineq
    exact hineq
  have hpoint (i : Fin n) (hi : i ∈ S) :
      w i * Real.log (w i / (1 / S.card)) =
        w i * Real.log (w i) + w i * Real.log (S.card) := by
    by_cases hw0 : w i = 0
    · rw [hw0]
      simp
    · have hw0' : w i ≠ 0 := ne_of_gt (lt_of_le_of_ne (hw i hi) (Ne.symm hw0))
      have hsplit : w i / (1 / S.card) = w i * S.card := by
        field_simp
      rw [hsplit]
      have hlog : Real.log (w i * S.card) = Real.log (w i) + Real.log (S.card) := by
        rw [Real.log_mul hw0' hcardne]
      rw [hlog]
      ring
  have hsum2 : (∑ i ∈ S, w i * Real.log (w i / (1 / S.card)))
      = (∑ i ∈ S, w i * Real.log (w i)) + (∑ i ∈ S, w i) * Real.log (S.card) := by
    calc (∑ i ∈ S, w i * Real.log (w i / (1 / S.card)))
        = (∑ i ∈ S, (w i * Real.log (w i) + w i * Real.log (S.card))) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hpoint i hi
      _ = (∑ i ∈ S, w i * Real.log (w i)) + (∑ i ∈ S, w i * Real.log (S.card)) := by
          rw [Finset.sum_add_distrib]
      _ = (∑ i ∈ S, w i * Real.log (w i)) + (∑ i ∈ S, w i) * Real.log (S.card) := by
          rw [Finset.sum_mul]
  rw [hsum2, hsum] at hmain
  linarith

/-- Summing negative terms divided by `Real.log 2` equals the negative of their sum divided by
`Real.log 2`. -/
theorem sum_neg_div_log2 {α : Type} [DecidableEq α] (S : Finset α) (f : α → ℝ) :
    (∑ i ∈ S, (-(f i)) / Real.log 2) = -(∑ i ∈ S, f i) / Real.log 2 := by
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  calc (∑ i ∈ S, (-(f i)) / Real.log 2)
      = ∑ i ∈ S, (-(f i)) * (1 / Real.log 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        field_simp
    _ = (∑ i ∈ S, -(f i)) * (1 / Real.log 2) := by
        rw [Finset.sum_mul]
    _ = -(∑ i ∈ S, f i) / Real.log 2 := by
        rw [Finset.sum_neg_distrib]
        field_simp

/-- Binary entropy of a finite convex combination is at least the corresponding convex
combination of binary entropies. -/
theorem binEntropy_mix {α : Type} [Fintype α] (S : Finset α) (w x : α → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hsum : (∑ i ∈ S, w i) = 1)
    (hx : ∀ i ∈ S, 0 ≤ x i) (hx1 : ∀ i ∈ S, x i ≤ 1) :
    (∑ i ∈ S, w i * binEntropy (x i)) ≤ binEntropy (∑ i ∈ S, w i * x i) := by
  classical
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog2ne : Real.log 2 ≠ 0 := ne_of_gt hlog2pos

  have hL (z : ℝ) : binEntropy z * Real.log 2
      = -(z * Real.log z + (1 - z) * Real.log (1 - z)) := by
    rw [binEntropy]
    field_simp

  set S' : Finset α := S.filter (fun i => 0 < w i) with hS'
  have hS'sub : S' ⊆ S := Finset.filter_subset _ _
  have hwS' : ∀ i ∈ S', 0 < w i := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hzeros : ∀ x ∈ S, x ∉ S' → w x = 0 := by
    intro x hxS hxnot
    by_contra h
    refine hxnot (Finset.mem_filter.mpr ⟨hxS, lt_of_le_of_ne (hw x hxS) (Ne.symm h)⟩)
  have hsum' : (∑ i ∈ S', w i) = 1 := by
    have hconv : (∑ i ∈ S', w i) = ∑ i ∈ S, w i :=
      Finset.sum_subset hS'sub (fun x hxS hxnot => hzeros x hxS hxnot)
    rw [hconv, hsum]
  have hconvx : (∑ i ∈ S', w i * x i) = ∑ i ∈ S, w i * x i := by
    refine Finset.sum_subset hS'sub (fun x hxS hxnot => ?_)
    rw [hzeros x hxS hxnot]
    ring
  have hconvbin : (∑ i ∈ S, w i * binEntropy (x i)) = ∑ i ∈ S', w i * binEntropy (x i) := by
    refine (Finset.sum_subset hS'sub (fun x hxS hxnot => ?_)).symm
    rw [hzeros x hxS hxnot]
    ring
  have hAB' : (∑ i ∈ S', w i * (1 - x i)) = 1 - ∑ i ∈ S', w i * x i := by
    have hsplit : (∑ i ∈ S', w i * (1 - x i)) = ∑ i ∈ S', (w i - w i * x i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hsplit, Finset.sum_sub_distrib, hsum']
  by_cases hAz : (∑ i ∈ S', w i * x i) = 0
  · have hx0 : ∀ i ∈ S', x i = 0 := by
      intro i hi
      have hz : w i * x i = 0 := by
        have hiff := Finset.sum_eq_zero_iff_of_nonneg (s := S')
          (fun j hj => mul_nonneg (hwS' j hj).le (hx j (hS'sub hj)))
        exact hiff.mp hAz i hi
      have hwi : w i ≠ 0 := ne_of_gt (hwS' i hi)
      exact (mul_eq_zero.mp hz).resolve_left hwi
    have hLsum : (∑ i ∈ S', w i * binEntropy (x i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hx0 i hi]
      simp [binEntropy]
    have hRsum : binEntropy (∑ i ∈ S, w i * x i) = 0 := by
      rw [← hconvx, hAz]
      simp [binEntropy]
    rw [hconvbin, hLsum, hRsum]
  by_cases hBz : (∑ i ∈ S', w i * (1 - x i)) = 0
  · have hx1 : ∀ i ∈ S', x i = 1 := by
      intro i hi
      have hz : w i * (1 - x i) = 0 := by
        have hiff := Finset.sum_eq_zero_iff_of_nonneg (s := S')
          (fun j hj => mul_nonneg (hwS' j hj).le (sub_nonneg.mpr (hx1 j (hS'sub hj))))
        exact hiff.mp hBz i hi
      have hwi : w i ≠ 0 := ne_of_gt (hwS' i hi)
      have hz' : 1 - x i = 0 := (mul_eq_zero.mp hz).resolve_left hwi
      exact (sub_eq_zero.mp hz').symm
    have hLsum : (∑ i ∈ S', w i * binEntropy (x i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hx1 i hi]
      simp [binEntropy]
    have hRsum : binEntropy (∑ i ∈ S, w i * x i) = 0 := by
      rw [← hconvx]
      have hAx : (∑ i ∈ S', w i * x i) = 1 := by
        calc (∑ i ∈ S', w i * x i) = ∑ i ∈ S', w i * 1 := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [hx1 i hi]
          _ = ∑ i ∈ S', w i := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
          _ = 1 := hsum'
      rw [hAx]
      simp [binEntropy]
    rw [hconvbin, hLsum, hRsum]
  · have hApos : 0 < ∑ i ∈ S', w i * x i := lt_of_le_of_ne (by
      have : 0 ≤ ∑ i ∈ S', w i * x i := Finset.sum_nonneg fun i hi =>
        mul_nonneg (hwS' i hi).le (hx i (hS'sub hi))
      simpa using! this) (Ne.symm hAz)
    have hBpos : 0 < ∑ i ∈ S', w i * (1 - x i) := lt_of_le_of_ne (by
      have : 0 ≤ ∑ i ∈ S', w i * (1 - x i) := Finset.sum_nonneg fun i hi =>
        mul_nonneg (hwS' i hi).le (sub_nonneg.mpr (hx1 i (hS'sub hi)))
      simpa using! this) (Ne.symm hBz)
    have hineq1 := log_sum_ineq S' (fun i => w i * x i) (fun i => w i)
      (fun i hi => mul_nonneg (hwS' i hi).le (hx i (hS'sub hi)))
      (fun i hi => hwS' i hi) hApos
    have hineq2 := log_sum_ineq S' (fun i => w i * (1 - x i)) (fun i => w i)
      (fun i hi => mul_nonneg (hwS' i hi).le (sub_nonneg.mpr (hx1 i (hS'sub hi))))
      (fun i hi => hwS' i hi) hBpos
    have hrw1 : (∑ i ∈ S', (w i * x i) * Real.log ((w i * x i) / w i))
        = ∑ i ∈ S', w i * x i * Real.log (x i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hwi : w i ≠ 0 := ne_of_gt (hwS' i hi)
      have hdiv : (w i * x i) / w i = x i := by field_simp
      rw [hdiv]
    have hrw2 : (∑ i ∈ S', (w i * (1 - x i)) * Real.log ((w i * (1 - x i)) / w i))
        = ∑ i ∈ S', w i * (1 - x i) * Real.log (1 - x i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hwi : w i ≠ 0 := ne_of_gt (hwS' i hi)
      have hdiv : (w i * (1 - x i)) / w i = 1 - x i := by field_simp
      rw [hdiv]
    have h1 : (∑ i ∈ S', w i * x i * Real.log (x i))
        ≥ (∑ i ∈ S', w i * x i) * Real.log (∑ i ∈ S', w i * x i) := by
      have hx := hineq1
      rw [hrw1] at hx
      have h1' : (∑ i ∈ S', (fun i => w i * x i) i) = ∑ i ∈ S', w i * x i := rfl
      have h2' : (∑ i ∈ S', (fun i => w i) i) = ∑ i ∈ S', w i := rfl
      rw [h1', h2', hsum', div_one] at hx
      exact hx
    have h2 : (∑ i ∈ S', w i * (1 - x i) * Real.log (1 - x i))
        ≥ (∑ i ∈ S', w i * (1 - x i)) * Real.log (∑ i ∈ S', w i * (1 - x i)) := by
      have hx := hineq2
      rw [hrw2] at hx
      have h1' : (∑ i ∈ S', (fun i => w i * (1 - x i)) i) = ∑ i ∈ S', w i * (1 - x i) := rfl
      have h2' : (∑ i ∈ S', (fun i => w i) i) = ∑ i ∈ S', w i := rfl
      rw [h1', h2', hsum', div_one] at hx
      exact hx

    have hcore : -(∑ i ∈ S', w i * x i * Real.log (x i))
        - (∑ i ∈ S', w i * (1 - x i) * Real.log (1 - x i))
        ≤ -((∑ i ∈ S', w i * x i) * Real.log (∑ i ∈ S', w i * x i))
          + -((∑ i ∈ S', w i * (1 - x i)) * Real.log (∑ i ∈ S', w i * (1 - x i))) := by
      have e1 := neg_le_neg h1.le
      have e2 := neg_le_neg h2.le
      have hsum := add_le_add e1 e2
      rw [← sub_eq_add_neg] at hsum
      exact hsum
    have hmul := mul_le_mul_of_nonneg_right hcore hlog2pos.le

    have hsumL : (∑ i ∈ S', w i * binEntropy (x i)) * Real.log 2
        = -(∑ i ∈ S', w i * x i * Real.log (x i))
          - (∑ i ∈ S', w i * (1 - x i) * Real.log (1 - x i)) := by
      calc (∑ i ∈ S', w i * binEntropy (x i)) * Real.log 2
          = ∑ i ∈ S', (w i * binEntropy (x i)) * Real.log 2 := by
            rw [Finset.sum_mul]
        _ = ∑ i ∈ S', w i * (-(x i * Real.log (x i) + (1 - x i) * Real.log (1 - x i))) := by
            apply Finset.sum_congr rfl
            intro i hi
            calc w i * binEntropy (x i) * Real.log 2
                = w i * (binEntropy (x i) * Real.log 2) := by ring
              _ = w i * (-(x i * Real.log (x i) + (1 - x i) * Real.log (1 - x i))) := by
                  rw [hL]
        _ = -(∑ i ∈ S', w i * (x i * Real.log (x i) + (1 - x i) * Real.log (1 - x i))) := by
            have hneg : ∀ i ∈ S',
                w i * (-(x i * Real.log (x i) + (1 - x i) * Real.log (1 - x i)))
                  = -(w i * (x i * Real.log (x i) + (1 - x i) * Real.log (1 - x i))) := by
              intro i hi
              ring
            rw [Finset.sum_congr rfl hneg, Finset.sum_neg_distrib]
        _ = -(∑ i ∈ S', w i * x i * Real.log (x i))
            - (∑ i ∈ S', w i * (1 - x i) * Real.log (1 - x i)) := by
            have hsplit : (∑ i ∈ S', w i * (x i * Real.log (x i) + (1 - x i) * Real.log (1 - x i)))
                = (∑ i ∈ S', w i * x i * Real.log (x i))
                  + (∑ i ∈ S', w i * (1 - x i) * Real.log (1 - x i)) := by
              have hstep : (∑ i ∈ S', w i * (x i * Real.log (x i) + (1 - x i) * Real.log (1 - x i)))
                  = ∑ i ∈ S', (w i * x i * Real.log (x i) + w i * (1 - x i) * Real.log (1 - x i)) := by
                apply Finset.sum_congr rfl
                intro i hi
                ring
              rw [hstep, Finset.sum_add_distrib]
            rw [hsplit]
            ring
    have hRA : binEntropy (∑ i ∈ S', w i * x i) * Real.log 2
        = -((∑ i ∈ S', w i * x i) * Real.log (∑ i ∈ S', w i * x i))
          + -((∑ i ∈ S', w i * (1 - x i)) * Real.log (∑ i ∈ S', w i * (1 - x i))) := by
      rw [hL, hAB']
      ring
    have hfinal : (∑ i ∈ S', w i * binEntropy (x i)) * Real.log 2
        ≤ binEntropy (∑ i ∈ S', w i * x i) * Real.log 2 := by
      rw [hsumL, hRA]
      exact hcore
    have hdiv : (∑ i ∈ S', w i * binEntropy (x i)) ≤ binEntropy (∑ i ∈ S', w i * x i) :=
      le_of_mul_le_mul_right hfinal hlog2pos
    rw [hconvbin]
    rw [← hconvx]
    exact hdiv

/-- Binary entropy is concave for two nonnegative weights summing to one and arguments in the
unit interval. -/
theorem binEntropy_mix_two (w₁ w₂ x y : ℝ)
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw : w₁ + w₂ = 1)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    w₁ * binEntropy x + w₂ * binEntropy y ≤
      binEntropy (w₁ * x + w₂ * y) := by
  classical
  have h := binEntropy_mix (Finset.univ : Finset Bool)
    (fun b => if b then w₂ else w₁) (fun b => if b then y else x)
    (fun b _ => by cases b <;> simp [hw₁, hw₂])
    (by rw [Fintype.sum_bool]; simp; ring_nf; linarith)
    (fun b _ => by cases b <;> simp [hy, hx])
    (fun b _ => by cases b <;> simp [hy1, hx1])
  rw [Fintype.sum_bool] at h
  simp at h
  have hkey : w₂ * y + w₁ * x = w₁ * x + w₂ * y := by ring
  rw [hkey] at h
  linarith [h]

/-- Every entry of a normalized nonnegative mass function is at most one. -/
theorem mass_le_one {n : ℕ} (a : Fin n → ℝ) (o : Fin n)
    (ha : ∀ j, 0 ≤ a j) (hsum : (∑ j, a j) = 1) : a o ≤ 1 := by
  have h1 : (∑ j, a j) = (∑ j ∈ (Finset.univ.erase o), a j) + a o := by
    symm
    exact Finset.sum_erase_add (Finset.univ : Finset (Fin n)) a (Finset.mem_univ o)
  rw [hsum] at h1
  have hpos : (0 : ℝ) ≤ ∑ j ∈ (Finset.univ.erase o), a j :=
    Finset.sum_nonneg fun j _ => ha j
  linarith

/-- For a normalized nonnegative distribution on at least two cells, entropy is at most
`binEntropy (1 - a o) + (1 - a o) * log₂ (n - 1)`. -/
theorem fano_leaf {n : ℕ} (hn : 2 ≤ n) (a : Fin n → ℝ) (o : Fin n)
    (ha : ∀ j, 0 ≤ a j) (hsum : (∑ j, a j) = 1) :
    entropy a ≤ binEntropy (1 - a o) + (1 - a o) * (Real.log (n - 1) / Real.log 2) := by
  classical
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have ho_le : a o ≤ 1 := mass_le_one a o ha hsum
  have ho_ge : 0 ≤ a o := ha o
  have hδ0 : (0 : ℝ) ≤ 1 - a o := by linarith
  by_cases hδ : a o = 1
  · have hrest : ∀ j, j ≠ o → a j = 0 := by
      intro j hj
      have h1 : (∑ k, a k) = (∑ k ∈ (Finset.univ.erase o), a k) + a o := by
        symm
        exact Finset.sum_erase_add (Finset.univ : Finset (Fin n)) a (Finset.mem_univ o)
      rw [hsum] at h1
      have hmem : j ∈ (Finset.univ.erase o : Finset (Fin n)) :=
        Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩
      have hsingle : a j ≤ ∑ k ∈ (Finset.univ.erase o), a k :=
        Finset.single_le_sum (f := a) (fun k _ => ha k) hmem
      have hpos : (0 : ℝ) ≤ ∑ k ∈ (Finset.univ.erase o), a k :=
        Finset.sum_nonneg fun k _ => ha k
      have haj : 0 ≤ a j := ha j
      linarith
    have hent : entropy a = 0 := by
      rw [entropy_eq_neg_slog]
      have h1 : (∑ j, a j * Real.log (a j))
          = (∑ j ∈ (Finset.univ.erase o), a j * Real.log (a j)) + a o * Real.log (a o) := by
        symm
        exact Finset.sum_erase_add (Finset.univ : Finset (Fin n))
          (fun j => a j * Real.log (a j)) (Finset.mem_univ o)
      rw [h1]
      have hz : (∑ j ∈ (Finset.univ.erase o), a j * Real.log (a j)) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [hrest j (Finset.mem_erase.mp hj).1]
        simp
      rw [hz, hδ]
      simp
    have hR : binEntropy (1 - a o) + (1 - a o) * (Real.log (n - 1) / Real.log 2) = 0 := by
      rw [show (1 - a o) = 0 by linarith]
      simp [binEntropy]
    rw [hent]
    exact hR.ge
  · have ho_lt : a o < 1 := by
      by_contra h
      have : a o = 1 := le_antisymm ho_le (le_of_not_gt h)
      exact hδ this
    have hδpos : (0 : ℝ) < 1 - a o := by linarith

    set b : Fin n → ℝ := fun j => if j = o then 0 else a j / (1 - a o) with hbdef
    have hb_o : b o = 0 := by simp [hbdef]
    have hb_nonneg : ∀ j, 0 ≤ b j := by
      intro j
      by_cases hj : j = o
      · have hb : b j = 0 := by rw [hbdef]; change (if j = o then 0 else a j / (1 - a o)) = 0; rw [if_pos hj]
        rw [hb]
      · have hb : b j = a j / (1 - a o) := by
          rw [hbdef]; change (if j = o then 0 else a j / (1 - a o)) = a j / (1 - a o); rw
              [if_neg hj]
        rw [hb]
        exact div_nonneg (ha j) (le_of_lt hδpos)
    have hb_sum : (∑ j, b j) = 1 := by
      have h1 : (∑ j, b j) = (∑ j ∈ (Finset.univ.erase o), b j) + b o := by
        symm
        exact Finset.sum_erase_add (Finset.univ : Finset (Fin n)) b (Finset.mem_univ o)
      rw [hb_o] at h1
      have h2 : (∑ j ∈ (Finset.univ.erase o), b j)
          = (1 / (1 - a o)) * (∑ j ∈ (Finset.univ.erase o), a j) := by
        calc (∑ j ∈ (Finset.univ.erase o), b j)
            = ∑ j ∈ (Finset.univ.erase o), (a j * (1 / (1 - a o))) := by
              apply Finset.sum_congr rfl
              intro j hj
              have hjo : j ≠ o := (Finset.mem_erase.mp hj).1
              have hb : b j = a j * (1 / (1 - a o)) := by
                rw [hbdef]
                change (if j = o then 0 else a j / (1 - a o)) = a j * (1 / (1 - a o))
                rw [if_neg hjo]
                ring
              rw [hb]
          _ = (1 / (1 - a o)) * (∑ j ∈ (Finset.univ.erase o), a j) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
      rw [h2] at h1
      have h3 : (∑ j ∈ (Finset.univ.erase o), a j) = 1 - a o := by
        have h4 : (∑ j, a j) = (∑ j ∈ (Finset.univ.erase o), a j) + a o := by
          symm
          exact Finset.sum_erase_add (Finset.univ : Finset (Fin n)) a (Finset.mem_univ o)
        rw [hsum] at h4
        linarith
      rw [h3] at h1
      have hone : 1 / (1 - a o) * (1 - a o) + 0 = 1 := by
        rw [one_div, inv_mul_cancel₀ (ne_of_gt hδpos), add_zero]
      rw [hone] at h1
      exact h1

    have hkey (j : Fin n) (hj : j ∈ (Finset.univ.erase o)) :
        a j * Real.log (a j)
          = (1 - a o) * b j * Real.log (1 - a o) + (1 - a o) * b j * Real.log (b j) := by
      have hjo : j ≠ o := (Finset.mem_erase.mp hj).1
      have haj : a j = (1 - a o) * b j := by
        rw [hbdef]
        change a j = (1 - a o) * (if j = o then 0 else a j / (1 - a o))
        rw [if_neg hjo]
        field_simp
      rw [haj]
      by_cases hb0 : b j = 0
      · rw [hb0]
        simp
      · have hbpos : 0 < b j := lt_of_le_of_ne (hb_nonneg j) (Ne.symm hb0)
        rw [Real.log_mul (by positivity) (by positivity)]
        ring
    have hchain : (∑ j, a j * Real.log (a j))
        = a o * Real.log (a o) + (1 - a o) * Real.log (1 - a o)
          + (1 - a o) * (∑ j, b j * Real.log (b j)) := by
      have h1 : (∑ j, a j * Real.log (a j))
          = (∑ j ∈ (Finset.univ.erase o), a j * Real.log (a j)) + a o * Real.log (a o) := by
        symm
        exact Finset.sum_erase_add (Finset.univ : Finset (Fin n))
          (fun j => a j * Real.log (a j)) (Finset.mem_univ o)
      have h2 : (∑ j ∈ (Finset.univ.erase o), a j * Real.log (a j))
          = (1 - a o) * Real.log (1 - a o) * (∑ j ∈ (Finset.univ.erase o), b j)
            + (1 - a o) * (∑ j ∈ (Finset.univ.erase o), b j * Real.log (b j)) := by
        calc (∑ j ∈ (Finset.univ.erase o), a j * Real.log (a j))
            = ∑ j ∈ (Finset.univ.erase o),
                ((1 - a o) * Real.log (1 - a o) * b j + (1 - a o) * (b j * Real.log (b j))) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  rw [hkey j hj]
                  ring
            _ = (1 - a o) * Real.log (1 - a o) * (∑ j ∈ (Finset.univ.erase o), b j)
                + (1 - a o) * (∑ j ∈ (Finset.univ.erase o), b j * Real.log (b j)) := by
                  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      have h3 : (∑ j ∈ (Finset.univ.erase o), b j) = 1 := by
        have hb1 : (∑ j, b j) = (∑ j ∈ (Finset.univ.erase o), b j) + b o := by
          symm
          exact Finset.sum_erase_add (Finset.univ : Finset (Fin n)) b (Finset.mem_univ o)
        rw [hb_o, hb_sum] at hb1
        linarith
      have h4 : (∑ j ∈ (Finset.univ.erase o), b j * Real.log (b j))
          = ∑ j, b j * Real.log (b j) := by
        have hb1 : (∑ j, b j * Real.log (b j))
            = (∑ j ∈ (Finset.univ.erase o), b j * Real.log (b j)) + b o * Real.log (b o) := by
          symm
          exact Finset.sum_erase_add (Finset.univ : Finset (Fin n))
            (fun j => b j * Real.log (b j)) (Finset.mem_univ o)
        rw [hb_o, zero_mul, add_zero] at hb1
        exact hb1.symm
      rw [h1, h2, h3, h4]
      ring

    have hmax : entropy b ≤ Real.log (n - 1) / Real.log 2 := by
      have hcard : 0 < (Finset.univ.erase o : Finset (Fin n)).card := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ o), Finset.card_fin]
        have : (2 : ℕ) ≤ n := hn
        omega
      have hsumS : (∑ j ∈ (Finset.univ.erase o), b j) = 1 := by
        have hb1 : (∑ j, b j) = (∑ j ∈ (Finset.univ.erase o), b j) + b o := by
          symm
          exact Finset.sum_erase_add (Finset.univ : Finset (Fin n)) b (Finset.mem_univ o)
        rw [hb_o, hb_sum] at hb1
        linarith
      have hlog : (∑ j, b j * Real.log (b j)) = ∑ j ∈ (Finset.univ.erase o), b j * Real.log (b j) := by
        have hb1 : (∑ j, b j * Real.log (b j))
            = (∑ j ∈ (Finset.univ.erase o), b j * Real.log (b j)) + b o * Real.log (b o) := by
          symm
          exact Finset.sum_erase_add (Finset.univ : Finset (Fin n))
            (fun j => b j * Real.log (b j)) (Finset.mem_univ o)
        rw [hb_o, zero_mul, add_zero] at hb1
        exact hb1
      have hme := maxEntropy_log_le (Finset.univ.erase o : Finset (Fin n)) b
        (fun j _ => hb_nonneg j) hsumS hcard
      have hcardval : (Finset.univ.erase o : Finset (Fin n)).card = n - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ o), Finset.card_fin]
      rw [← hlog] at hme
      have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      have hraw : -(∑ j, b j * Real.log (b j)) ≤ Real.log ((n : ℝ) - 1) := by
        have hx := hme
        rw [hcardval, hcast] at hx
        exact hx
      have hdiv : -(∑ j, b j * Real.log (b j)) / Real.log 2
          ≤ Real.log ((n : ℝ) - 1) / Real.log 2 := by
        apply (div_le_div_iff₀ hlog2pos hlog2pos).2
        exact mul_le_mul_of_nonneg_right hraw hlog2pos.le
      calc entropy b = -(∑ j, b j * Real.log (b j)) / Real.log 2 := entropy_eq_neg_slog b
        _ ≤ Real.log ((n : ℝ) - 1) / Real.log 2 := hdiv

    have hchain' : entropy a = binEntropy (1 - a o) + (1 - a o) * entropy b := by
      rw [entropy_eq_neg_slog, entropy_eq_neg_slog]
      have hebin : binEntropy (1 - a o)
          = -((1 - a o) * Real.log (1 - a o) + a o * Real.log (a o)) / Real.log 2 := by
        rw [binEntropy]
        have hone2 : (1 - (1 - a o)) = a o := by ring
        rw [hone2]
        field_simp
      rw [hebin]
      rw [hchain]
      ring
    rw [hchain']
    have hmul : (1 - a o) * entropy b ≤ (1 - a o) * (Real.log (n - 1) / Real.log 2) :=
      mul_le_mul_of_nonneg_left hmax hδ0
    linarith

/-- For a normalized nonnegative prior and `1 / 2 < p < 1`, the tree-leaf functional of the
constant one equals the initial weight. -/
theorem treeLeaf_weight_total {n : ℕ} (p : ℝ) (tr : BoolQueryTree (Fin n) (Fin n))
    (a : Fin n → ℝ) (W : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hsum : (∑ j, a j) = 1)
    (hp : 1 / 2 < p) (hp1 : p < 1) :
    treeLeaf p (fun _ _ => 1) tr a W = W := by
  induction tr generalizing a W with
  | halt o => simp [treeLeaf]
  | ask c onFalse onTrue ihFalse ihTrue =>
      simp only [treeLeaf]
      obtain ⟨hF, hT, hcomp⟩ :=
        bayes_answer_probabilities a c p ha hsum (show 0 < p by linarith) hp1
      have haF : ∀ j, 0 ≤ bayesFalsePost a c p j :=
        bayesFalsePost_nonneg a c p ha (show 0 ≤ p by linarith) hp1.le
      have haT : ∀ j, 0 ≤ bayesTruePost a c p j :=
        bayesTruePost_nonneg a c p ha (show 0 ≤ p by linarith) hp1.le
      have hsF : (∑ j, bayesFalsePost a c p j) = 1 :=
        bayesFalsePost_sum a c p ha hsum (show 0 < p by linarith) hp1
      have hsT : (∑ j, bayesTruePost a c p j) = 1 :=
        bayesTruePost_sum a c p ha hsum (show 0 < p by linarith) hp1
      rw [ihFalse (bayesFalsePost a c p) (W * bayesFalseNorm a c p) haF hsF,
        ihTrue (bayesTruePost a c p) (W * bayesTrueNorm a c p) haT hsT]
      calc W * bayesFalseNorm a c p + W * bayesTrueNorm a c p
          = W * (bayesFalseNorm a c p + bayesTrueNorm a c p) := by ring
        _ = W := by rw [hcomp]; ring

/-- With normalized nonnegative prior and nonnegative initial weight, the tree-leaf error
functional lies between zero and that weight when `1 / 2 < p < 1`. -/
theorem treeLeaf_err_bounds {n : ℕ} (p : ℝ) (tr : BoolQueryTree (Fin n) (Fin n))
    (a : Fin n → ℝ) (W : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hsum : (∑ j, a j) = 1)
    (hp : 1 / 2 < p) (hp1 : p < 1) (hW : 0 ≤ W) :
    0 ≤ treeLeaf p (fun a o => 1 - a o) tr a W ∧
      treeLeaf p (fun a o => 1 - a o) tr a W ≤ W := by
  induction tr generalizing a W with
  | halt o =>
      rw [treeLeaf]
      have ho_le : a o ≤ 1 := mass_le_one a o ha hsum
      have ho_ge : 0 ≤ a o := ha o
      constructor
      · have : 0 ≤ 1 - a o := by linarith
        nlinarith
      · have : 1 - a o ≤ 1 := by linarith
        nlinarith
  | ask c onFalse onTrue ihFalse ihTrue =>
      simp only [treeLeaf]
      obtain ⟨hF, hT, hcomp⟩ :=
        bayes_answer_probabilities a c p ha hsum (show 0 < p by linarith) hp1
      have haF : ∀ j, 0 ≤ bayesFalsePost a c p j :=
        bayesFalsePost_nonneg a c p ha (show 0 ≤ p by linarith) hp1.le
      have haT : ∀ j, 0 ≤ bayesTruePost a c p j :=
        bayesTruePost_nonneg a c p ha (show 0 ≤ p by linarith) hp1.le
      have hsF : (∑ j, bayesFalsePost a c p j) = 1 :=
        bayesFalsePost_sum a c p ha hsum (show 0 < p by linarith) hp1
      have hsT : (∑ j, bayesTruePost a c p j) = 1 :=
        bayesTruePost_sum a c p ha hsum (show 0 < p by linarith) hp1
      have hWF : 0 ≤ W * bayesFalseNorm a c p := mul_nonneg hW hF.le
      have hWT : 0 ≤ W * bayesTrueNorm a c p := mul_nonneg hW hT.le
      have h1 := ihFalse (bayesFalsePost a c p) (W * bayesFalseNorm a c p) haF hsF hWF
      have h2 := ihTrue (bayesTruePost a c p) (W * bayesTrueNorm a c p) haT hsT hWT
      constructor
      · linarith [h1.1, h2.1]
      · have hsumW : W * bayesFalseNorm a c p + W * bayesTrueNorm a c p = W := by
          calc W * bayesFalseNorm a c p + W * bayesTrueNorm a c p
              = W * (bayesFalseNorm a c p + bayesTrueNorm a c p) := by ring
            _ = W := by rw [hcomp]; ring
        linarith [h1.2, h2.2, hsumW]

/-- Multiplying the stated binary-entropy mixture inequality by positive `W` gives the
corresponding inequality with combined argument `(x + y) / W`. -/
theorem mix_step {w₁ w₂ x y W : ℝ}
    (hw₁ne : w₁ ≠ 0) (hw₂ne : w₂ ≠ 0) (hW : 0 < W)
    (hmix : w₁ * binEntropy (x / (W * w₁)) + w₂ * binEntropy (y / (W * w₂))
      ≤ binEntropy (w₁ * (x / (W * w₁)) + w₂ * (y / (W * w₂)))) :
    (W * w₁) * binEntropy (x / (W * w₁)) + (W * w₂) * binEntropy (y / (W * w₂))
      ≤ W * binEntropy ((x + y) / W) := by
  have hkey : w₁ * (x / (W * w₁)) + w₂ * (y / (W * w₂)) = (x + y) / W := by
    field_simp
  have hA := mul_le_mul_of_nonneg_left hmix (le_of_lt hW)
  calc (W * w₁) * binEntropy (x / (W * w₁)) + (W * w₂) * binEntropy (y / (W * w₂))
      = W * (w₁ * binEntropy (x / (W * w₁)) + w₂ * binEntropy (y / (W * w₂))) := by ring
    _ ≤ W * binEntropy (w₁ * (x / (W * w₁)) + w₂ * (y / (W * w₂))) := hA
    _ = W * binEntropy ((x + y) / W) := by rw [hkey]

/-- The weighted leaf entropy is bounded by the Fano expression formed from total leaf error and
initial weight for `n ≥ 2` and `1 / 2 < p < 1`. -/
theorem tree_fano_numerator {n : ℕ} (p : ℝ) (tr : BoolQueryTree (Fin n) (Fin n))
    (a : Fin n → ℝ) (W : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hsum : (∑ j, a j) = 1)
    (hp : 1 / 2 < p) (hp1 : p < 1) (hW : 0 < W) (hn : 2 ≤ n) :
    treeLeaf p (fun a o => entropy a) tr a W
      ≤ W * binEntropy (treeLeaf p (fun a o => 1 - a o) tr a W / W)
        + treeLeaf p (fun a o => 1 - a o) tr a W * (Real.log (n - 1) / Real.log 2) := by
  induction tr generalizing a W with
  | halt o =>
      simp only [treeLeaf]
      have hfa := fano_leaf hn a o ha hsum
      have hdiv : (W * (1 - a o)) / W = 1 - a o := by field_simp
      rw [hdiv]
      have hmul : W * entropy a
          ≤ W * binEntropy (1 - a o) + (W * (1 - a o)) * (Real.log (n - 1) / Real.log 2) := by
        have hx := mul_le_mul_of_nonneg_left hfa hW.le
        convert! hx using 1 <;> ring
      exact hmul
  | ask c onFalse onTrue ihFalse ihTrue =>
      simp only [treeLeaf]
      obtain ⟨hF, hT, hcomp⟩ :=
        bayes_answer_probabilities a c p ha hsum (show 0 < p by linarith) hp1
      have haF : ∀ j, 0 ≤ bayesFalsePost a c p j :=
        bayesFalsePost_nonneg a c p ha (show 0 ≤ p by linarith) hp1.le
      have haT : ∀ j, 0 ≤ bayesTruePost a c p j :=
        bayesTruePost_nonneg a c p ha (show 0 ≤ p by linarith) hp1.le
      have hsF : (∑ j, bayesFalsePost a c p j) = 1 :=
        bayesFalsePost_sum a c p ha hsum (show 0 < p by linarith) hp1
      have hsT : (∑ j, bayesTruePost a c p j) = 1 :=
        bayesTruePost_sum a c p ha hsum (show 0 < p by linarith) hp1
      have hWF : 0 < W * bayesFalseNorm a c p := mul_pos hW hF
      have hWT : 0 < W * bayesTrueNorm a c p := mul_pos hW hT
      have h1 := ihFalse (bayesFalsePost a c p) (W * bayesFalseNorm a c p) haF hsF hWF
      have h2 := ihTrue (bayesTruePost a c p) (W * bayesTrueNorm a c p) haT hsT hWT
      have h1b := treeLeaf_err_bounds p onFalse (bayesFalsePost a c p) (W * bayesFalseNorm a c p)
        haF hsF hp hp1 (le_of_lt hWF)
      have h2b := treeLeaf_err_bounds p onTrue (bayesTruePost a c p) (W * bayesTrueNorm a c p)
        haT hsT hp hp1 (le_of_lt hWT)
      let x : ℝ := treeLeaf p (fun a o => 1 - a o) onFalse (bayesFalsePost a c p)
        (W * bayesFalseNorm a c p)
      let y : ℝ := treeLeaf p (fun a o => 1 - a o) onTrue (bayesTruePost a c p)
        (W * bayesTrueNorm a c p)
      have hx0 : 0 ≤ x := by simpa only [x] using! h1b.1
      have hx1 : x ≤ W * bayesFalseNorm a c p := by simpa only [x] using! h1b.2
      have hy0 : 0 ≤ y := by simpa only [y] using! h2b.1
      have hy1 : y ≤ W * bayesTrueNorm a c p := by simpa only [y] using! h2b.2
      have hxdiv0 : 0 ≤ x / (W * bayesFalseNorm a c p) := div_nonneg hx0 (le_of_lt hWF)
      have hxdiv1 : x / (W * bayesFalseNorm a c p) ≤ 1 := by
        rw [div_le_iff₀ hWF]
        linarith
      have hydiv0 : 0 ≤ y / (W * bayesTrueNorm a c p) := div_nonneg hy0 (le_of_lt hWT)
      have hydiv1 : y / (W * bayesTrueNorm a c p) ≤ 1 := by
        rw [div_le_iff₀ hWT]
        linarith
      have hmix := binEntropy_mix_two (bayesFalseNorm a c p) (bayesTrueNorm a c p)
        (x / (W * bayesFalseNorm a c p)) (y / (W * bayesTrueNorm a c p))
        hF.le hT.le hcomp hxdiv0 hxdiv1 hydiv0 hydiv1
      have hstep := mix_step (ne_of_gt hF) (ne_of_gt hT) hW hmix
      have h1' : treeLeaf p (fun a o => entropy a) onFalse (bayesFalsePost a c p)
          (W * bayesFalseNorm a c p)
          ≤ (W * bayesFalseNorm a c p) * binEntropy (x / (W * bayesFalseNorm a c p))
            + x * (Real.log (n - 1) / Real.log 2) := by
        simpa only [x] using! h1
      have h2' : treeLeaf p (fun a o => entropy a) onTrue (bayesTruePost a c p)
          (W * bayesTrueNorm a c p)
          ≤ (W * bayesTrueNorm a c p) * binEntropy (y / (W * bayesTrueNorm a c p))
            + y * (Real.log (n - 1) / Real.log 2) := by
        simpa only [y] using! h2
      calc treeLeaf p (fun a o => entropy a) onFalse (bayesFalsePost a c p)
              (W * bayesFalseNorm a c p)
            + treeLeaf p (fun a o => entropy a) onTrue (bayesTruePost a c p)
              (W * bayesTrueNorm a c p)
          ≤ (W * bayesFalseNorm a c p) * binEntropy (x / (W * bayesFalseNorm a c p))
            + x * (Real.log (n - 1) / Real.log 2)
            + ((W * bayesTrueNorm a c p) * binEntropy (y / (W * bayesTrueNorm a c p))
              + y * (Real.log (n - 1) / Real.log 2)) := add_le_add h1' h2'
        _ = (W * bayesFalseNorm a c p) * binEntropy (x / (W * bayesFalseNorm a c p))
            + (W * bayesTrueNorm a c p) * binEntropy (y / (W * bayesTrueNorm a c p))
            + (x + y) * (Real.log (n - 1) / Real.log 2) := by ring
        _ ≤ W * binEntropy ((x + y) / W) + (x + y) * (Real.log (n - 1) / Real.log 2) := by
          have hx := add_le_add_right hstep ((x + y) * (Real.log (n - 1) / Real.log 2))
          simpa only [add_comm] using! hx

/-- The entropy of the uniform posterior on `n > 0` cells is `log₂ n`. -/
theorem entropy_uniform {n : ℕ} (hn : 0 < n) :
    entropy (uniformPosterior (n := n)) = Real.log n / Real.log 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hstep : (∑ j, uniformPosterior (n := n) j * Real.log (uniformPosterior (n := n) j))
      = ↑n * ((1 / ↑n) * Real.log (1 / ↑n)) := by
    calc (∑ j, uniformPosterior (n := n) j * Real.log (uniformPosterior (n := n) j))
        = ∑ _j : Fin n, ((1 / ↑n) * Real.log (1 / ↑n)) := by
          apply Finset.sum_congr rfl
          intro j _
          simp [uniformPosterior]
        _ = ↑n * ((1 / ↑n) * Real.log (1 / ↑n)) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_fin]
  rw [entropy_eq_neg_slog, hstep]
  have hne : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hlog : Real.log (1 / ↑n) = -Real.log ↑n := by
    rw [Real.log_div (by norm_num) hne, Real.log_one, zero_sub]
  rw [hlog]
  have hlog2ne : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  field_simp <;> ring

/-- For a normalized nonnegative prior and `1 / 2 < p < 1`, tree information gain is leaf
information minus initial weighted information. -/
theorem treeInfo_eq_leafInfo {n : ℕ} (p : ℝ) (tr : BoolQueryTree (Fin n) (Fin n))
    (a : Fin n → ℝ) (W : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hsum : (∑ j, a j) = 1)
    (hp : 1 / 2 < p) (hp1 : p < 1) :
    treeInfo p tr a W = treeLeaf p (fun a _ => postInfo a) tr a W - W * postInfo a := by
  induction tr generalizing a W with
  | halt o =>
      simp [treeInfo, treeLeaf]
  | ask c onFalse onTrue ihFalse ihTrue =>
      rw [treeInfo, treeLeaf]
      obtain ⟨hF, hT, hcomp⟩ :=
        bayes_answer_probabilities a c p ha hsum (show 0 < p by linarith) hp1
      have haF : ∀ j, 0 ≤ bayesFalsePost a c p j :=
        bayesFalsePost_nonneg a c p ha (show 0 ≤ p by linarith) hp1.le
      have haT : ∀ j, 0 ≤ bayesTruePost a c p j :=
        bayesTruePost_nonneg a c p ha (show 0 ≤ p by linarith) hp1.le
      have hsF : (∑ j, bayesFalsePost a c p j) = 1 :=
        bayesFalsePost_sum a c p ha hsum (show 0 < p by linarith) hp1
      have hsT : (∑ j, bayesTruePost a c p j) = 1 :=
        bayesTruePost_sum a c p ha hsum (show 0 < p by linarith) hp1
      have h1 := ihFalse (bayesFalsePost a c p) (W * bayesFalseNorm a c p) haF hsF
      have h2 := ihTrue (bayesTruePost a c p) (W * bayesTrueNorm a c p) haT hsT
      have hkey : W * bayesFalseNorm a c p
            * (postInfo (bayesFalsePost a c p) - postInfo a)
          + W * bayesTrueNorm a c p
            * (postInfo (bayesTruePost a c p) - postInfo a)
          = W * bayesFalseNorm a c p * postInfo (bayesFalsePost a c p)
            + W * bayesTrueNorm a c p * postInfo (bayesTruePost a c p)
            - W * postInfo a := by
        calc W * bayesFalseNorm a c p * (postInfo (bayesFalsePost a c p) - postInfo a)
            + W * bayesTrueNorm a c p * (postInfo (bayesTruePost a c p) - postInfo a)
            = W * (bayesFalseNorm a c p * postInfo (bayesFalsePost a c p)
                + bayesTrueNorm a c p * postInfo (bayesTruePost a c p)
                - (bayesFalseNorm a c p + bayesTrueNorm a c p) * postInfo a) := by ring
          _ = W * (bayesFalseNorm a c p * postInfo (bayesFalsePost a c p)
                + bayesTrueNorm a c p * postInfo (bayesTruePost a c p) - postInfo a) := by
                rw [hcomp]
                ring
          _ = W * bayesFalseNorm a c p * postInfo (bayesFalsePost a c p)
              + W * bayesTrueNorm a c p * postInfo (bayesTruePost a c p)
              - W * postInfo a := by ring
      rw [h1, h2, hkey]
      ring

/-- For `n ≥ 2` and `1 / 2 < p < 1`, the uniform posterior entropy is bounded by the Fano
expression in the uniform error probability. -/
theorem fano_numerator_uniform {n : ℕ} (p : ℝ) (tr : BoolQueryTree (Fin n) (Fin n))
    (hp : 1 / 2 < p) (hp1 : p < 1) (hn : 2 ≤ n) :
    uniformPosteriorEntropy p tr
      ≤ binEntropy (uniformErrorProb p tr)
        + uniformErrorProb p tr * (Real.log (n - 1) / Real.log 2) := by
  have ha : ∀ j : Fin n, 0 ≤ uniformPosterior (n := n) j := by
    intro j
    simp [uniformPosterior]
  have hsum : (∑ j, uniformPosterior (n := n) j) = 1 := uniform_sum (by omega)
  have h := tree_fano_numerator p tr (uniformPosterior (n := n)) 1 ha hsum hp hp1 (by norm_num) hn

  simpa using! h

/-- Pointwise equal leaf functionals give equal tree-leaf evaluations. -/
theorem treeLeaf_congr {n : ℕ} (p : ℝ) (tr : BoolQueryTree (Fin n) (Fin n))
    (f g : (Fin n → ℝ) → Fin n → ℝ) (a : Fin n → ℝ) (W : ℝ)
    (h : ∀ (post : Fin n → ℝ) (o : Fin n), f post o = g post o) :
    treeLeaf p f tr a W = treeLeaf p g tr a W := by
  induction tr generalizing a W with
  | halt o => simp [treeLeaf, h]
  | ask c onFalse onTrue ihFalse ihTrue =>
      simp only [treeLeaf]
      rw [ihFalse (bayesFalsePost a c p) (W * bayesFalseNorm a c p),
        ihTrue (bayesTruePost a c p) (W * bayesTrueNorm a c p)]

/-- For a normalized nonnegative prior and `1 / 2 < p < 1`, the leaf functional of `cc - f` is
`cc * W` minus the leaf functional of `f`. -/
theorem treeLeaf_sub_const {n : ℕ} (p : ℝ) (tr : BoolQueryTree (Fin n) (Fin n))
    (cc : ℝ) (f : (Fin n → ℝ) → Fin n → ℝ) (a : Fin n → ℝ) (W : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hsum : (∑ j, a j) = 1)
    (hp : 1 / 2 < p) (hp1 : p < 1) :
    treeLeaf p (fun post o => cc - f post o) tr a W
      = cc * W - treeLeaf p f tr a W := by
  induction tr generalizing a W with
  | halt o =>
      simp [treeLeaf]
      ring
  | ask c onFalse onTrue ihFalse ihTrue =>
      obtain ⟨hF, hT, hcomp⟩ :=
        bayes_answer_probabilities a c p ha hsum (show 0 < p by linarith) hp1
      have haF : ∀ j, 0 ≤ bayesFalsePost a c p j :=
        bayesFalsePost_nonneg a c p ha (show 0 ≤ p by linarith) hp1.le
      have haT : ∀ j, 0 ≤ bayesTruePost a c p j :=
        bayesTruePost_nonneg a c p ha (show 0 ≤ p by linarith) hp1.le
      have hsF : (∑ j, bayesFalsePost a c p j) = 1 :=
        bayesFalsePost_sum a c p ha hsum (show 0 < p by linarith) hp1
      have hsT : (∑ j, bayesTruePost a c p j) = 1 :=
        bayesTruePost_sum a c p ha hsum (show 0 < p by linarith) hp1
      calc treeLeaf p (fun post o => cc - f post o) (.ask c onFalse onTrue) a W
          = (cc * (W * bayesFalseNorm a c p)
              - treeLeaf p f onFalse (bayesFalsePost a c p) (W * bayesFalseNorm a c p))
            + (cc * (W * bayesTrueNorm a c p)
              - treeLeaf p f onTrue (bayesTruePost a c p) (W * bayesTrueNorm a c p)) := by
              simp only [treeLeaf]
              rw [ihFalse (bayesFalsePost a c p) (W * bayesFalseNorm a c p) haF hsF,
                ihTrue (bayesTruePost a c p) (W * bayesTrueNorm a c p) haT hsT]
        _ = cc * W - (treeLeaf p f onFalse (bayesFalsePost a c p) (W * bayesFalseNorm a c p)
            + treeLeaf p f onTrue (bayesTruePost a c p) (W * bayesTrueNorm a c p)) := by
              have hsumW : W * bayesFalseNorm a c p + W * bayesTrueNorm a c p = W := by
                calc W * bayesFalseNorm a c p + W * bayesTrueNorm a c p
                    = W * (bayesFalseNorm a c p + bayesTrueNorm a c p) := by ring
                  _ = W * 1 := by rw [hcomp]
                  _ = W := by ring
              calc cc * (W * bayesFalseNorm a c p) - treeLeaf p f onFalse (bayesFalsePost a c p)
                    (W * bayesFalseNorm a c p)
                  + (cc * (W * bayesTrueNorm a c p) - treeLeaf p f onTrue (bayesTruePost a c p)
                    (W * bayesTrueNorm a c p))
                  = (cc * (W * bayesFalseNorm a c p) + cc * (W * bayesTrueNorm a c p))
                    - (treeLeaf p f onFalse (bayesFalsePost a c p) (W * bayesFalseNorm a c p)
                      + treeLeaf p f onTrue (bayesTruePost a c p) (W * bayesTrueNorm a c p)) := by ring
                _ = cc * W - (treeLeaf p f onFalse (bayesFalsePost a c p) (W * bayesFalseNorm a c p)
                    + treeLeaf p f onTrue (bayesTruePost a c p) (W * bayesTrueNorm a c p)) := by
                  have hkey : cc * (W * bayesFalseNorm a c p) + cc * (W * bayesTrueNorm a c p) = cc * W := by
                    calc cc * (W * bayesFalseNorm a c p) + cc * (W * bayesTrueNorm a c p)
                        = cc * (W * bayesFalseNorm a c p + W * bayesTrueNorm a c p) := by ring
                      _ = cc * W := by rw [hsumW]
                  rw [hkey]
        _ = cc * W - treeLeaf p f (.ask c onFalse onTrue) a W := by
              simp only [treeLeaf]

/-- For `n ≥ 2` and `1 / 2 < p < 1`, the Fano capacity expression evaluated at the uniform error
probability bounds uniform expected queries from below. -/
theorem fano_capacity_lower_bound {n : ℕ} (p : ℝ) (tr : BoolQueryTree (Fin n) (Fin n))
    (hp : 1 / 2 < p) (hp1 : p < 1) (hn : 2 ≤ n) :
    fanoCapacity (n := n) (uniformErrorProb p tr) p ≤ uniformExpectedQueries p tr := by
  have ha : ∀ j : Fin n, 0 ≤ uniformPosterior (n := n) j := by
    intro j
    simp [uniformPosterior]
  have hsum : (∑ j, uniformPosterior (n := n) j) = 1 := uniform_sum (by omega)

  have hchan := walkGoal_information_accounting p tr hp hp1 (by omega)

  have hnum := fano_numerator_uniform p tr hp hp1 hn

  have hinfo : treeInfo p tr (uniformPosterior (n := n)) 1 = uniformPosteriorInfo p tr := by
    rw [treeInfo_eq_leafInfo p tr (uniformPosterior (n := n)) 1 ha hsum hp hp1]
    have hpost : postInfo (uniformPosterior (n := n)) = 0 := by
      have hent := entropy_uniform (n := n) (by omega)
      rw [postInfo, hent]
      ring
    rw [hpost]
    ring_nf
    rfl

  have hleaf : uniformPosteriorInfo p tr = Real.log n / Real.log 2 - uniformPosteriorEntropy p tr := by
    have hpost : ∀ (post : Fin n → ℝ) (o : Fin n),
        postInfo post = Real.log n / Real.log 2 - entropy post := by
      intro post o
      rw [postInfo]
    have hcongr := treeLeaf_congr p tr (fun a _ => postInfo a)
      (fun a _ => (Real.log n / Real.log 2 - entropy a)) (uniformPosterior (n := n)) 1 hpost
    have hsub := treeLeaf_sub_const p tr (Real.log n / Real.log 2) (fun a _ => entropy a)
      (uniformPosterior (n := n)) 1 ha hsum hp hp1
    rw [uniformPosteriorInfo]
    rw [hcongr, hsub]
    simp only [uniformPosteriorEntropy]
    ring

  have hI : (0 : ℝ) < queryInfo p := queryInfo_pos hp hp1
  have hmain : Real.log n / Real.log 2 - binEntropy (uniformErrorProb p tr)
      - uniformErrorProb p tr * (Real.log (n - 1) / Real.log 2)
      ≤ queryInfo p * uniformExpectedQueries p tr := by
    have hleaf' : Real.log n / Real.log 2
        = uniformPosteriorInfo p tr + uniformPosteriorEntropy p tr := by
      linarith [hleaf]
    rw [hleaf']
    have h1 : uniformPosteriorInfo p tr ≤ queryInfo p * uniformExpectedQueries p tr := by
      rw [← hinfo]
      exact hchan
    have h2 : uniformPosteriorInfo p tr
        ≥ Real.log n / Real.log 2 - binEntropy (uniformErrorProb p tr)
          - uniformErrorProb p tr * (Real.log (n - 1) / Real.log 2) := by
      have hle : uniformPosteriorEntropy p tr
          ≤ binEntropy (uniformErrorProb p tr)
            + uniformErrorProb p tr * (Real.log (n - 1) / Real.log 2) := hnum
      linarith
    linarith

  have hcore : Real.log n / Real.log 2 - binEntropy (uniformErrorProb p tr)
      - uniformErrorProb p tr * (Real.log (n - 1) / Real.log 2)
      ≤ uniformExpectedQueries p tr * queryInfo p := by
    simpa [mul_comm] using! hmain
  have hdiv : (Real.log n / Real.log 2 - binEntropy (uniformErrorProb p tr)
      - uniformErrorProb p tr * (Real.log (n - 1) / Real.log 2)) / queryInfo p
      ≤ uniformExpectedQueries p tr := (div_le_iff₀ hI).2 hcore
  rw [← fanoCapacity] at hdiv
  exact hdiv

/-- Collects the leaf Fano inequality, its uniform-tree form, and the resulting capacity lower
bound on expected queries. -/
theorem walkGoal_capacity_endpoint :
    (∀ {n : ℕ} (hn : 2 ≤ n) (a : Fin n → ℝ) (o : Fin n),
      (∀ j, 0 ≤ a j) → (∑ j, a j = 1) →
      entropy a ≤ binEntropy (1 - a o) + (1 - a o) * (Real.log (n - 1) / Real.log 2)) ∧
    (∀ {n : ℕ} (p : ℝ) (tr : BoolQueryTree (Fin n) (Fin n)),
      (1 / 2 : ℝ) < p → p < 1 → 2 ≤ n →
      uniformPosteriorEntropy p tr
        ≤ binEntropy (uniformErrorProb p tr)
          + uniformErrorProb p tr * (Real.log (n - 1) / Real.log 2)) ∧
    (∀ {n : ℕ} (p : ℝ) (tr : BoolQueryTree (Fin n) (Fin n)),
      (1 / 2 : ℝ) < p → p < 1 → 2 ≤ n →
      fanoCapacity (n := n) (uniformErrorProb p tr) p ≤ uniformExpectedQueries p tr) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn a o ha hsum; exact fano_leaf hn a o ha hsum
  · intro n p tr hp hp1 hn; exact fano_numerator_uniform p tr hp hp1 hn
  · intro n p tr hp hp1 hn; exact fano_capacity_lower_bound p tr hp hp1 hn

/-- The false- and true-answer Bayesian normalizers sum to the total prior mass. -/
theorem norm_sum {n : ℕ} (a : Fin n → ℝ) (c : Fin n) (p : ℝ) :
    bayesFalseNorm a c p + bayesTrueNorm a c p = (∑ m, a m) := by
  have key : ∀ m : Fin n,
      a m * bayesFalseLikelihood c m p + a m * bayesTrueLikelihood c m p = a m := by
    intro m
    by_cases h : (c : ℕ) ≤ (m : ℕ)
    · simp [bayesFalseLikelihood, bayesTrueLikelihood, h]; ring
    · simp [bayesFalseLikelihood, bayesTrueLikelihood, h]; ring
  calc bayesFalseNorm a c p + bayesTrueNorm a c p
      = ∑ m, (a m * bayesFalseLikelihood c m p + a m * bayesTrueLikelihood c m p) := by
        unfold bayesFalseNorm bayesTrueNorm
        rw [Finset.sum_add_distrib]
    _ = ∑ m, a m := Finset.sum_congr rfl (fun m _ => key m)

/-- For a normalized nonnegative prior, nonnegative weight, and `0 < p < 1`, the deep-tree
weight is at most the initial weight. -/
theorem treeDeepProb_le {n : ℕ} (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∀ (tr : BoolQueryTree (Fin n) (Fin n)) (a : Fin n → ℝ) (W : ℝ),
      (∀ j, 0 ≤ a j) → (∑ j, a j) = 1 → 0 ≤ W →
      ∀ b : ℕ, treeDeepProb p b tr a W ≤ W := by
  intro tr
  induction tr with
  | halt o =>
    intro a W ha hsum hW b
    by_cases h : b = 0
    · simp only [treeDeepProb, h, ↓reduceIte]
      exact le_rfl
    · simp only [treeDeepProb, h, ↓reduceIte]
      exact hW
  | ask c onFalse onTrue ihF ihT =>
    intro a W ha hsum hW b
    by_cases h : b = 0
    · simp [treeDeepProb, h]
    · simp only [treeDeepProb, h, ↓reduceIte]
      have hnF : 0 ≤ bayesFalseNorm a c p := by
        unfold bayesFalseNorm
        exact Finset.sum_nonneg fun j _ => mul_nonneg (ha j) (by
          unfold bayesFalseLikelihood; split_ifs <;> linarith)
      have hnT : 0 ≤ bayesTrueNorm a c p := by
        unfold bayesTrueNorm
        exact Finset.sum_nonneg fun j _ => mul_nonneg (ha j) (by
          unfold bayesTrueLikelihood; split_ifs <;> linarith)
      have h1 := ihF (bayesFalsePost a c p) (W * bayesFalseNorm a c p)
        (fun j => bayesFalsePost_nonneg a c p ha (le_of_lt hp) (le_of_lt hp1) j)
        (bayesFalsePost_sum a c p ha hsum hp hp1)
        (mul_nonneg hW hnF)
        (b - 1)
      have h2 := ihT (bayesTruePost a c p) (W * bayesTrueNorm a c p)
        (fun j => bayesTruePost_nonneg a c p ha (le_of_lt hp) (le_of_lt hp1) j)
        (bayesTruePost_sum a c p ha hsum hp hp1)
        (mul_nonneg hW hnT)
        (b - 1)
      have hn := norm_sum a c p
      have hW1 : W * bayesFalseNorm a c p + W * bayesTrueNorm a c p = W := by
        calc W * bayesFalseNorm a c p + W * bayesTrueNorm a c p
            = W * (bayesFalseNorm a c p + bayesTrueNorm a c p) := by ring
          _ = W * (∑ m, a m) := by rw [hn]
          _ = W * 1 := by rw [hsum]
          _ = W := by ring
      linarith

/-- The weighted tree depth is nonnegative for a normalized nonnegative prior, nonnegative
weight, and `0 < p < 1`. -/
theorem treeDepth_nonneg {n : ℕ} (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∀ (tr : BoolQueryTree (Fin n) (Fin n)) (a : Fin n → ℝ) (W : ℝ),
      (∀ j, 0 ≤ a j) → (∑ j, a j) = 1 → 0 ≤ W → 0 ≤ treeDepth p tr a W := by
  intro tr
  induction tr with
  | halt o =>
    intro a W ha hsum hW
    simp [treeDepth]
  | ask c onFalse onTrue ihF ihT =>
    intro a W ha hsum hW
    simp only [treeDepth]
    have hnF : 0 ≤ bayesFalseNorm a c p := by
      unfold bayesFalseNorm
      exact Finset.sum_nonneg fun j _ => mul_nonneg (ha j) (by
        unfold bayesFalseLikelihood; split_ifs <;> linarith)
    have hnT : 0 ≤ bayesTrueNorm a c p := by
      unfold bayesTrueNorm
      exact Finset.sum_nonneg fun j _ => mul_nonneg (ha j) (by
        unfold bayesTrueLikelihood; split_ifs <;> linarith)
    have h1 := ihF (bayesFalsePost a c p) (W * bayesFalseNorm a c p)
      (fun j => bayesFalsePost_nonneg a c p ha (le_of_lt hp) (le_of_lt hp1) j)
      (bayesFalsePost_sum a c p ha hsum hp hp1)
      (mul_nonneg hW hnF)
    have h2 := ihT (bayesTruePost a c p) (W * bayesTrueNorm a c p)
      (fun j => bayesTruePost_nonneg a c p ha (le_of_lt hp) (le_of_lt hp1) j)
      (bayesTruePost_sum a c p ha hsum hp hp1)
      (mul_nonneg hW hnT)
    linarith

/-- For a normalized nonnegative prior and nonnegative weight, the depth threshold times the
deep-tree weight is at most weighted tree depth when `0 < p < 1`. -/
theorem treeDepth_markov {n : ℕ} (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∀ (tr : BoolQueryTree (Fin n) (Fin n)) (a : Fin n → ℝ) (W : ℝ),
      (∀ j, 0 ≤ a j) → (∑ j, a j) = 1 → 0 ≤ W →
      ∀ b : ℕ, (b : ℝ) * treeDeepProb p b tr a W ≤ treeDepth p tr a W := by
  intro tr
  induction tr with
  | halt o =>
    intro a W ha hsum hW b
    by_cases h : b = 0
    · simp [treeDeepProb, h, treeDepth]
    · simp [treeDeepProb, h, treeDepth]
  | ask c onFalse onTrue ihF ihT =>
    intro a W ha hsum hW b
    by_cases h : b = 0
    · simp only [treeDeepProb, h, ↓reduceIte, Nat.cast_zero, zero_mul]
      exact treeDepth_nonneg p hp hp1 (.ask c onFalse onTrue) a W ha hsum hW
    · simp only [treeDeepProb, h, ↓reduceIte]
      have hnF : 0 ≤ bayesFalseNorm a c p := by
        unfold bayesFalseNorm
        exact Finset.sum_nonneg fun j _ => mul_nonneg (ha j) (by
          unfold bayesFalseLikelihood; split_ifs <;> linarith)
      have hnT : 0 ≤ bayesTrueNorm a c p := by
        unfold bayesTrueNorm
        exact Finset.sum_nonneg fun j _ => mul_nonneg (ha j) (by
          unfold bayesTrueLikelihood; split_ifs <;> linarith)
      have h1 := ihF (bayesFalsePost a c p) (W * bayesFalseNorm a c p)
        (fun j => bayesFalsePost_nonneg a c p ha (le_of_lt hp) (le_of_lt hp1) j)
        (bayesFalsePost_sum a c p ha hsum hp hp1)
        (mul_nonneg hW hnF)
        (b - 1)
      have h2 := ihT (bayesTruePost a c p) (W * bayesTrueNorm a c p)
        (fun j => bayesTruePost_nonneg a c p ha (le_of_lt hp) (le_of_lt hp1) j)
        (bayesTruePost_sum a c p ha hsum hp hp1)
        (mul_nonneg hW hnT)
        (b - 1)
      set D_F := treeDeepProb p (b - 1) onFalse (bayesFalsePost a c p)
        (W * bayesFalseNorm a c p) with hDFdef
      set D_T := treeDeepProb p (b - 1) onTrue (bayesTruePost a c p)
        (W * bayesTrueNorm a c p) with hDTdef
      set Δ_F := treeDepth p onFalse (bayesFalsePost a c p)
        (W * bayesFalseNorm a c p) with hΔFdef
      set Δ_T := treeDepth p onTrue (bayesTruePost a c p)
        (W * bayesTrueNorm a c p) with hΔTdef
      have hdf := treeDeepProb_le p hp hp1 onFalse (bayesFalsePost a c p)
        (W * bayesFalseNorm a c p)
        (fun j => bayesFalsePost_nonneg a c p ha (le_of_lt hp) (le_of_lt hp1) j)
        (bayesFalsePost_sum a c p ha hsum hp hp1)
        (mul_nonneg hW hnF) (b - 1)
      have hdt := treeDeepProb_le p hp hp1 onTrue (bayesTruePost a c p)
        (W * bayesTrueNorm a c p)
        (fun j => bayesTruePost_nonneg a c p ha (le_of_lt hp) (le_of_lt hp1) j)
        (bayesTruePost_sum a c p ha hsum hp hp1)
        (mul_nonneg hW hnT) (b - 1)
      have hn := norm_sum a c p
      have hW1 : W * bayesFalseNorm a c p + W * bayesTrueNorm a c p = W := by
        calc W * bayesFalseNorm a c p + W * bayesTrueNorm a c p
            = W * (bayesFalseNorm a c p + bayesTrueNorm a c p) := by ring
          _ = W * (∑ m, a m) := by rw [hn]
          _ = W * 1 := by rw [hsum]
          _ = W := by ring
      have hcast : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
        rw [Nat.cast_sub (R := ℝ) (m := 1) (n := b) (by omega)]
        norm_num
      have hdist : ((b - 1 : ℕ) : ℝ) * (D_F + D_T)
          = ((b - 1 : ℕ) : ℝ) * D_F + ((b - 1 : ℕ) : ℝ) * D_T := by ring
      have hdist2 : (b : ℝ) * (D_F + D_T)
          = ((b - 1 : ℕ) : ℝ) * (D_F + D_T) + (D_F + D_T) := by
        rw [hcast]; ring
      have hDF : D_F ≤ W * bayesFalseNorm a c p := by rw [hDFdef]; exact hdf
      have hDT : D_T ≤ W * bayesTrueNorm a c p := by rw [hDTdef]; exact hdt
      have hΔF : ((b - 1 : ℕ) : ℝ) * D_F ≤ Δ_F := by
        rw [hDFdef, hΔFdef]; exact h1
      have hΔT : ((b - 1 : ℕ) : ℝ) * D_T ≤ Δ_T := by
        rw [hDTdef, hΔTdef]; exact h2
      simp only [treeDepth]
      linarith

/-- For a nonempty uniform search space and `0 < p < 1`, the threshold times the query tail
probability is at most expected queries. -/
theorem noisy_markov_tail {n : ℕ} (hn : 0 < n) (p : ℝ) (tr : BoolQueryTree (Fin n) (Fin n))
    (hp : 0 < p) (hp1 : p < 1) (t : ℕ) :
    (t : ℝ) * uniformTailProb p t tr ≤ uniformExpectedQueries p tr := by
  have h := treeDepth_markov p hp hp1 tr (uniformPosterior (n := n)) 1
    (fun j => by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
      unfold uniformPosterior
      exact div_nonneg (by norm_num) hn0)
    (uniform_sum hn) (by norm_num) t
  simpa [uniformTailProb, uniformExpectedQueries] using! h

/-- At depth threshold zero, the deep-tree functional equals the initial weight. -/
theorem treeDeepProb_zero {n : ℕ} (p : ℝ) :
    ∀ (tr : BoolQueryTree (Fin n) (Fin n)) (a : Fin n → ℝ) (W : ℝ),
      treeDeepProb p 0 tr a W = W := by
  intro tr
  induction tr with
  | halt o => intro a W; simp [treeDeepProb]
  | ask c onFalse onTrue ihF ihT =>
    intro a W
    simp [treeDeepProb]

/-- Collects Markov tail bounds for uniform noisy query costs and weighted tree depths. -/
theorem walkGoal_tail_endpoint :
    ∀ (n : ℕ) (p : ℝ) (tr : BoolQueryTree (Fin n) (Fin n)),
      (hn : 0 < n) → (hp : 1 / 2 < p) → (hp1 : p < 1) →
      (∀ (t : ℕ), (t : ℝ) * uniformTailProb p t tr ≤ uniformExpectedQueries p tr) ∧
      (∀ (t : ℕ) (a : Fin n → ℝ) (W : ℝ),
        (∀ j, 0 ≤ a j) → (∑ j, a j) = 1 → 0 ≤ W →
        (t : ℝ) * treeDeepProb p t tr a W ≤ treeDepth p tr a W) := by
  intro n p tr hn hp hp1
  have hp0 : 0 < p := by linarith
  refine ⟨?_, ?_⟩
  · intro t
    exact noisy_markov_tail hn p tr hp0 hp1 t
  · intro t a W ha hsum hW
    exact treeDepth_markov p hp0 hp1 tr a W ha hsum hW t

/-- At an ask node, weighted noiseless depth is the total input weight plus the depth sums of
the two branches with their corresponding restricted weights. -/
theorem noiselessDepthSumW_ask {n : ℕ} (c : Fin n) (onFalse onTrue : BoolQueryTree (Fin n) (Fin n))
    (w : Fin n → ℝ) :
    noiselessDepthSumW (.ask c onFalse onTrue) w
      = (∑ j : Fin n, w j)
        + noiselessDepthSumW onFalse (fun j => if (c : ℕ) ≤ (j : ℕ) then 0 else w j)
        + noiselessDepthSumW onTrue (fun j => if (c : ℕ) ≤ (j : ℕ) then w j else 0) := by
  have key : (∑ j : Fin n, w j * noiselessQueries j (.ask c onFalse onTrue))
      = (∑ j : Fin n, w j)
        + (∑ j : Fin n, (if (c : ℕ) ≤ (j : ℕ) then 0 else w j) * noiselessQueries j onFalse)
        + (∑ j : Fin n, (if (c : ℕ) ≤ (j : ℕ) then w j else 0) * noiselessQueries j onTrue) := by
    have hfinal : ∀ j : Fin n,
        w j * noiselessQueries j (.ask c onFalse onTrue)
          = w j + (if (c : ℕ) ≤ (j : ℕ) then 0 else w j) * noiselessQueries j onFalse
              + (if (c : ℕ) ≤ (j : ℕ) then w j else 0) * noiselessQueries j onTrue := by
      intro j
      by_cases h : (c : ℕ) ≤ (j : ℕ)
      · rw [noiselessQueries_ask j c onFalse onTrue h]
        simp only [if_pos h, Nat.cast_add, Nat.cast_one]
        ring
      · rw [noiselessQueries_ask_neg j c onFalse onTrue h]
        simp only [if_neg h, Nat.cast_add, Nat.cast_one]
        ring
    rw [sum_congr' hfinal]
    simp only [Finset.sum_add_distrib]
  unfold noiselessDepthSumW
  rw [key]

/-- The depth threshold times the number of cells above that threshold is at most the sum of
their noiseless query counts. -/
theorem cellsAboveDepth_card_le {n : ℕ} (tr : BoolQueryTree (Fin n) (Fin n)) (t : ℕ) :
    (t : ℝ) * ((cellsAboveDepth tr t).card : ℝ)
      ≤ ∑ j ∈ cellsAboveDepth tr t, (noiselessQueries j tr : ℝ) := by
  have hstep : ∀ j ∈ cellsAboveDepth tr t, t ≤ noiselessQueries j tr := by
    intro j hj
    have h := (Finset.mem_filter.mp hj).2
    omega
  have hsum : (∑ j ∈ cellsAboveDepth tr t, t) = (cellsAboveDepth tr t).card * t := by
    simp [Finset.sum_const]
  have h1 : t * (cellsAboveDepth tr t).card ≤ ∑ j ∈ cellsAboveDepth tr t, noiselessQueries j tr := by
    calc t * (cellsAboveDepth tr t).card = (cellsAboveDepth tr t).card * t := Nat.mul_comm _ _
      _ = ∑ j ∈ cellsAboveDepth tr t, t := hsum.symm
      _ ≤ ∑ j ∈ cellsAboveDepth tr t, noiselessQueries j tr :=
        Finset.sum_le_sum (s := cellsAboveDepth tr t) (f := fun _ => t)
          (g := fun j => noiselessQueries j tr) fun j hj => hstep j hj
  exact_mod_cast h1

/-- The sum of noiseless query counts over cells above a threshold is at most the sum over all
cells. -/
theorem cellsAboveDepth_sum_le {n : ℕ} (tr : BoolQueryTree (Fin n) (Fin n)) (t : ℕ) :
    (∑ j ∈ cellsAboveDepth tr t, (noiselessQueries j tr : ℝ))
      ≤ ∑ j : Fin n, (noiselessQueries j tr : ℝ) := by
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun x _ => Finset.mem_univ x)
    (fun x _ _ => Nat.cast_nonneg _)

/-- The sum of all noiseless query counts equals `noiselessDepthSum`. -/
theorem noiselessDepthSum_eq {n : ℕ} (tr : BoolQueryTree (Fin n) (Fin n)) :
    (∑ j : Fin n, (noiselessQueries j tr : ℝ)) = noiselessDepthSum tr := by
  rw [noiselessDepthSum, noiselessDepthSumW]
  exact sum_congr' fun j => by ring

/-- The depth threshold times the number of cells above it is at most `noiselessDepthSum`. -/
theorem cellsAboveDepth_card_le_sum {n : ℕ} (tr : BoolQueryTree (Fin n) (Fin n)) (t : ℕ) :
    (t : ℝ) * ((cellsAboveDepth tr t).card : ℝ) ≤ noiselessDepthSum tr :=
  (cellsAboveDepth_card_le tr t).trans
    ((cellsAboveDepth_sum_le tr t).trans_eq (noiselessDepthSum_eq tr))

/-- The explicit four-cell query tree used as a counterexample to the printed mean-query bound. -/
noncomputable def cor27Witness : BoolQueryTree (Fin 4) (Fin 4) :=
  .ask ⟨2, by decide⟩
    (.ask ⟨1, by decide⟩ (.halt ⟨0, by decide⟩) (.halt ⟨1, by decide⟩))
    (.halt ⟨2, by decide⟩)

/-- The sum of noiseless query counts of `cor27Witness` over its four inputs is six. -/
theorem cor27Witness_depthSum :
    (∑ j : Fin 4, (noiselessQueries j cor27Witness : ℝ)) = 6 := by
  simp [cor27Witness, noiselessQueries, Fin.sum_univ_four]
  ring

/-- The noiseless depth sum of `cor27Witness` is six. -/
theorem cor27Witness_depthSum' : noiselessDepthSum cor27Witness = 6 := by
  rw [noiselessDepthSum, noiselessDepthSumW]
  simpa using! cor27Witness_depthSum

/-- The witness tree returns the correct cell on exactly three inputs. -/
theorem cor27Witness_correct :
    (correctCells cor27Witness).card = 3 := by
  have hset : correctCells cor27Witness = {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩} := by
    ext j
    simp only [correctCells, Finset.mem_filter, Finset.mem_univ, true_and]
    fin_cases j <;> simp [cor27Witness, noiselessOutput]
  simp [hset]

/-- The mean noiseless query count of the witness tree is `3 / 2`. -/
theorem cor27Witness_mean : noiselessMeanQueries cor27Witness = (3 / 2 : ℝ) := by
  rw [noiselessMeanQueries, cor27Witness_depthSum']
  norm_num

/-- The four-cell witness has mean query count strictly below the printed logarithmic bound,
refuting that mean-query formulation of [Ben-Or and Hassidim, Corollary
2.7][BenOrHassidim2007]. -/
theorem printed_corollary_2_7_mean_refuted :
    noiselessMeanQueries cor27Witness
      < Real.log 4 / Real.log 2 - Real.log (1 / (1 - 1 / 4)) / Real.log 2 := by
  have hmean : noiselessMeanQueries cor27Witness = (3 / 2 : ℝ) := cor27Witness_mean
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : Real.log 4 / Real.log 2 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    field_simp
    norm_num
  have hfrac : 1 / (1 - 1 / 4 : ℝ) = 4 / 3 := by norm_num
  have hsmall : Real.log (4 / 3 : ℝ) / Real.log 2 < 1 / 2 := by
    have h1 : (4 / 3 : ℝ) < Real.sqrt 2 := by
      have hsq : (4 / 3 : ℝ) ^ 2 < 2 := by norm_num
      have hpos : (0 : ℝ) ≤ 4 / 3 := by norm_num
      exact (Real.lt_sqrt hpos).mpr hsq
    have h2 : Real.log (4 / 3 : ℝ) < Real.log (Real.sqrt 2) :=
      Real.log_lt_log (by norm_num) h1
    have hsqrt : Real.log (Real.sqrt 2) = Real.log 2 / 2 := by
      have hpos2 : (0 : ℝ) ≤ 2 := by norm_num
      rw [Real.log_sqrt hpos2]
    rw [hsqrt] at h2
    have h2' : Real.log (4 / 3 : ℝ) < ((Real.log 2 / 2) / Real.log 2) * Real.log 2 := by
      have heq : ((Real.log 2 / 2) / Real.log 2) * Real.log 2 = Real.log 2 / 2 := by field_simp
      rw [heq]
      exact h2
    have h3 : Real.log (4 / 3 : ℝ) / Real.log 2 < (Real.log 2 / 2) / Real.log 2 :=
      (div_lt_iff₀ hlog2).mpr h2'
    have h4 : (Real.log 2 / 2) / Real.log 2 = 1 / 2 := by field_simp
    linarith
  rw [hmean, hL, hfrac]
  linarith

/-- If mean noiseless queries are at most `a > 0`, the fraction of cells at depth at least `t ≥
χ * a` is at most `1 / χ` for `χ > 1`. This is the corrected Markov tail statement
associated with [Ben-Or and Hassidim, Lemma 2.9][BenOrHassidim2007]. -/
theorem lemma2_9_tail_corrected {n : ℕ} (tr : BoolQueryTree (Fin n) (Fin n)) (a : ℝ) (t : ℕ)
    (χ : ℝ) (hn : 0 < n) (hχ : 1 < χ) (ha : 0 < a)
    (hmean : noiselessMeanQueries tr ≤ a) (ht : (t : ℝ) ≥ χ * a) :
    ((cellsAboveDepth tr t).card : ℝ) / (n : ℝ) ≤ 1 / χ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (t : ℝ) * ((cellsAboveDepth tr t).card : ℝ) ≤ noiselessDepthSum tr :=
    cellsAboveDepth_card_le_sum tr t
  have h2 : noiselessDepthSum tr ≤ (n : ℝ) * a := by
    have hmean' : noiselessDepthSum tr / (n : ℝ) ≤ a := by
      simpa [noiselessMeanQueries] using! hmean
    have hraw := (div_le_iff₀ hn0).mp hmean'
    calc noiselessDepthSum tr ≤ a * (n : ℝ) := hraw
      _ = (n : ℝ) * a := by ring
  have h5 : ((χ : ℝ) * ((cellsAboveDepth tr t).card : ℝ)) * a ≤ (n : ℝ) * a := by
    calc ((χ : ℝ) * ((cellsAboveDepth tr t).card : ℝ)) * a
        = (χ : ℝ) * a * ((cellsAboveDepth tr t).card : ℝ) := by ring
      _ ≤ (t : ℝ) * ((cellsAboveDepth tr t).card : ℝ) :=
        mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg _)
      _ ≤ noiselessDepthSum tr := h1
      _ ≤ (n : ℝ) * a := h2
  have h6 : (χ : ℝ) * ((cellsAboveDepth tr t).card : ℝ) ≤ (n : ℝ) :=
    le_of_mul_le_mul_right h5 ha
  have h4 : ((cellsAboveDepth tr t).card : ℝ) / (n : ℝ) ≤ 1 / χ := by
    rw [div_le_iff₀ hn0]
    rw [show (1 / χ : ℝ) * (n : ℝ) = (n : ℝ) / χ by ring]
    rw [le_div_iff₀ (show (0 : ℝ) < χ by linarith)]
    linarith
  exact h4

/-- Expands the difference between the printed tail threshold and `χ` times the stated mean
bound into a single quotient. -/
theorem lemma2_9_printed_threshold_eq {L lgL c₁ δ χ I : ℝ} (hI : I ≠ 0) :
    (L / I + χ * (c₁ + 2) * lgL / I
        - χ * (L / I + c₁ * lgL * (Real.log (1 / δ) / Real.log 2) / I))
      = (-(χ - 1) * L + χ * lgL * (c₁ + 2 - c₁ * (Real.log (1 / δ) / Real.log 2))) / I := by
  have hlog : Real.log (1 / δ) = -Real.log δ := by
    simp only [div_eq_mul_inv, one_mul, Real.log_inv]
  rw [hlog]
  field_simp
  ring

/-- For positive `I`, the printed tail threshold is at least `χ` times the mean expression
exactly when the stated inequality in `L` and `lgL` holds. -/
theorem lemma2_9_printed_threshold_condition {L lgL c₁ δ χ I : ℝ} (hI : 0 < I) :
    (L / I + χ * (c₁ + 2) * lgL / I
        ≥ χ * (L / I + c₁ * lgL * (Real.log (1 / δ) / Real.log 2) / I))
      ↔ ((χ - 1) * L ≤ χ * lgL * (c₁ + 2 - c₁ * (Real.log (1 / δ) / Real.log 2))) := by
  have h := lemma2_9_printed_threshold_eq (L := L) (lgL := lgL) (c₁ := c₁) (δ := δ) (χ := χ)
    (I := I) hI.ne'
  have hsub : (0 ≤ (L / I + χ * (c₁ + 2) * lgL / I
        - χ * (L / I + c₁ * lgL * (Real.log (1 / δ) / Real.log 2) / I)) ↔
      0 ≤ (-(χ - 1) * L + χ * lgL * (c₁ + 2 - c₁ * (Real.log (1 / δ) / Real.log 2))) / I) := by
    rw [h]
  constructor
  · intro hx
    have hx' : 0 ≤ (L / I + χ * (c₁ + 2) * lgL / I
        - χ * (L / I + c₁ * lgL * (Real.log (1 / δ) / Real.log 2) / I)) := by
      exact sub_nonneg.mpr hx
    have hquot := (le_div_iff₀ hI).mp (hsub.mp hx')
    linarith
  · intro hx
    have hx' : 0 ≤ (-(χ - 1) * L
        + χ * lgL * (c₁ + 2 - c₁ * (Real.log (1 / δ) / Real.log 2))) := by linarith
    have hquot : 0 ≤ (-(χ - 1) * L
        + χ * lgL * (c₁ + 2 - c₁ * (Real.log (1 / δ) / Real.log 2))) / I :=
      div_nonneg hx' hI.le
    exact sub_nonneg.mp (hsub.mpr hquot)

/-- The necessary printed-threshold comparison fails for the explicit constants `L = 2`, `lgL =
1`, `c₁ = 1`, `δ = 1 / 256`, and `χ = 2`. -/
theorem lemma2_9_printed_threshold_fails :
    ¬ ((2 - 1 : ℝ) * 2 ≤ 2 * 1 * (1 + 2 - 1 * (Real.log (1 / (1 / 256 : ℝ)) / Real.log 2))) := by
  have hlog : Real.log (1 / (1 / 256 : ℝ)) / Real.log 2 = 8 := by
    rw [show (1 / (1 / 256 : ℝ)) = 2 ^ 8 by norm_num, Real.log_pow]
    field_simp
    norm_num
  rw [hlog]
  norm_num

/-- The sum of `2` to the negative noiseless query depth over any correctly identified set of
cells is at most one. -/
theorem kraft_correct {n : ℕ} : ∀ (tr : BoolQueryTree (Fin n) (Fin n)) (S : Finset (Fin n)),
    (∀ j ∈ S, noiselessOutput j tr = j) →
    (∑ j ∈ S, (1 / 2 : ℝ) ^ (noiselessQueries j tr)) ≤ 1 := by
  intro tr
  induction tr with
  | halt o =>
      intro S hS
      have hsub : S ⊆ ({o} : Finset (Fin n)) := by
        intro j hj
        have h1 : o = j := hS j hj
        rw [h1]
        exact Finset.mem_singleton.mpr rfl
      have hpoint : ∀ j ∈ S, (1 / 2 : ℝ) ^ (noiselessQueries j (.halt o)) = 1 := by
        intro j _
        simp [noiselessQueries]
      have hsum : (∑ j ∈ S, (1 / 2 : ℝ) ^ (noiselessQueries j (.halt o))) = (S.card : ℝ) := by
        rw [Finset.sum_congr rfl hpoint]
        simp [Finset.sum_const]
      have hcard : (S.card : ℝ) ≤ 1 := by
        have hle : S.card ≤ ({o} : Finset (Fin n)).card := Finset.card_le_card hsub
        simp only [Finset.card_singleton] at hle
        exact_mod_cast hle
      rw [hsum]
      exact hcard
  | ask c onFalse onTrue ihFalse ihTrue =>
      intro S hS
      have hsplit := Finset.sum_filter_add_sum_filter_not S
        (fun j : Fin n => (c : ℕ) ≤ (j : ℕ))
        (fun j => (1 / 2 : ℝ) ^ (noiselessQueries j (.ask c onFalse onTrue)))
      have hplus : (∑ j ∈ S.filter (fun j : Fin n => (c : ℕ) ≤ (j : ℕ)),
            (1 / 2 : ℝ) ^ (noiselessQueries j (.ask c onFalse onTrue)))
          = (1 / 2 : ℝ) * (∑ j ∈ S.filter (fun j : Fin n => (c : ℕ) ≤ (j : ℕ)),
            (1 / 2 : ℝ) ^ (noiselessQueries j onTrue)) := by
        have hpoint : ∀ j ∈ S.filter (fun j : Fin n => (c : ℕ) ≤ (j : ℕ)),
            (1 / 2 : ℝ) ^ (noiselessQueries j (.ask c onFalse onTrue))
              = (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ (noiselessQueries j onTrue) := by
          intro j hj
          have hc : (c : ℕ) ≤ (j : ℕ) := (Finset.mem_filter.mp hj).2
          rw [noiselessQueries_ask j c onFalse onTrue hc, pow_add]
          simp only [pow_one]
        rw [Finset.sum_congr rfl hpoint]
        rw [← Finset.mul_sum]
      have hminus : (∑ j ∈ S.filter (fun j : Fin n => ¬((c : ℕ) ≤ (j : ℕ))),
            (1 / 2 : ℝ) ^ (noiselessQueries j (.ask c onFalse onTrue)))
          = (1 / 2 : ℝ) * (∑ j ∈ S.filter (fun j : Fin n => ¬((c : ℕ) ≤ (j : ℕ))),
            (1 / 2 : ℝ) ^ (noiselessQueries j onFalse)) := by
        have hpoint : ∀ j ∈ S.filter (fun j : Fin n => ¬((c : ℕ) ≤ (j : ℕ))),
            (1 / 2 : ℝ) ^ (noiselessQueries j (.ask c onFalse onTrue))
              = (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ (noiselessQueries j onFalse) := by
          intro j hj
          have hc : ¬((c : ℕ) ≤ (j : ℕ)) := (Finset.mem_filter.mp hj).2
          rw [noiselessQueries_ask_neg j c onFalse onTrue hc, pow_add]
          simp only [pow_one]
        rw [Finset.sum_congr rfl hpoint]
        rw [← Finset.mul_sum]
      have hSplus : ∀ j ∈ S.filter (fun j : Fin n => (c : ℕ) ≤ (j : ℕ)),
          noiselessOutput j onTrue = j := by
        intro j hj
        have hj' := Finset.mem_filter.mp hj
        have hjS : j ∈ S := hj'.1
        have hc : (c : ℕ) ≤ (j : ℕ) := hj'.2
        have hout := hS j hjS
        rw [noiselessOutput_ask j c onFalse onTrue hc] at hout
        exact hout
      have hSminus : ∀ j ∈ S.filter (fun j : Fin n => ¬((c : ℕ) ≤ (j : ℕ))),
          noiselessOutput j onFalse = j := by
        intro j hj
        have hj' := Finset.mem_filter.mp hj
        have hjS : j ∈ S := hj'.1
        have hc : ¬((c : ℕ) ≤ (j : ℕ)) := hj'.2
        have hout := hS j hjS
        rw [noiselessOutput_ask_neg j c onFalse onTrue hc] at hout
        exact hout
      rw [← hsplit, hplus, hminus]
      have h1 := ihTrue _ hSplus
      have h2 := ihFalse _ hSminus
      linarith

/-- A finite product of powers of a fixed real base equals that base raised to the sum of the
exponents. -/
theorem prod_const_pow {ι : Type*} (s : Finset ι) (b : ℝ) (f : ι → ℕ) :
    (∏ i ∈ s, b ^ (f i)) = b ^ (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha, Finset.prod_insert ha]
      rw [ih, pow_add]

/-- On a nonempty set of correctly identified cells, the sum of noiseless query counts is at
least its cardinality times the base-two logarithm of that cardinality. -/
theorem depth_sum_ge_card_log_card {n : ℕ} (tr : BoolQueryTree (Fin n) (Fin n))
    (S : Finset (Fin n)) (hS : ∀ j ∈ S, noiselessOutput j tr = j) (hcard : 0 < S.card) :
    (↑(∑ j ∈ S, noiselessQueries j tr) : ℝ)
      ≥ (S.card : ℝ) * (Real.log (S.card : ℝ) / Real.log 2) := by
  classical
  have hzpos : ∀ j : Fin n, 0 < (1 / 2 : ℝ) ^ (noiselessQueries j tr) := by
    intro j
    positivity
  have hk := kraft_correct tr S hS
  have hsum1 : (∑ j ∈ S, (1 : ℝ)) = (S.card : ℝ) := by
    simp [Finset.sum_const]
  have hcardR : (0 : ℝ) < S.card := by exact_mod_cast hcard
  have hgm0 := Real.geom_mean_le_arith_mean S (fun _ => (1 : ℝ))
    (fun j => (1 / 2 : ℝ) ^ (noiselessQueries j tr))
    (fun _ _ => by norm_num) (by rw [hsum1]; exact_mod_cast hcard)
    (fun j _ => (le_of_lt (hzpos j)))
  have hgmprod : (∏ j ∈ S, ((1 / 2 : ℝ) ^ (noiselessQueries j tr)) ^ (1 : ℝ))
      = ∏ j ∈ S, (1 / 2 : ℝ) ^ (noiselessQueries j tr) := by
    simp [Real.rpow_one]
  have hgm : (∏ j ∈ S, (1 / 2 : ℝ) ^ (noiselessQueries j tr)) ^ ((S.card : ℝ))⁻¹
      ≤ (∑ j ∈ S, (1 / 2 : ℝ) ^ (noiselessQueries j tr)) / (S.card : ℝ) := by
    have h := hgm0
    simp only [Real.rpow_one, hsum1] at h
    have h2 : (∑ x ∈ S, 1 * (1 / 2 : ℝ) ^ (noiselessQueries x tr))
        = ∑ x ∈ S, (1 / 2 : ℝ) ^ (noiselessQueries x tr) :=
      Finset.sum_congr rfl fun j _ => by ring
    rw [h2] at h
    exact h
  have hsum_le : (∑ j ∈ S, (1 / 2 : ℝ) ^ (noiselessQueries j tr)) * (S.card : ℝ)
      ≤ 1 * (S.card : ℝ) := mul_le_mul_of_nonneg_right hk hcardR.le
  have hfrac : (∑ j ∈ S, (1 / 2 : ℝ) ^ (noiselessQueries j tr)) / (S.card : ℝ)
      ≤ 1 / (S.card : ℝ) := by
    exact (div_le_div_iff₀ hcardR hcardR).mpr hsum_le
  have hmono : MonotoneOn Real.log (Set.Ioi 0) := Real.strictMonoOn_log.monotoneOn
  have hprodpos : 0 < (∏ j ∈ S, (1 / 2 : ℝ) ^ (noiselessQueries j tr)) := by
    exact Finset.prod_pos fun j _ => hzpos j
  have hposL : 0 < (∏ j ∈ S, (1 / 2 : ℝ) ^ (noiselessQueries j tr)) ^ ((S.card : ℝ))⁻¹ := by
    rw [Real.rpow_def_of_pos hprodpos]
    exact Real.exp_pos _
  obtain ⟨j0, hj0⟩ : S.Nonempty := Finset.card_ne_zero.mp (ne_of_gt hcard)
  have hsumpos : 0 < (∑ j ∈ S, (1 / 2 : ℝ) ^ (noiselessQueries j tr)) :=
    Finset.sum_pos (fun j _ => hzpos j) ⟨j0, hj0⟩
  have hposR : 0 < (∑ j ∈ S, (1 / 2 : ℝ) ^ (noiselessQueries j tr)) / (S.card : ℝ) :=
    div_pos hsumpos hcardR
  have hlog1 : Real.log ((∏ j ∈ S, (1 / 2 : ℝ) ^ (noiselessQueries j tr)) ^ ((S.card : ℝ))⁻¹)
      ≤ Real.log (1 / (S.card : ℝ)) := by
    calc Real.log ((∏ j ∈ S, (1 / 2 : ℝ) ^ (noiselessQueries j tr)) ^ ((S.card : ℝ))⁻¹)
        ≤ Real.log ((∑ j ∈ S, (1 / 2 : ℝ) ^ (noiselessQueries j tr)) / (S.card : ℝ)) :=
          hmono (Set.mem_Ioi.mpr hposL) (Set.mem_Ioi.mpr hposR) hgm
      _ ≤ Real.log (1 / (S.card : ℝ)) :=
        hmono (Set.mem_Ioi.mpr hposR) (Set.mem_Ioi.mpr (div_pos (by norm_num) hcardR)) hfrac
  have hlogprod : Real.log (∏ j ∈ S, (1 / 2 : ℝ) ^ (noiselessQueries j tr))
      = -(↑(∑ j ∈ S, noiselessQueries j tr) : ℝ) * Real.log 2 := by
    have hprod : (∏ j ∈ S, (1 / 2 : ℝ) ^ (noiselessQueries j tr))
        = (1 / 2 : ℝ) ^ (∑ j ∈ S, noiselessQueries j tr) := by
      rw [← prod_const_pow]
    rw [hprod, Real.log_pow]
    have hinv : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [div_eq_mul_inv, one_mul, Real.log_inv]
    rw [hinv]
    ring
  have hlogprod' : Real.log ((∏ j ∈ S, (1 / 2 : ℝ) ^ (noiselessQueries j tr))
      ^ ((S.card : ℝ))⁻¹)
      = ((S.card : ℝ))⁻¹ * (-(↑(∑ j ∈ S, noiselessQueries j tr) : ℝ) * Real.log 2) := by
    rw [Real.log_rpow hprodpos]
    rw [hlogprod]
  have hloginv : Real.log (1 / (S.card : ℝ)) = -Real.log (S.card : ℝ) := by
    rw [div_eq_mul_inv, one_mul, Real.log_inv]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [hlogprod', hloginv] at hlog1
  have hfinal : (↑(∑ j ∈ S, noiselessQueries j tr) : ℝ) * Real.log 2
      ≥ (S.card : ℝ) * Real.log (S.card : ℝ) := by
    have hmul : ((S.card : ℝ))⁻¹ * (-(↑(∑ j ∈ S, noiselessQueries j tr) : ℝ) * Real.log 2)
        ≤ -Real.log (S.card : ℝ) := hlog1
    have h2 := mul_le_mul_of_nonneg_right hmul hcardR.le
    field_simp at h2
    linarith
  have hdiv : (↑(∑ j ∈ S, noiselessQueries j tr) : ℝ)
      ≥ (S.card : ℝ) * (Real.log (S.card : ℝ) / Real.log 2) := by
    have hres := (div_le_iff₀ hlog2).mpr hfinal
    have heq : (S.card : ℝ) * (Real.log (S.card : ℝ) / Real.log 2)
        = (S.card : ℝ) * Real.log (S.card : ℝ) / Real.log 2 := by ring
    rw [heq]
    exact hres
  exact hdiv

/-- A finite sum of natural numbers cast termwise to the reals equals the cast of their
natural-number sum. -/
theorem sum_cast_eq {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    (∑ i ∈ s, (f i : ℝ)) = (↑(∑ i ∈ s, f i) : ℝ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [ih]
      simp only [Nat.cast_add]

/-- If the correct-cell set is nonempty, its noiseless query-count sum is at least its
cardinality times the base-two logarithm of its cardinality. -/
theorem correctCells_depth_sum_ge {n : ℕ} (tr : BoolQueryTree (Fin n) (Fin n))
    (hcard : 0 < (correctCells tr).card) :
    (∑ j ∈ correctCells tr, (noiselessQueries j tr : ℝ))
      ≥ (correctCells tr).card * (Real.log (correctCells tr).card / Real.log 2) := by
  have hcorrect : ∀ j ∈ correctCells tr, noiselessOutput j tr = j := by
    intro j hj
    exact (Finset.mem_filter.mp hj).2
  have h := depth_sum_ge_card_log_card tr (correctCells tr) hcorrect hcard
  rw [← sum_cast_eq] at h
  exact h

/-- The noiseless query-count sum over correctly identified cells is at most the total noiseless
depth sum. -/
theorem correctCells_depth_sum_le_total {n : ℕ} (tr : BoolQueryTree (Fin n) (Fin n)) :
    (∑ j ∈ correctCells tr, (noiselessQueries j tr : ℝ)) ≤ noiselessDepthSum tr := by
  have h1 : (∑ j ∈ correctCells tr, (noiselessQueries j tr : ℝ))
      ≤ ∑ j : Fin n, (noiselessQueries j tr : ℝ) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun x _ => Finset.mem_univ x)
      (fun x _ _ => Nat.cast_nonneg _)
  rw [noiselessDepthSum_eq tr] at h1
  exact h1

/-- For a nonempty correct-cell set, its cardinality times its base-two logarithm is at most the
total noiseless depth sum. This gives a corrected mean-query bound associated with [Ben-Or
and Hassidim, Corollary 2.7][BenOrHassidim2007]. -/
theorem corrected_corollary_2_7_mean {n : ℕ} (tr : BoolQueryTree (Fin n) (Fin n))
    (hcard : 0 < (correctCells tr).card) :
    (correctCells tr).card * (Real.log (correctCells tr).card / Real.log 2)
      ≤ noiselessDepthSum tr :=
  (correctCells_depth_sum_ge tr hcard).trans (correctCells_depth_sum_le_total tr)

/-- Writing `s` for the positive fraction of correctly identified cells, `s * (log₂ n + log₂ s)`
is at most the mean noiseless depth for a nonempty search space. -/
theorem corrected_corollary_2_7_mean_tau {n : ℕ} (tr : BoolQueryTree (Fin n) (Fin n))
    (hn : 0 < n) (hcard : 0 < (correctCells tr).card) :
    ((correctCells tr).card : ℝ) / (n : ℝ)
        * (Real.log (n : ℝ) / Real.log 2
          + Real.log (((correctCells tr).card : ℝ) / (n : ℝ)) / Real.log 2)
      ≤ noiselessDepthSum tr / (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < (correctCells tr).card := by exact_mod_cast hcard
  have hlogid : Real.log (n : ℝ) / Real.log 2
      + Real.log (((correctCells tr).card : ℝ) / (n : ℝ)) / Real.log 2
      = Real.log ((correctCells tr).card : ℝ) / Real.log 2 := by
    have h1 : Real.log (n : ℝ) + Real.log (((correctCells tr).card : ℝ) / (n : ℝ))
        = Real.log ((correctCells tr).card : ℝ) := by
      have heq : (n : ℝ) * (((correctCells tr).card : ℝ) / (n : ℝ)) = (correctCells tr).card := by
        field_simp
      rw [← Real.log_mul (by positivity) (by positivity), heq]
    have h1' := congrArg (fun x : ℝ => x / Real.log 2) h1

    rw [add_div] at h1'
    exact h1'
  have hmain := corrected_corollary_2_7_mean tr hcard
  have h1 : ((correctCells tr).card : ℝ) / (n : ℝ)
      * (Real.log ((correctCells tr).card : ℝ) / Real.log 2) * (n : ℝ)
      ≤ noiselessDepthSum tr := by
    calc ((correctCells tr).card : ℝ) / (n : ℝ)
        * (Real.log ((correctCells tr).card : ℝ) / Real.log 2) * (n : ℝ)
        = ((correctCells tr).card : ℝ) * (Real.log ((correctCells tr).card : ℝ) / Real.log 2) := by
          field_simp
      _ ≤ noiselessDepthSum tr := hmain
  have h2 : ((correctCells tr).card : ℝ) / (n : ℝ)
      * (Real.log ((correctCells tr).card : ℝ) / Real.log 2)
      ≤ noiselessDepthSum tr / (n : ℝ) := (le_div_iff₀ hn0).mpr h1
  rw [hlogid]
  exact h2

/-- At `p = 1`, the false-answer likelihood is the indicator of `j < c`. -/
theorem bayesFalseLikelihood_one {n : ℕ} (c j : Fin n) :
    bayesFalseLikelihood c j 1 = if (c : ℕ) ≤ (j : ℕ) then 0 else 1 := by
  simp only [bayesFalseLikelihood]
  by_cases h : (c : ℕ) ≤ (j : ℕ)
  · simp [h]
  · simp [h]

/-- At `p = 1`, the true-answer likelihood is the indicator of `c ≤ j`. -/
theorem bayesTrueLikelihood_one {n : ℕ} (c j : Fin n) :
    bayesTrueLikelihood c j 1 = if (c : ℕ) ≤ (j : ℕ) then 1 else 0 := by
  simp only [bayesTrueLikelihood]
  by_cases h : (c : ℕ) ≤ (j : ℕ)
  · simp [h]
  · simp [h]

/-- At `p = 1`, the false-answer posterior has total mass one if its normalizer is nonzero and
the prior is nonnegative. -/
theorem bayesFalsePost_sum_one {n : ℕ} (a : Fin n → ℝ) (c : Fin n) (ha : ∀ j, 0 ≤ a j)
    (hn : bayesFalseNorm a c 1 ≠ 0) :
    (∑ j, bayesFalsePost a c 1 j) = 1 := by
  unfold bayesFalsePost
  rw [← Finset.sum_div]
  have h1 : (∑ j, a j * bayesFalseLikelihood c j 1) = bayesFalseNorm a c 1 := rfl
  rw [h1]
  exact div_self hn

/-- At `p = 1`, the true-answer posterior has total mass one if its normalizer is nonzero and
the prior is nonnegative. -/
theorem bayesTruePost_sum_one {n : ℕ} (a : Fin n → ℝ) (c : Fin n) (ha : ∀ j, 0 ≤ a j)
    (hn : bayesTrueNorm a c 1 ≠ 0) :
    (∑ j, bayesTruePost a c 1 j) = 1 := by
  unfold bayesTruePost
  rw [← Finset.sum_div]
  have h1 : (∑ j, a j * bayesTrueLikelihood c j 1) = bayesTrueNorm a c 1 := rfl
  rw [h1]
  exact div_self hn

/-- The weighted tree depth is zero when its initial weight is zero. -/
theorem treeDepth_zero {n : ℕ} (p : ℝ) :
    ∀ (tr : BoolQueryTree (Fin n) (Fin n)) (a : Fin n → ℝ) (W : ℝ), W = 0 →
      treeDepth p tr a W = 0 := by
  intro tr
  induction tr with
  | halt o =>
      intro a W hW
      simp [treeDepth]
  | ask c onFalse onTrue ihFalse ihTrue =>
      intro a W hW
      simp only [treeDepth]
      rw [hW]
      simp only [zero_mul]
      rw [ihFalse _ _ rfl, ihTrue _ _ rfl]
      ring

/-- A weighted-depth averaging identity for a subtree transfers to a normalized nonnegative
posterior whose nonzero normalizer recovers the unnormalized weights. -/
theorem branch_contrib_ne {n : ℕ} {W : ℝ} (sub : BoolQueryTree (Fin n) (Fin n))
    (ih : ∀ (a : Fin n → ℝ) (W : ℝ), (∀ j, 0 ≤ a j) → (∑ j, a j) = 1 →
      treeDepth 1 sub a W = W * (∑ j, a j * noiselessQueries j sub))
    (post : Fin n → ℝ) (norm : ℝ) (w : Fin n → ℝ)
    (hpost : ∀ j, 0 ≤ post j) (hpostsum : (∑ j, post j) = 1)
    (hnorm : norm ≠ 0) (hpostmul : ∀ j, norm * post j = w j) :
    treeDepth 1 sub post (W * norm) = W * (∑ j, w j * noiselessQueries j sub) := by
  rw [ih post (W * norm) hpost hpostsum]
  calc W * norm * (∑ j, post j * noiselessQueries j sub)
      = ∑ j, W * (norm * post j) * noiselessQueries j sub := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
    _ = W * (∑ j, (norm * post j) * noiselessQueries j sub) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
    _ = W * (∑ j, w j * noiselessQueries j sub) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by rw [hpostmul j])

/-- If the branch normalizer and all unnormalized weights vanish, both expressions for the
noiseless branch depth contribution are zero. -/
theorem branch_contrib_zero {n : ℕ} {W : ℝ} (sub : BoolQueryTree (Fin n) (Fin n))
    (post : Fin n → ℝ) (norm : ℝ) (w : Fin n → ℝ)
    (hnorm : norm = 0) (hw : ∀ j, w j = 0) :
    treeDepth 1 sub post (W * norm) = W * (∑ j, w j * noiselessQueries j sub) := by
  rw [hnorm, mul_zero, treeDepth_zero 1 sub post 0 rfl]
  simp [hw]

/-- At `p = 1`, weighted tree depth equals the initial weight times the prior-weighted noiseless
query count for a normalized nonnegative prior. -/
theorem treeDepth_one_eq {n : ℕ} (tr : BoolQueryTree (Fin n) (Fin n)) :
    ∀ (a : Fin n → ℝ) (W : ℝ), (∀ j, 0 ≤ a j) → (∑ j, a j) = 1 →
      treeDepth 1 tr a W = W * (∑ j, a j * noiselessQueries j tr) := by
  induction tr with
  | halt o =>
      intro a W ha hsum
      simp [treeDepth, noiselessQueries]
  | ask c onFalse onTrue ihFalse ihTrue =>
      intro a W ha hsum
      have hnorm : bayesFalseNorm a c 1 + bayesTrueNorm a c 1 = 1 := by
        have hpoint : ∀ j : Fin n,
            a j * bayesFalseLikelihood c j 1 + a j * bayesTrueLikelihood c j 1 = a j := by
          intro j
          rw [bayesFalseLikelihood_one, bayesTrueLikelihood_one]
          split_ifs <;> ring
        calc bayesFalseNorm a c 1 + bayesTrueNorm a c 1
            = (∑ j, a j * bayesFalseLikelihood c j 1) + ∑ j, a j * bayesTrueLikelihood c j 1 := rfl
          _ = ∑ j, (a j * bayesFalseLikelihood c j 1 + a j * bayesTrueLikelihood c j 1) := by
            rw [Finset.sum_add_distrib]
          _ = ∑ j, a j := Finset.sum_congr rfl (fun j _ => hpoint j)
          _ = 1 := hsum
      have hwF : ∀ j : Fin n, bayesFalseNorm a c 1 * bayesFalsePost a c 1 j
          = (if (c : ℕ) ≤ (j : ℕ) then 0 else a j) := by
        intro j
        have h1 : bayesFalseNorm a c 1 * bayesFalsePost a c 1 j
            = a j * bayesFalseLikelihood c j 1 := by
          unfold bayesFalsePost
          by_cases hn : bayesFalseNorm a c 1 = 0
          · rw [hn, zero_mul]
            have hle : a j * bayesFalseLikelihood c j 1 ≤ bayesFalseNorm a c 1 := by
              unfold bayesFalseNorm
              exact Finset.single_le_sum (f := fun m => a m * bayesFalseLikelihood c m 1)
                (fun m _ => mul_nonneg (ha m) (by
                  unfold bayesFalseLikelihood; split_ifs <;> norm_num)) (Finset.mem_univ j)
            rw [hn] at hle
            have hnonneg : 0 ≤ a j * bayesFalseLikelihood c j 1 :=
              mul_nonneg (ha j) (by unfold bayesFalseLikelihood; split_ifs <;> norm_num)
            linarith
          · field_simp
        rw [h1, bayesFalseLikelihood_one]
        by_cases h : (c : ℕ) ≤ (j : ℕ)
        · simp only [if_pos h]; ring
        · simp only [if_neg h]; ring
      have hwT : ∀ j : Fin n, bayesTrueNorm a c 1 * bayesTruePost a c 1 j
          = (if (c : ℕ) ≤ (j : ℕ) then a j else 0) := by
        intro j
        have h1 : bayesTrueNorm a c 1 * bayesTruePost a c 1 j
            = a j * bayesTrueLikelihood c j 1 := by
          unfold bayesTruePost
          by_cases hn : bayesTrueNorm a c 1 = 0
          · rw [hn, zero_mul]
            have hle : a j * bayesTrueLikelihood c j 1 ≤ bayesTrueNorm a c 1 := by
              unfold bayesTrueNorm
              exact Finset.single_le_sum (f := fun m => a m * bayesTrueLikelihood c m 1)
                (fun m _ => mul_nonneg (ha m) (by
                  unfold bayesTrueLikelihood; split_ifs <;> norm_num)) (Finset.mem_univ j)
            rw [hn] at hle
            have hnonneg : 0 ≤ a j * bayesTrueLikelihood c j 1 :=
              mul_nonneg (ha j) (by unfold bayesTrueLikelihood; split_ifs <;> norm_num)
            linarith
          · field_simp
        rw [h1, bayesTrueLikelihood_one]
        by_cases h : (c : ℕ) ≤ (j : ℕ)
        · simp only [if_pos h]; ring
        · simp only [if_neg h]; ring
      have hdepth : (∑ j : Fin n, a j * noiselessQueries j (.ask c onFalse onTrue))
          = (∑ j : Fin n, a j)
            + (∑ j : Fin n, (if (c : ℕ) ≤ (j : ℕ) then 0 else a j) * noiselessQueries j onFalse)
            + (∑ j : Fin n, (if (c : ℕ) ≤ (j : ℕ) then a j else 0) * noiselessQueries j onTrue) := by
        have hpoint : ∀ j ∈ (Finset.univ : Finset (Fin n)),
            a j * noiselessQueries j (.ask c onFalse onTrue)
              = a j + (if (c : ℕ) ≤ (j : ℕ) then a j * noiselessQueries j onTrue
                        else a j * noiselessQueries j onFalse) := by
          intro j _
          by_cases h : (c : ℕ) ≤ (j : ℕ)
          · rw [noiselessQueries_ask j c onFalse onTrue h]
            simp only [if_pos h, Nat.cast_add, Nat.cast_one]
            ring
          · rw [noiselessQueries_ask_neg j c onFalse onTrue h]
            simp only [if_neg h, Nat.cast_add, Nat.cast_one]
            ring
        have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n))
          (fun j : Fin n => (c : ℕ) ≤ (j : ℕ))
          (fun j => if (c : ℕ) ≤ (j : ℕ) then a j * noiselessQueries j onTrue
                     else a j * noiselessQueries j onFalse)
        have hT : (∑ j ∈ (Finset.univ : Finset (Fin n)).filter
                (fun j : Fin n => (c : ℕ) ≤ (j : ℕ)),
              (if (c : ℕ) ≤ (j : ℕ) then a j * noiselessQueries j onTrue
                else a j * noiselessQueries j onFalse))
            = ∑ j : Fin n, (if (c : ℕ) ≤ (j : ℕ) then a j else 0) * noiselessQueries j onTrue := by
          rw [Finset.sum_filter]
          have hconv : ∀ j ∈ (Finset.univ : Finset (Fin n)),
              (if (c : ℕ) ≤ (j : ℕ) then
                  (if (c : ℕ) ≤ (j : ℕ) then a j * noiselessQueries j onTrue
                    else a j * noiselessQueries j onFalse) else 0)
                = (if (c : ℕ) ≤ (j : ℕ) then a j else 0) * noiselessQueries j onTrue := by
            intro j _
            by_cases h : (c : ℕ) ≤ (j : ℕ)
            · simp [h]
            · simp [h]
          rw [Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl hconv]
        have hF : (∑ j ∈ (Finset.univ : Finset (Fin n)).filter
                (fun j : Fin n => ¬((c : ℕ) ≤ (j : ℕ))),
              (if (c : ℕ) ≤ (j : ℕ) then a j * noiselessQueries j onTrue
                else a j * noiselessQueries j onFalse))
            = ∑ j : Fin n, (if (c : ℕ) ≤ (j : ℕ) then 0 else a j) * noiselessQueries j onFalse := by
          rw [Finset.sum_filter]
          have hconv : ∀ j ∈ (Finset.univ : Finset (Fin n)),
              (if ¬((c : ℕ) ≤ (j : ℕ)) then
                  (if (c : ℕ) ≤ (j : ℕ) then a j * noiselessQueries j onTrue
                    else a j * noiselessQueries j onFalse) else 0)
                = (if (c : ℕ) ≤ (j : ℕ) then 0 else a j) * noiselessQueries j onFalse := by
            intro j _
            by_cases h : (c : ℕ) ≤ (j : ℕ)
            · simp [h]
            · simp [h]
          rw [Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl hconv]
        rw [Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl hpoint,
          Finset.sum_add_distrib, ← hsplit, hT, hF]
        ring

      have hFbranch : treeDepth 1 onFalse (bayesFalsePost a c 1) (W * bayesFalseNorm a c 1)
          = W * (∑ j : Fin n, (if (c : ℕ) ≤ (j : ℕ) then 0 else a j) * noiselessQueries j onFalse) := by
        by_cases hn : bayesFalseNorm a c 1 = 0
        · apply branch_contrib_zero onFalse (bayesFalsePost a c 1) (bayesFalseNorm a c 1)
            (fun j => if (c : ℕ) ≤ (j : ℕ) then 0 else a j)
          · exact hn
          · intro j
            by_cases h : (c : ℕ) ≤ (j : ℕ)
            · simp [h]
            · simp only [if_neg h]
              have hle : a j ≤ bayesFalseNorm a c 1 := by
                have h1 : a j * bayesFalseLikelihood c j 1 ≤ bayesFalseNorm a c 1 := by
                  unfold bayesFalseNorm
                  exact Finset.single_le_sum (f := fun m => a m * bayesFalseLikelihood c m 1)
                    (fun m _ => mul_nonneg (ha m) (by
                      unfold bayesFalseLikelihood; split_ifs <;> norm_num)) (Finset.mem_univ j)
                rw [bayesFalseLikelihood_one, if_neg h] at h1
                linarith
              rw [hn] at hle
              have haj : 0 ≤ a j := ha j
              linarith
        · apply branch_contrib_ne onFalse ihFalse (bayesFalsePost a c 1) (bayesFalseNorm a c 1)
            (fun j => if (c : ℕ) ≤ (j : ℕ) then 0 else a j)
          · exact bayesFalsePost_nonneg a c 1 ha (by norm_num) (by norm_num)
          · exact bayesFalsePost_sum_one a c ha hn
          · exact hn
          · intro j; exact hwF j
      have hTbranch : treeDepth 1 onTrue (bayesTruePost a c 1) (W * bayesTrueNorm a c 1)
          = W * (∑ j : Fin n, (if (c : ℕ) ≤ (j : ℕ) then a j else 0) * noiselessQueries j onTrue) := by
        by_cases hn : bayesTrueNorm a c 1 = 0
        · apply branch_contrib_zero onTrue (bayesTruePost a c 1) (bayesTrueNorm a c 1)
            (fun j => if (c : ℕ) ≤ (j : ℕ) then a j else 0)
          · exact hn
          · intro j
            by_cases h : (c : ℕ) ≤ (j : ℕ)
            · simp only [if_pos h]
              have hle : a j ≤ bayesTrueNorm a c 1 := by
                have h1 : a j * bayesTrueLikelihood c j 1 ≤ bayesTrueNorm a c 1 := by
                  unfold bayesTrueNorm
                  exact Finset.single_le_sum (f := fun m => a m * bayesTrueLikelihood c m 1)
                    (fun m _ => mul_nonneg (ha m) (by
                      unfold bayesTrueLikelihood; split_ifs <;> norm_num)) (Finset.mem_univ j)
                rw [bayesTrueLikelihood_one, if_pos h] at h1
                linarith
              rw [hn] at hle
              have haj : 0 ≤ a j := ha j
              linarith
            · simp [h]
        · apply branch_contrib_ne onTrue ihTrue (bayesTruePost a c 1) (bayesTrueNorm a c 1)
            (fun j => if (c : ℕ) ≤ (j : ℕ) then a j else 0)
          · exact bayesTruePost_nonneg a c 1 ha (by norm_num) (by norm_num)
          · exact bayesTruePost_sum_one a c ha hn
          · exact hn
          · intro j; exact hwT j
      simp only [treeDepth]
      rw [hFbranch, hTbranch, hdepth, hsum]
      ring

/-- For a nonempty search space, uniform expected queries at `p = 1` equal mean noiseless
queries. -/
theorem uniformExpectedQueries_one_eq {n : ℕ} (tr : BoolQueryTree (Fin n) (Fin n))
    (hn : 0 < n) :
    uniformExpectedQueries 1 tr = noiselessMeanQueries tr := by
  have h := treeDepth_one_eq tr (uniformPosterior (n := n)) 1
    (fun j => by simp [uniformPosterior]) (uniform_sum hn)
  rw [uniformExpectedQueries, noiselessMeanQueries, h]
  simp only [uniformPosterior]
  rw [← Finset.mul_sum]
  simp [noiselessDepthSum, noiselessDepthSumW]
  ring

/-- For a nonempty search space and correct-cell set, its cardinality times its base-two
logarithm is at most `n` times uniform expected queries at `p = 1`. -/
theorem corrected_corollary_2_7_mean_uniform {n : ℕ} (tr : BoolQueryTree (Fin n) (Fin n))
    (hn : 0 < n) (hcard : 0 < (correctCells tr).card) :
    (correctCells tr).card * (Real.log (correctCells tr).card / Real.log 2)
      ≤ (n : ℝ) * uniformExpectedQueries 1 tr := by
  have hmain := corrected_corollary_2_7_mean tr hcard
  have hbridge := uniformExpectedQueries_one_eq tr hn
  calc (correctCells tr).card * (Real.log (correctCells tr).card / Real.log 2)
      ≤ noiselessDepthSum tr := hmain
    _ = (n : ℝ) * uniformExpectedQueries 1 tr := by
      rw [hbridge, noiselessMeanQueries]
      field_simp

/-- For rational `0 < p < 1`, the rational prefix mass casts to the prefix mass of the real
record posterior. -/
theorem prefixMassRat_eq {n : ℕ} (hn : 0 < n) (p : ℚ) (hp : 0 < p) (hp1 : p < 1)
    (t : Record n) (i : Fin n) :
    (prefixMassRat p t i : ℝ) = prefixMass (recordPosterior t (p : ℝ)) i := by
  have hrec : ∀ j : Fin n, (recordPosteriorRat p t j : ℝ) = recordPosterior t (p : ℝ) j :=
    fun j => recordPosteriorRat_eq hn p hp hp1 t j
  calc (prefixMassRat p t i : ℝ)
      = ∑ j : Fin n, ((if j.val ≤ i.val then recordPosteriorRat p t j else 0 : ℚ) : ℝ) := by
        unfold prefixMassRat
        push_cast
        exact Finset.sum_congr rfl (fun j _ => rfl)
    _ = ∑ j : Fin n, (if j.val ≤ i.val then recordPosterior t (p : ℝ) j else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j.val ≤ i.val
        · simp only [hj, if_true]
          exact hrec j
        · simp only [hj, if_false]
          norm_num
    _ = prefixMass (recordPosterior t (p : ℝ)) i := rfl

/-- For rational `0 < p < 1`, the rational cut set equals the cut set of the real record
posterior at the cast threshold. -/
theorem cutSetRat_eq {n : ℕ} (hn : 0 < n) (p : ℚ) (hp : 0 < p) (hp1 : p < 1)
    (ε : ℚ) (t : Record n) :
    cutSetRat p ε t = cutSet (recordPosterior t (p : ℝ)) (ε : ℝ) := by
  have hpm : ∀ i, (prefixMassRat p t i : ℝ) = prefixMass (recordPosterior t (p : ℝ)) i :=
    fun i => prefixMassRat_eq hn p hp hp1 t i
  have hhalf : ((1 / 2 : ℚ) : ℝ) = (1 / 2 : ℝ) := by norm_num
  have hε : ((1 / 2 - ε : ℚ) : ℝ) = 1 / 2 - (ε : ℝ) := by
    rw [Rat.cast_sub, hhalf]
  unfold cutSetRat cutSet
  apply Finset.filter_congr
  intro i _
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · have h1' : ((1 / 2 - ε : ℚ) : ℝ) ≤ (prefixMassRat p t i : ℝ) :=
        (Rat.cast_le (K := ℝ)).mpr h1
      rw [hε, hpm i] at h1'
      exact h1'
    · have h2' : (prefixMassRat p t i : ℝ) < ((1 / 2 : ℚ) : ℝ) :=
        (Rat.cast_lt (K := ℝ)).mpr h2
      rw [hpm i, hhalf] at h2'
      exact h2'
  · rintro ⟨h1, h2⟩
    constructor
    · have h1' : ((1 / 2 - ε : ℚ) : ℝ) ≤ (prefixMassRat p t i : ℝ) := by
        rw [← hpm i] at h1
        rwa [← hε] at h1
      exact (Rat.cast_le (K := ℝ)).mp h1'
    · have h2' : (prefixMassRat p t i : ℝ) < ((1 / 2 : ℚ) : ℝ) := by
        rw [← hpm i] at h2
        rw [← hhalf] at h2
        exact h2
      exact (Rat.cast_lt (K := ℝ)).mp h2'

/-- For rational `0 < p < 1`, the rational stage-two cut equals the stage-two cut of the real
record posterior. -/
theorem stageTwoCutRat_eq {n : ℕ} (hn : 0 < n) (p : ℚ) (hp : 0 < p) (hp1 : p < 1)
    (ε : ℚ) (t : Record n) :
    stageTwoCutRat hn p ε t = stageTwoCut hn (recordPosterior t (p : ℝ)) (ε : ℝ) := by
  unfold stageTwoCutRat stageTwoCut
  rw [cutSetRat_eq hn p hp hp1 ε t]

/-- For rational `0 < p < 1`, rational and real adaptive cut selection agree. -/
theorem cutAtRat_eq {n : ℕ} (hn : 0 < n) (p : ℚ) (hp : 0 < p) (hp1 : p < 1)
    (ε : ℚ) (t : Record n) :
    cutAtRat hn p ε t = cutAt hn (p : ℝ) ε t := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hp1R : (p : ℝ) < 1 := by exact_mod_cast hp1
  have hpm : ∀ i, prefixMass (transportFold t (p : ℝ)) i
      = prefixMass (recordPosterior t (p : ℝ)) i := by
    intro i
    unfold prefixMass
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.val ≤ i.val
    · simp only [hj, if_true]
      exact transportFold_eq_recordPosterior hn (p : ℝ) hpR hp1R t j
    · simp only [hj, if_false]
  have hset : cutSet (transportFold t (p : ℝ)) (ε : ℝ)
      = cutSet (recordPosterior t (p : ℝ)) (ε : ℝ) := by
    unfold cutSet
    apply Finset.filter_congr
    intro i _
    constructor
    · rintro ⟨h1, h2⟩
      constructor
      · rw [← hpm i]; exact h1
      · rw [← hpm i]; exact h2
    · rintro ⟨h1, h2⟩
      constructor
      · rw [hpm i]; exact h1
      · rw [hpm i]; exact h2
  have hcut : cutAt hn (p : ℝ) ε t = stageTwoCut hn (recordPosterior t (p : ℝ)) (ε : ℝ) := by
    unfold cutAt stageTwoCut
    rw [hset]
  rw [cutAtRat, hcut]
  exact stageTwoCutRat_eq hn p hp hp1 ε t

/-- The binary symmetric channel probability for the ideal ordered-comparison answer equals
`answerLikelihood`. -/
theorem bscAnswerProb_eq_answerLikelihood {n : ℕ} (p : ℝ) (m c : Fin n) (b : Bool) :
    bscAnswerProb p (decide ((c : ℕ) ≤ (m : ℕ))) b = answerLikelihood m c p b := by
  cases b with
  | false =>
    by_cases h : (c : ℕ) ≤ (m : ℕ)
    · simp [bscAnswerProb, answerLikelihood, bayesFalseLikelihood, h]
    · simp [bscAnswerProb, answerLikelihood, bayesFalseLikelihood, h]
  | true =>
    by_cases h : (c : ℕ) ≤ (m : ℕ)
    · simp [bscAnswerProb, answerLikelihood, bayesTrueLikelihood, h]
    · simp [bscAnswerProb, answerLikelihood, bayesTrueLikelihood, h]

/-- For `0 ≤ p ≤ 1`, the squared amplitude of the diluted comparison oracle with initial answer
bit false equals `answerLikelihood`. -/
theorem dilutedOracle_answerLikelihood {n : ℕ} (p : ℝ) (m c : Fin n) (b : Bool)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (dilutedOracle (fun m => decide ((c : ℕ) ≤ (m : ℕ))) p (m, b) (m, false)).normSq
      = answerLikelihood m c p b := by
  rw [dilutedOracle_prob _ p hp0 hp1]
  have hb : (false != decide ((c : ℕ) ≤ (m : ℕ))) = decide ((c : ℕ) ≤ (m : ℕ)) := by
    cases h : decide ((c : ℕ) ≤ (m : ℕ)) <;> rfl
  rw [hb]
  exact bscAnswerProb_eq_answerLikelihood p m c b

/-- Collects agreement of rational and real cut selection and identification of comparison
answer likelihoods with channel probabilities and diluted-oracle squared amplitudes. -/
theorem clause16_cut_endpoint :
    (∀ (n : ℕ) (p : ℚ) (t : Record n) (hn : 0 < n) (hp : 0 < p) (hp1 : p < 1) (ε : ℚ),
      cutAtRat hn p ε t = cutAt hn (p : ℝ) ε t) ∧
    (∀ (n : ℕ) (p : ℚ) (t : Record n) (hn : 0 < n) (hp : 0 < p) (hp1 : p < 1) (ε : ℚ),
      stageTwoCutRat hn p ε t = stageTwoCut hn (recordPosterior t (p : ℝ)) (ε : ℝ)) ∧
    (∀ (n : ℕ) (p : ℝ) (m c : Fin n) (b : Bool),
      bscAnswerProb p (decide ((c : ℕ) ≤ (m : ℕ))) b = answerLikelihood m c p b) ∧
    (∀ (n : ℕ) (p : ℝ) (m c : Fin n) (b : Bool) (hp0 : 0 ≤ p) (hp1 : p ≤ 1),
      (dilutedOracle (fun m => decide ((c : ℕ) ≤ (m : ℕ))) p (m, b) (m, false)).normSq
        = answerLikelihood m c p b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n p t hn hp hp1 ε; exact cutAtRat_eq hn p hp hp1 ε t
  · intro n p t hn hp hp1 ε; exact stageTwoCutRat_eq hn p hp hp1 ε t
  · intro n p m c b; exact bscAnswerProb_eq_answerLikelihood p m c b
  · intro n p m c b hp0 hp1; exact dilutedOracle_answerLikelihood p m c b hp0 hp1

/-- For a normalized nonnegative prior, nonnegative initial weight, and `0 < p < 1`, every
deep-tree weight is nonnegative. -/
theorem treeDeepProb_nonneg {n : ℕ} (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∀ (tr : BoolQueryTree (Fin n) (Fin n)) (a : Fin n → ℝ) (W : ℝ),
      (∀ j, 0 ≤ a j) → (∑ j, a j) = 1 → 0 ≤ W →
      ∀ b : ℕ, 0 ≤ treeDeepProb p b tr a W := by
  intro tr
  induction tr with
  | halt o =>
    intro a W ha hsum hW b
    by_cases hb : b = 0
    · simp [treeDeepProb, hb, hW]
    · simp [treeDeepProb, hb]
  | ask c onFalse onTrue ihF ihT =>
    intro a W ha hsum hW b
    by_cases hb : b = 0
    · simp [treeDeepProb, hb, hW]
    · simp only [treeDeepProb, hb, ↓reduceIte]
      have hnF : 0 ≤ bayesFalseNorm a c p := by
        unfold bayesFalseNorm
        exact Finset.sum_nonneg fun j _ => mul_nonneg (ha j) (by
          unfold bayesFalseLikelihood; split_ifs <;> linarith)
      have hnT : 0 ≤ bayesTrueNorm a c p := by
        unfold bayesTrueNorm
        exact Finset.sum_nonneg fun j _ => mul_nonneg (ha j) (by
          unfold bayesTrueLikelihood; split_ifs <;> linarith)
      have h1 := ihF (bayesFalsePost a c p) (W * bayesFalseNorm a c p)
        (fun j => bayesFalsePost_nonneg a c p ha (le_of_lt hp) (le_of_lt hp1) j)
        (bayesFalsePost_sum a c p ha hsum hp hp1)
        (mul_nonneg hW hnF) (b - 1)
      have h2 := ihT (bayesTruePost a c p) (W * bayesTrueNorm a c p)
        (fun j => bayesTruePost_nonneg a c p ha (le_of_lt hp) (le_of_lt hp1) j)
        (bayesTruePost_sum a c p ha hsum hp hp1)
        (mul_nonneg hW hnT) (b - 1)
      linarith

/-- For thresholds `b ≤ cc`, `(cc - b)` times deep-tree weight at `cc + 1` is at most weighted
depth minus `b` times deep-tree weight at `b`. -/
theorem treeDepth_generalized_markov {n : ℕ} (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∀ (tr : BoolQueryTree (Fin n) (Fin n)) (a : Fin n → ℝ) (W : ℝ),
      (∀ j, 0 ≤ a j) → (∑ j, a j) = 1 → 0 ≤ W →
      ∀ (b cc : ℕ), b ≤ cc →
        ((cc : ℝ) - (b : ℝ)) * treeDeepProb p (cc + 1) tr a W
          ≤ treeDepth p tr a W - (b : ℝ) * treeDeepProb p b tr a W := by
  intro tr
  induction tr with
  | halt o =>
    intro a W ha hsum hW b cc hbc
    by_cases hb : b = 0
    · simp [treeDeepProb, treeDepth, hb]
    · simp [treeDeepProb, treeDepth, hb]
  | ask c onFalse onTrue ihF ihT =>
    intro a W ha hsum hW b cc hbc
    by_cases hb0 : b = 0
    · have hle : (cc : ℝ) * treeDeepProb p (cc + 1) (.ask c onFalse onTrue) a W
          ≤ treeDepth p (.ask c onFalse onTrue) a W := by
        have hM := treeDepth_markov p hp hp1 (.ask c onFalse onTrue) a W ha hsum hW (cc + 1)
        have hcast : ((cc + 1 : ℕ) : ℝ) = (cc : ℝ) + 1 := by push_cast; ring
        rw [hcast] at hM
        have hD0 := treeDeepProb_nonneg p hp hp1 (.ask c onFalse onTrue) a W ha hsum hW (cc + 1)
        have hM' : (cc : ℝ) * treeDeepProb p (cc + 1) (.ask c onFalse onTrue) a W
              + treeDeepProb p (cc + 1) (.ask c onFalse onTrue) a W
            ≤ treeDepth p (.ask c onFalse onTrue) a W := by
          calc (cc : ℝ) * treeDeepProb p (cc + 1) (.ask c onFalse onTrue) a W
                + treeDeepProb p (cc + 1) (.ask c onFalse onTrue) a W
              = ((cc : ℝ) + 1) * treeDeepProb p (cc + 1) (.ask c onFalse onTrue) a W := by ring
              _ ≤ treeDepth p (.ask c onFalse onTrue) a W := hM
        nlinarith [hM', hD0]
      have hbcast : (b : ℝ) = 0 := by rw [hb0]; norm_num
      rw [hbcast]
      simp only [sub_zero, zero_mul]
      exact hle
    · have hb1 : 1 ≤ b := by omega
      have hc1 : 1 ≤ cc := by omega
      have hnF : 0 ≤ bayesFalseNorm a c p := by
        unfold bayesFalseNorm
        exact Finset.sum_nonneg fun j _ => mul_nonneg (ha j) (by
          unfold bayesFalseLikelihood; split_ifs <;> linarith)
      have hnT : 0 ≤ bayesTrueNorm a c p := by
        unfold bayesTrueNorm
        exact Finset.sum_nonneg fun j _ => mul_nonneg (ha j) (by
          unfold bayesTrueLikelihood; split_ifs <;> linarith)
      have h1 := ihF (bayesFalsePost a c p) (W * bayesFalseNorm a c p)
        (fun j => bayesFalsePost_nonneg a c p ha (le_of_lt hp) (le_of_lt hp1) j)
        (bayesFalsePost_sum a c p ha hsum hp hp1)
        (mul_nonneg hW hnF) (b - 1) (cc - 1) (by omega)
      have h2 := ihT (bayesTruePost a c p) (W * bayesTrueNorm a c p)
        (fun j => bayesTruePost_nonneg a c p ha (le_of_lt hp) (le_of_lt hp1) j)
        (bayesTruePost_sum a c p ha hsum hp hp1)
        (mul_nonneg hW hnT) (b - 1) (cc - 1) (by omega)
      have hcc : cc - 1 + 1 = cc := by omega
      have hcastC : ((cc - 1 : ℕ) : ℝ) = (cc : ℝ) - 1 := by
        rw [Nat.cast_sub (R := ℝ) (m := 1) (n := cc) (by omega)]
        norm_num
      have hcastB : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
        rw [Nat.cast_sub (R := ℝ) (m := 1) (n := b) (by omega)]
        norm_num
      have hsum1 : ((cc : ℝ) - (b : ℝ)) * treeDeepProb p cc onFalse (bayesFalsePost a c p)
              (W * bayesFalseNorm a c p)
          ≤ treeDepth p onFalse (bayesFalsePost a c p) (W * bayesFalseNorm a c p)
            - ((b : ℝ) - 1) * treeDeepProb p (b - 1) onFalse (bayesFalsePost a c p)
              (W * bayesFalseNorm a c p) := by
        rw [hcc] at h1
        rw [hcastC, hcastB] at h1
        have hcc' : (cc : ℝ) - 1 - ((b : ℝ) - 1) = (cc : ℝ) - (b : ℝ) := by ring
        rw [hcc'] at h1
        exact h1
      have hsum2 : ((cc : ℝ) - (b : ℝ)) * treeDeepProb p cc onTrue (bayesTruePost a c p)
              (W * bayesTrueNorm a c p)
          ≤ treeDepth p onTrue (bayesTruePost a c p) (W * bayesTrueNorm a c p)
            - ((b : ℝ) - 1) * treeDeepProb p (b - 1) onTrue (bayesTruePost a c p)
              (W * bayesTrueNorm a c p) := by
        rw [hcc] at h2
        rw [hcastC, hcastB] at h2
        have hcc' : (cc : ℝ) - 1 - ((b : ℝ) - 1) = (cc : ℝ) - (b : ℝ) := by ring
        rw [hcc'] at h2
        exact h2
      have hle : treeDeepProb p b (.ask c onFalse onTrue) a W
          = treeDeepProb p (b - 1) onFalse (bayesFalsePost a c p) (W * bayesFalseNorm a c p)
            + treeDeepProb p (b - 1) onTrue (bayesTruePost a c p) (W * bayesTrueNorm a c p) := by
        simp only [treeDeepProb, hb0, ↓reduceIte]
      have hle2 : treeDeepProb p (cc + 1) (.ask c onFalse onTrue) a W
          = treeDeepProb p cc onFalse (bayesFalsePost a c p) (W * bayesFalseNorm a c p)
            + treeDeepProb p cc onTrue (bayesTruePost a c p) (W * bayesTrueNorm a c p) := by
        simp only [treeDeepProb, show cc + 1 ≠ 0 by omega, ↓reduceIte]
        have hsub : (cc + 1) - 1 = cc := by omega
        rw [hsub]
      have hle3 : treeDepth p (.ask c onFalse onTrue) a W
          = W + treeDepth p onFalse (bayesFalsePost a c p) (W * bayesFalseNorm a c p)
            + treeDepth p onTrue (bayesTruePost a c p) (W * bayesTrueNorm a c p) := by
        simp only [treeDepth]
      have hle4 : treeDeepProb p b (.ask c onFalse onTrue) a W ≤ W := by
        have h := treeDeepProb_le p hp hp1 (.ask c onFalse onTrue) a W ha hsum hW b
        simpa using! h
      rw [hle] at hle4
      rw [hle, hle2, hle3]
      nlinarith [hsum1, hsum2, hle4]

/-- For `b ≤ cc` and `0 < p < 1`, the uniform tail at `cc + 1`, multiplied by `cc - b`, is
bounded by mean queries minus `b` times the tail at `b`. -/
theorem uniform_generalized_markov {n : ℕ} (hn : 0 < n) (p : ℝ)
    (tr : BoolQueryTree (Fin n) (Fin n)) (hp : 0 < p) (hp1 : p < 1)
    (b cc : ℕ) (hbc : b ≤ cc) :
    ((cc : ℝ) - (b : ℝ)) * uniformTailProb p (cc + 1) tr
      ≤ uniformExpectedQueries p tr - (b : ℝ) * uniformTailProb p b tr := by
  have h := treeDepth_generalized_markov p hp hp1 tr (uniformPosterior (n := n)) 1
    (fun j => by
      have hnn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
      unfold uniformPosterior
      exact div_nonneg (by norm_num) hnn)
    (uniform_sum hn) (by norm_num) b cc hbc
  simpa [uniformTailProb, uniformExpectedQueries] using! h

/-- A mean bound `a` and tail lower bound `1 - β` at `b < c` give an upper tail bound `(a - b +
β * b) / (c - b)` at `c + 1`. This is the finite-tree form of [Ben-Or and Hassidim, Lemma
2.8][BenOrHassidim2007]. -/
theorem source_lemma_2_8 {n : ℕ} (hn : 0 < n) (p : ℝ)
    (tr : BoolQueryTree (Fin n) (Fin n)) (hp : 0 < p) (hp1 : p < 1)
    (b c : ℕ) (hbc : b < c) (a : ℝ) (ha : uniformExpectedQueries p tr ≤ a)
    (β : ℝ) (hprob : 1 - β ≤ uniformTailProb p b tr) :
    uniformTailProb p (c + 1) tr ≤ (a - (b : ℝ) + β * (b : ℝ)) / ((c : ℝ) - (b : ℝ)) := by
  have hgen := uniform_generalized_markov hn p tr hp hp1 b c (Nat.le_of_lt hbc)
  have hbcR : (b : ℝ) < (c : ℝ) := by exact_mod_cast hbc
  have hden : (0 : ℝ) < (c : ℝ) - (b : ℝ) := by linarith
  have hnum : uniformExpectedQueries p tr - (b : ℝ) * uniformTailProb p b tr
      ≤ a - (b : ℝ) + β * (b : ℝ) := by
    have hbR : (0 : ℝ) ≤ (b : ℝ) := by exact_mod_cast (Nat.zero_le b)
    nlinarith
  have hkey : uniformTailProb p (c + 1) tr * ((c : ℝ) - (b : ℝ))
      ≤ a - (b : ℝ) + β * (b : ℝ) := by linarith
  exact (le_div_iff₀ hden).mpr hkey

/-- Collects the Fano capacity lower bound, Markov and generalized Markov bounds, and the
refined tail estimate for uniform noisy query trees. -/
theorem walkGoal_noisy_corollary_2_7 :
    ∀ (n : ℕ) (p : ℝ) (tr : BoolQueryTree (Fin n) (Fin n)),
      (hn : 0 < n) → (hp : 1 / 2 < p) → (hp1 : p < 1) → (hn2 : 2 ≤ n) →
      (fanoCapacity (n := n) (uniformErrorProb p tr) p ≤ uniformExpectedQueries p tr) ∧
      (∀ (t : ℕ), (t : ℝ) * uniformTailProb p t tr ≤ uniformExpectedQueries p tr) ∧
      (∀ (b c : ℕ), b ≤ c →
        ((c : ℝ) - (b : ℝ)) * uniformTailProb p (c + 1) tr
          ≤ uniformExpectedQueries p tr - (b : ℝ) * uniformTailProb p b tr) ∧
      (∀ (b c : ℕ) (a β : ℝ), b < c →
        uniformExpectedQueries p tr ≤ a → 1 - β ≤ uniformTailProb p b tr →
        uniformTailProb p (c + 1) tr
          ≤ (a - (b : ℝ) + β * (b : ℝ)) / ((c : ℝ) - (b : ℝ))) := by
  intro n p tr hn hp hp1 hn2
  have hp0 : 0 < p := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fano_capacity_lower_bound p tr hp hp1 hn2
  · intro t; exact noisy_markov_tail hn p tr hp0 hp1 t
  · intro b c hbc; exact uniform_generalized_markov hn p tr hp0 hp1 b c hbc
  · intro b c a β hbc ha hprob
    exact source_lemma_2_8 hn p tr hp0 hp1 b c hbc a ha β hprob

/-- For `k < i`, an observation's likelihood ratio is `p / (1 - p)` for a true crossing, its
reciprocal for a false crossing, and one otherwise. -/
theorem answerLikelihood_ratio_cross {n : ℕ} (p : ℝ) (k i : Fin n) (obs : Comparison n)
    (hp : 0 < p) (hp1 : p < 1) (hki : k.val < i.val) :
    (answerLikelihood i obs.1 p obs.2 / answerLikelihood k obs.1 p obs.2)
      = if IsCrossing k i obs then (if obs.2 then p / (1 - p) else (1 - p) / p) else 1 := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hp1' : 1 - p ≠ 0 := by linarith
  by_cases hc : IsCrossing k i obs
  · rw [if_pos hc]
    obtain ⟨hk, hi⟩ := hc
    have hnk : ¬ obs.1.val ≤ k.val := Nat.not_le.mpr hk
    cases obs.2 with
    | true =>
      simp [answerLikelihood, bayesTrueLikelihood, hi, hnk, hp0, hp1']
    | false =>
      simp [answerLikelihood, bayesFalseLikelihood, hi, hnk, hp0, hp1']
  · rw [if_neg hc]
    by_cases habove : k.val < obs.1.val
    · have hi : ¬ obs.1.val ≤ i.val := by
        intro hcon
        exact hc ⟨habove, hcon⟩
      have hnk : ¬ obs.1.val ≤ k.val := Nat.not_le.mpr habove
      cases obs.2 with
      | true =>
        simp [answerLikelihood, bayesTrueLikelihood, hnk, hi, hp0, hp1']
      | false =>
        simp [answerLikelihood, bayesFalseLikelihood, hnk, hi, hp0, hp1']
    · have hlow : obs.1.val ≤ k.val := by omega
      have hi : obs.1.val ≤ i.val := by omega
      cases obs.2 with
      | true =>
        simp [answerLikelihood, bayesTrueLikelihood, hlow, hi, hp0, hp1']
      | false =>
        simp [answerLikelihood, bayesFalseLikelihood, hlow, hi, hp0, hp1']

/-- For `k < i` and `0 < p < 1`, the record ratio is the product of the true- and false-crossing
likelihood factors raised to their counts. -/
theorem recordRatio_eq_crossFactors {n : ℕ} (p : ℝ) (k i : Fin n) (hp : 0 < p) (hp1 : p < 1)
    (hki : k.val < i.val) (t : Record n) :
    recordRatio t k i p
      = (p / (1 - p)) ^ crossTrue k i t * ((1 - p) / p) ^ crossFalse k i t := by
  induction t with
  | nil =>
    simp [recordRatio, recordLikelihood, crossTrue, crossFalse]
  | cons obs t ih =>
    have hstep := answerLikelihood_ratio_cross p k i obs hp hp1 hki
    have hrec : recordLikelihood (obs :: t) i p
        = answerLikelihood i obs.1 p obs.2 * recordLikelihood t i p := by
      show (obs :: t).foldr (fun obs acc => answerLikelihood i obs.1 p obs.2 * acc) 1
          = answerLikelihood i obs.1 p obs.2 * recordLikelihood t i p
      rw [List.foldr_cons]
      rfl
    have hreck : recordLikelihood (obs :: t) k p
        = answerLikelihood k obs.1 p obs.2 * recordLikelihood t k p := by
      show (obs :: t).foldr (fun obs acc => answerLikelihood k obs.1 p obs.2 * acc) 1
          = answerLikelihood k obs.1 p obs.2 * recordLikelihood t k p
      rw [List.foldr_cons]
      rfl
    have hden1 : answerLikelihood k obs.1 p obs.2 ≠ 0 :=
      ne_of_gt (answerLikelihood_pos k obs.1 p obs.2 hp hp1)
    have hden2 : recordLikelihood t k p ≠ 0 := ne_of_gt (recordLikelihood_pos p hp hp1 t k)
    have hsplit : (answerLikelihood i obs.1 p obs.2 * recordLikelihood t i p) /
          (answerLikelihood k obs.1 p obs.2 * recordLikelihood t k p)
        = (answerLikelihood i obs.1 p obs.2 / answerLikelihood k obs.1 p obs.2)
          * (recordLikelihood t i p / recordLikelihood t k p) := by
      field_simp
    rw [recordRatio] at ih
    rw [recordRatio, hrec, hreck, hsplit, hstep, ih]
    by_cases hc : IsCrossing k i obs
    · cases hb : obs.2 with
      | true =>
        have hfac : (if IsCrossing k i obs then (if true = true then p / (1 - p) else (1 - p) / p) else 1)
            = p / (1 - p) := by
          simp [hc]
        have hct : crossTrue k i (obs :: t) = 1 + crossTrue k i t := by
          simp [crossTrue, hc, hb]
        have hcf : crossFalse k i (obs :: t) = crossFalse k i t := by
          simp [crossFalse, hc, hb]
        rw [hfac, hct, hcf, pow_add, pow_one]
        ac_rfl
      | false =>
        have hfac : (if IsCrossing k i obs then (if false = true then p / (1 - p) else (1 - p) / p) else 1)
            = (1 - p) / p := by
          simp [hc]
        have hct : crossTrue k i (obs :: t) = crossTrue k i t := by
          simp [crossTrue, hc, hb]
        have hcf : crossFalse k i (obs :: t) = 1 + crossFalse k i t := by
          simp [crossFalse, hc, hb]
        rw [hfac, hct, hcf, pow_add, pow_one]
        ac_rfl
    · have hfac : (if IsCrossing k i obs then (if obs.2 then p / (1 - p) else (1 - p) / p) else 1)
          = 1 := by
        simp [hc]
      have hct : crossTrue k i (obs :: t) = crossTrue k i t := by
        simp [crossTrue, hc]
      have hcf : crossFalse k i (obs :: t) = crossFalse k i t := by
        simp [crossFalse, hc]
      rw [hfac, hct, hcf, one_mul]

/-- The total number of true and false crossing observations is at most the record length. -/
theorem crossCount_le_length {n : ℕ} (k i : Fin n) : ∀ (t : Record n),
    crossTrue k i t + crossFalse k i t ≤ t.length := by
  intro t
  induction t with
  | nil => simp [crossTrue, crossFalse]
  | cons obs t ih =>
    by_cases hc : IsCrossing k i obs
    · cases hb : obs.2 with
      | true =>
        have hct : crossTrue k i (obs :: t) = 1 + crossTrue k i t := by
          simp [crossTrue, hc, hb]
        have hcf : crossFalse k i (obs :: t) = crossFalse k i t := by
          simp [crossFalse, hc, hb]
        rw [hct, hcf]
        simp only [List.length_cons]
        omega
      | false =>
        have hct : crossTrue k i (obs :: t) = crossTrue k i t := by
          simp [crossTrue, hc, hb]
        have hcf : crossFalse k i (obs :: t) = 1 + crossFalse k i t := by
          simp [crossFalse, hc, hb]
        rw [hct, hcf]
        simp only [List.length_cons]
        omega
    · have hct : crossTrue k i (obs :: t) = crossTrue k i t := by
        simp [crossTrue, hc]
      have hcf : crossFalse k i (obs :: t) = crossFalse k i t := by
        simp [crossFalse, hc]
      rw [hct, hcf]
      simp only [List.length_cons]
      omega

/-- If `p / (1 - p) > 1`, at least `x + r` true crossings and at most `x` false crossings force
the record ratio to be at least `(p / (1 - p)) ^ r`. -/
theorem crossFactors_ge {n : ℕ} (p : ℝ) (k i : Fin n) (hp : 0 < p) (hp1 : p < 1)
    (hki : k.val < i.val) (t : Record n) (x r : ℕ)
    (hqr : 1 < p / (1 - p)) :
    crossTrue k i t ≥ x + r → crossFalse k i t ≤ x →
      (p / (1 - p)) ^ r ≤ recordRatio t k i p := by
  have hratio := recordRatio_eq_crossFactors p k i hp hp1 hki t
  have hq0 : (0 : ℝ) ≤ p / (1 - p) := by positivity
  have hr0 : (0 : ℝ) ≤ (1 - p) / p := by positivity
  have hp0 : 0 < p := by linarith
  have hp1' : (1 - p) ≠ 0 := by linarith
  have hp1'' : 1 - p < p := by
    simpa using! (lt_div_iff₀ (by linarith)).mp hqr
  have hr0le1 : (1 - p) / p ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hprod : (p / (1 - p)) * ((1 - p) / p) = 1 := by
    field_simp
  intro hA hB
  rw [hratio]
  have hA' : (p / (1 - p)) ^ (x + r) ≤ (p / (1 - p)) ^ crossTrue k i t :=
    pow_le_pow_right₀ (by linarith) (by omega)
  have hB' : ((1 - p) / p) ^ x ≤ ((1 - p) / p) ^ crossFalse k i t :=
    pow_le_pow_of_le_one hr0 hr0le1 hB
  have hnonneg : 0 ≤ (p / (1 - p)) ^ crossTrue k i t := pow_nonneg hq0 _
  have hnonneg2 : 0 ≤ ((1 - p) / p) ^ crossFalse k i t := pow_nonneg hr0 _
  have hkey : (p / (1 - p)) ^ (x + r) * ((1 - p) / p) ^ x = (p / (1 - p)) ^ r := by
    calc (p / (1 - p)) ^ (x + r) * ((1 - p) / p) ^ x
        = (p / (1 - p)) ^ x * (p / (1 - p)) ^ r * ((1 - p) / p) ^ x := by rw [pow_add]
      _ = (p / (1 - p)) ^ r * ((p / (1 - p)) * ((1 - p) / p)) ^ x := by
        rw [mul_pow]
        ring
      _ = (p / (1 - p)) ^ r * 1 ^ x := by rw [hprod]
      _ = (p / (1 - p)) ^ r := by rw [one_pow, mul_one]
  calc (p / (1 - p)) ^ crossTrue k i t * ((1 - p) / p) ^ crossFalse k i t
      ≥ (p / (1 - p)) ^ (x + r) * ((1 - p) / p) ^ x := by
        exact mul_le_mul hA' hB' (pow_nonneg hr0 _) hnonneg
    _ = (p / (1 - p)) ^ r := hkey

/-- Collects the crossing-factor formula for record ratios, the record-length bound on crossing
counts, and a ratio lower bound from excess true crossings. -/
theorem clause13_crossing_endpoint :
    (∀ (n : ℕ) (p : ℝ) (k i : Fin n) (hp : 0 < p) (hp1 : p < 1) (hki : k.val < i.val)
      (t : Record n),
      recordRatio t k i p
        = (p / (1 - p)) ^ crossTrue k i t * ((1 - p) / p) ^ crossFalse k i t) ∧
    (∀ (n : ℕ) (k i : Fin n) (t : Record n),
      crossTrue k i t + crossFalse k i t ≤ t.length) ∧
    (∀ (n : ℕ) (p : ℝ) (k i : Fin n) (hp : 0 < p) (hp1 : p < 1) (hki : k.val < i.val)
      (t : Record n) (x r : ℕ) (hqr : 1 < p / (1 - p)),
      crossTrue k i t ≥ x + r → crossFalse k i t ≤ x →
        (p / (1 - p)) ^ r ≤ recordRatio t k i p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n p k i hp hp1 hki t; exact recordRatio_eq_crossFactors p k i hp hp1 hki t
  · intro n k i t; exact crossCount_le_length k i t
  · intro n p k i hp hp1 hki t x r hqr hA hB
    exact crossFactors_ge p k i hp hp1 hki t x r hqr hA hB

/-- Appending one observation increments the true-crossing count exactly when it is a crossing
with answer true. -/
theorem crossTrue_append {n : ℕ} (k i : Fin n) (t : Record n) (obs : Comparison n) :
    crossTrue k i (t ++ [obs])
      = crossTrue k i t + (if IsCrossing k i obs ∧ obs.2 = true then 1 else 0) := by
  induction t with
  | nil => simp [crossTrue]
  | cons o t ih =>
    have hcons : (o :: t) ++ [obs] = o :: (t ++ [obs]) := List.cons_append
    rw [hcons]
    simp only [crossTrue, ih]
    ring

/-- Appending one observation increments the false-crossing count exactly when it is a crossing
with answer false. -/
theorem crossFalse_append {n : ℕ} (k i : Fin n) (t : Record n) (obs : Comparison n) :
    crossFalse k i (t ++ [obs])
      = crossFalse k i t + (if IsCrossing k i obs ∧ obs.2 = false then 1 else 0) := by
  induction t with
  | nil => simp [crossFalse]
  | cons o t ih =>
    have hcons : (o :: t) ++ [obs] = o :: (t ++ [obs]) := List.cons_append
    rw [hcons]
    simp only [crossFalse, ih]
    ring

/-- An adaptive record extension adds the new observation's `stepScore` to the crossing score. -/
theorem crossScore_step {n : ℕ} (hn : 0 < n) (p ε : ℝ) (k i : Fin n) (t : Record n) (b : Bool) :
    crossScore k i (extend hn p ε t b)
      = crossScore k i t + stepScore k i (cutAt hn p ε t, b) := by
  have h1 := crossTrue_append k i t (cutAt hn p ε t, b)
  have h2 := crossFalse_append k i t (cutAt hn p ε t, b)
  simp only [extend, crossScore]
  rw [h1, h2]
  by_cases hc : IsCrossing k i (cutAt hn p ε t, b)
  · cases b with
    | true =>
      simp [stepScore, hc] <;> push_cast <;> ring
    | false =>
      simp [stepScore, hc] <;> push_cast <;> ring
  · cases b with
    | true =>
      have hct : ¬ IsCrossing k i (cutAt hn p ε t, true) := by
        intro h
        exact hc (by simpa only [Prod.fst] using! h)
      simp [stepScore, hc, hct] <;> push_cast <;> ring
    | false =>
      have hcf : ¬ IsCrossing k i (cutAt hn p ε t, false) := by
        intro h
        exact hc (by simpa only [Prod.fst] using! h)
      simp [stepScore, hc, hcf] <;> push_cast <;> ring

/-- An adaptive record extension adds the new observation's `stepCount` to the crossing count. -/
theorem crossCount_step {n : ℕ} (hn : 0 < n) (p ε : ℝ) (k i : Fin n) (t : Record n) (b : Bool) :
    crossCount k i (extend hn p ε t b)
      = crossCount k i t + stepCount k i (cutAt hn p ε t, b) := by
  have h1 := crossTrue_append k i t (cutAt hn p ε t, b)
  have h2 := crossFalse_append k i t (cutAt hn p ε t, b)
  simp only [extend, crossCount]
  rw [h1, h2]
  by_cases hc : IsCrossing k i (cutAt hn p ε t, b)
  · cases b with
    | true =>
      simp [stepCount, hc] <;> push_cast <;> ring
    | false =>
      simp [stepCount, hc] <;> push_cast <;> ring
  · cases b with
    | true =>
      have hct : ¬ IsCrossing k i (cutAt hn p ε t, true) := by
        intro h
        exact hc (by simpa only [Prod.fst] using! h)
      simp [stepCount, hc, hct] <;> push_cast <;> ring
    | false =>
      have hcf : ¬ IsCrossing k i (cutAt hn p ε t, false) := by
        intro h
        exact hc (by simpa only [Prod.fst] using! h)
      simp [stepCount, hc, hcf] <;> push_cast <;> ring

/-- When `u ≤ k < i` and `0 < p < 1`, the weighted one-step crossing score is `1 - 2 * p` at a
crossing cut and zero otherwise. -/
theorem crossScore_drift {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u k i : Fin n)
    (hp : 0 < p) (hp1 : p < 1) (huk : (u : ℕ) ≤ (k : ℕ)) (hki : (k : ℕ) < (i : ℕ))
    (t : Record n) :
    (∑ b : Bool, stepWeight hn p ε u t b * stepScore k i (cutAt hn p ε t, b))
      = (if IsCrossing k i (cutAt hn p ε t, true) then 1 - 2 * p else 0) := by
  have hsum : (∑ b : Bool, stepWeight hn p ε u t b) = 1 := by
    unfold stepWeight
    rw [Fintype.sum_bool]
    simpa [add_comm] using! answerLikelihood_sum u (cutAt hn p ε t) p
  by_cases hc : IsCrossing k i (cutAt hn p ε t, true)
  · have hc' : (k : ℕ) < (cutAt hn p ε t).val ∧ (cutAt hn p ε t).val ≤ (i : ℕ) := by
      simpa only [IsCrossing, Prod.fst] using! hc
    have hcu : ¬ ((cutAt hn p ε t).val ≤ (u : ℕ)) := by omega
    have hlikT : answerLikelihood u (cutAt hn p ε t) p true = 1 - p := by
      simp [answerLikelihood, bayesTrueLikelihood, hcu]
    have hlikF : answerLikelihood u (cutAt hn p ε t) p false = p := by
      simp [answerLikelihood, bayesFalseLikelihood, hcu]
    have hcf : IsCrossing k i (cutAt hn p ε t, false) := by
      simpa only [Prod.fst] using! hc
    simp only [Fintype.sum_bool, stepWeight]
    rw [hlikF, hlikT]
    simp [stepScore, hc, hcf] <;> ring
  · have hcf : ¬ IsCrossing k i (cutAt hn p ε t, false) := by
      intro h
      exact hc (by simpa only [Prod.fst] using! h)
    simp only [Fintype.sum_bool, stepWeight]
    simp [stepScore, hc, hcf] <;> ring

/-- For `0 < p < 1`, the weighted one-step crossing count is one at a crossing cut and zero
otherwise. -/
theorem crossCount_drift {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u k i : Fin n)
    (hp : 0 < p) (hp1 : p < 1) (t : Record n) :
    (∑ b : Bool, stepWeight hn p ε u t b * stepCount k i (cutAt hn p ε t, b))
      = (if IsCrossing k i (cutAt hn p ε t, true) then 1 else 0) := by
  have hsum : (∑ b : Bool, stepWeight hn p ε u t b) = 1 := by
    unfold stepWeight
    rw [Fintype.sum_bool]
    simpa [add_comm] using! answerLikelihood_sum u (cutAt hn p ε t) p
  by_cases hc : IsCrossing k i (cutAt hn p ε t, true)
  · have hcf : IsCrossing k i (cutAt hn p ε t, false) := by
      simpa only [Prod.fst] using! hc
    simp only [Fintype.sum_bool, stepWeight]
    simp [stepCount, hc, hcf]
    simpa [add_comm] using! answerLikelihood_sum u (cutAt hn p ε t) p
  · have hcf : ¬ IsCrossing k i (cutAt hn p ε t, false) := by
      intro h
      exact hc (by simpa only [Prod.fst] using! h)
    simp only [Fintype.sum_bool, stepWeight]
    simp [stepCount, hc, hcf] <;> ring

/-- For `k < i` and `0 < p < 1`, the log record ratio equals the crossing score times `Real.log
(p / (1 - p))`. -/
theorem crossRatio_log {n : ℕ} (p : ℝ) (k i : Fin n) (hp : 0 < p) (hp1 : p < 1)
    (hki : k.val < i.val) (t : Record n) :
    Real.log (recordRatio t k i p)
      = crossScore k i t * Real.log (p / (1 - p)) := by
  have hfac := recordRatio_eq_crossFactors p k i hp hp1 hki t
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hp1' : 1 - p ≠ 0 := by linarith
  have hq0 : p / (1 - p) ≠ 0 := by positivity
  have hr0 : (1 - p) / p ≠ 0 := by positivity
  have hpow0 : (p / (1 - p)) ^ crossTrue k i t ≠ 0 := by positivity
  have hrpow0 : ((1 - p) / p) ^ crossFalse k i t ≠ 0 := by positivity
  rw [hfac]
  rw [Real.log_mul hpow0 hrpow0, Real.log_pow, Real.log_pow]
  have hq : Real.log ((1 - p) / p) = -Real.log (p / (1 - p)) := by
    rw [Real.log_div (by linarith : (1 - p) ≠ 0) hp0, Real.log_div hp0 hp1']
    ring
  rw [hq]
  simp only [crossScore]
  push_cast
  ring

/-- A positive lower bound `R` on the record ratio gives `Real.log R ≤ crossScore k i t *
Real.log (p / (1 - p))`. -/
theorem crossScore_of_ratio_ge {n : ℕ} (p : ℝ) (k i : Fin n) (hp : 0 < p) (hp1 : p < 1)
    (hki : k.val < i.val) (t : Record n) {R : ℝ} (hR : 0 < R)
    (h : R ≤ recordRatio t k i p) :
    Real.log R ≤ crossScore k i t * Real.log (p / (1 - p)) := by
  have hpos : 0 < recordRatio t k i p := by
    unfold recordRatio
    exact div_pos (recordLikelihood_pos p hp hp1 t i) (recordLikelihood_pos p hp hp1 t k)
  have hmono : Real.log R ≤ Real.log (recordRatio t k i p) :=
    Real.strictMonoOn_log.monotoneOn hR hpos h
  rw [crossRatio_log p k i hp hp1 hki t] at hmono
  exact hmono

/-- The tree-weight functional preserves pointwise addition. -/
theorem treeWeight_add {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u : Fin n) (V W : Record n → ℝ) :
    ∀ (m : ℕ) (t : Record n),
      treeWeight hn p ε u (fun s => V s + W s) m t
        = treeWeight hn p ε u V m t + treeWeight hn p ε u W m t := by
  intro m
  induction m with
  | zero => intro t; simp only [treeWeight] <;> ring
  | succ m ih =>
    intro t
    simp only [treeWeight, Fintype.sum_bool]
    simp only [ih] <;> ring

/-- A constant real factor can be pulled out of the tree-weight functional. -/
theorem treeWeight_const_mul {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u : Fin n) (c : ℝ)
    (V : Record n → ℝ) :
    ∀ (m : ℕ) (t : Record n),
      treeWeight hn p ε u (fun s => c * V s) m t = c * treeWeight hn p ε u V m t := by
  intro m
  induction m with
  | zero => intro t; simp only [treeWeight] <;> ring
  | succ m ih =>
    intro t
    simp only [treeWeight, Fintype.sum_bool]
    simp only [ih] <;> ring

/-- Equal record functions give equal tree-weight evaluations. -/
theorem treeWeight_congr {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u : Fin n) {V W : Record n → ℝ}
    (h : V = W) :
    ∀ (m : ℕ) (t : Record n), treeWeight hn p ε u V m t = treeWeight hn p ε u W m t := by
  intro m
  induction m with
  | zero => intro t; simp only [treeWeight]; rw [h]
  | succ m ih =>
    intro t
    simp only [treeWeight, Fintype.sum_bool]
    simp only [ih, h]

/-- The tree-weight functional preserves pointwise subtraction. -/
theorem treeWeight_sub {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u : Fin n) (V W : Record n → ℝ) :
    ∀ (m : ℕ) (t : Record n),
      treeWeight hn p ε u (fun s => V s - W s) m t
        = treeWeight hn p ε u V m t - treeWeight hn p ε u W m t := by
  intro m
  induction m with
  | zero => intro t; simp only [treeWeight] <;> ring
  | succ m ih =>
    intro t
    simp only [treeWeight, Fintype.sum_bool]
    simp only [ih] <;> ring

/-- Expands the tree weight of `(f + c)^2` into the weighted second moment, cross term, and
constant term. -/
theorem treeWeight_sq_add {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u : Fin n) (f : Record n → ℝ) (c : ℝ) :
    ∀ (m : ℕ) (t : Record n),
      treeWeight hn p ε u (fun s => (f s + c) ^ 2) m t
        = treeWeight hn p ε u (fun s => f s ^ 2) m t
          + 2 * c * treeWeight hn p ε u f m t
          + c ^ 2 * treeWeight hn p ε u (fun _ => 1) m t := by
  intro m
  induction m with
  | zero => intro t; simp only [treeWeight] <;> ring
  | succ m ih =>
    intro t
    simp only [treeWeight, Fintype.sum_bool]
    simp only [ih] <;> ring

/-- For `0 < p < 1`, the tree-weight functional preserves pointwise inequalities. -/
theorem treeWeight_mono {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u : Fin n) (hp : 0 < p) (hp1 : p < 1)
    {V W : Record n → ℝ} (hVW : ∀ s, V s ≤ W s) :
    ∀ (m : ℕ) (t : Record n), treeWeight hn p ε u V m t ≤ treeWeight hn p ε u W m t := by
  intro m
  induction m with
  | zero => intro t; simp only [treeWeight]; exact hVW t
  | succ m ih =>
    intro t
    simp only [treeWeight]
    apply Finset.sum_le_sum
    intro b _
    apply mul_le_mul_of_nonneg_left (ih (extend hn p ε t b))
    unfold stepWeight
    exact le_of_lt (answerLikelihood_pos u (cutAt hn p ε t) p b hp hp1)

/-- The tree-weight functional evaluates a constant record function to that constant. -/
theorem treeWeight_const {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u : Fin n) (c : ℝ) :
    ∀ (m : ℕ) (t : Record n), treeWeight hn p ε u (fun _ => c) m t = c := by
  intro m t
  have hcongr : treeWeight hn p ε u (fun _ => c) m t
      = treeWeight hn p ε u (fun s => c * 1) m t := by
    refine treeWeight_congr hn p ε u (m := m) (t := t) ?_
    funext s; ring
  rw [hcongr, treeWeight_const_mul hn p ε u c (fun _ => 1) m t]
  have h1 := treeWeight_one hn p ε u m t
  rw [h1]
  ring

/-- The tree count of a predicate equals the tree weight of its zero-one indicator. -/
theorem treeCount_eq_indicator {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u : Fin n)
    (φ : Record n → Prop) :
    ∀ (m : ℕ) (t : Record n),
      treeCount hn p ε u φ m t = treeWeight hn p ε u (fun s => if φ s then 1 else 0) m t := by
  intro m
  induction m with
  | zero => intro t; simp [treeCount, treeWeight]
  | succ m ih =>
    intro t
    simp only [treeCount, treeWeight, Fintype.sum_bool]
    simp only [ih] <;> ring

/-- An adaptive extension changes the crossing martingale by the crossing score increment minus
`(1 - 2 * p)` times the crossing-count increment. -/
theorem crossMartingale_step {n : ℕ} (hn : 0 < n) (p ε : ℝ) (k i : Fin n) (t : Record n)
    (b : Bool) :
    crossMartingale p k i (extend hn p ε t b)
      = crossMartingale p k i t
        + (stepScore k i (cutAt hn p ε t, b)
          - (1 - 2 * p) * stepCount k i (cutAt hn p ε t, b)) := by
  have h1 := crossScore_step hn p ε k i t b
  have h2 := crossCount_step hn p ε k i t b
  simp only [crossMartingale]
  rw [h1, h2]
  ring

/-- For `u ≤ k < i` and `0 < p < 1`, the centered crossing-score increment has weighted mean
zero. -/
theorem crossStep_drift_zero {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u k i : Fin n)
    (hp : 0 < p) (hp1 : p < 1) (huk : (u : ℕ) ≤ (k : ℕ)) (hki : (k : ℕ) < (i : ℕ))
    (t : Record n) :
    (∑ b : Bool, stepWeight hn p ε u t b
      * (stepScore k i (cutAt hn p ε t, b)
        - (1 - 2 * p) * stepCount k i (cutAt hn p ε t, b))) = 0 := by
  by_cases hc : IsCrossing k i (cutAt hn p ε t, true)
  · have hc' : (k : ℕ) < (cutAt hn p ε t).val ∧ (cutAt hn p ε t).val ≤ (i : ℕ) := by
      simpa only [IsCrossing, Prod.fst] using! hc
    have hcu : ¬ ((cutAt hn p ε t).val ≤ (u : ℕ)) := by omega
    have hlikT : answerLikelihood u (cutAt hn p ε t) p true = 1 - p := by
      simp [answerLikelihood, bayesTrueLikelihood, hcu]
    have hlikF : answerLikelihood u (cutAt hn p ε t) p false = p := by
      simp [answerLikelihood, bayesFalseLikelihood, hcu]
    have hcf : IsCrossing k i (cutAt hn p ε t, false) := by
      simpa only [Prod.fst] using! hc
    simp only [Fintype.sum_bool, stepWeight]
    rw [hlikF, hlikT]
    simp [stepScore, stepCount, hc, hcf] <;> ring
  · have hcf : ¬ IsCrossing k i (cutAt hn p ε t, false) := by
      intro h
      exact hc (by simpa only [Prod.fst] using! h)
    simp only [Fintype.sum_bool, stepWeight]
    simp [stepScore, stepCount, hc, hcf] <;> ring

/-- For `u ≤ k < i` and `0 < p < 1`, the centered crossing increment has weighted second moment
`4 * p * (1 - p)` at a crossing cut and zero otherwise. -/
theorem crossStep_sq_drift {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u k i : Fin n)
    (hp : 0 < p) (hp1 : p < 1) (huk : (u : ℕ) ≤ (k : ℕ)) (hki : (k : ℕ) < (i : ℕ))
    (t : Record n) :
    (∑ b : Bool, stepWeight hn p ε u t b
      * (stepScore k i (cutAt hn p ε t, b)
        - (1 - 2 * p) * stepCount k i (cutAt hn p ε t, b)) ^ 2)
      = (if IsCrossing k i (cutAt hn p ε t, true) then 4 * p * (1 - p) else 0) := by
  by_cases hc : IsCrossing k i (cutAt hn p ε t, true)
  · have hc' : (k : ℕ) < (cutAt hn p ε t).val ∧ (cutAt hn p ε t).val ≤ (i : ℕ) := by
      simpa only [IsCrossing, Prod.fst] using! hc
    have hcu : ¬ ((cutAt hn p ε t).val ≤ (u : ℕ)) := by omega
    have hlikT : answerLikelihood u (cutAt hn p ε t) p true = 1 - p := by
      simp [answerLikelihood, bayesTrueLikelihood, hcu]
    have hlikF : answerLikelihood u (cutAt hn p ε t) p false = p := by
      simp [answerLikelihood, bayesFalseLikelihood, hcu]
    have hcf : IsCrossing k i (cutAt hn p ε t, false) := by
      simpa only [Prod.fst] using! hc
    simp only [Fintype.sum_bool, stepWeight]
    rw [hlikF, hlikT]
    simp [stepScore, stepCount, hc, hcf] <;> ring
  · have hcf : ¬ IsCrossing k i (cutAt hn p ε t, false) := by
      intro h
      exact hc (by simpa only [Prod.fst] using! h)
    simp only [Fintype.sum_bool, stepWeight]
    simp [stepScore, stepCount, hc, hcf] <;> ring

/-- For `u ≤ k < i` and `0 < p < 1`, the tree-weighted crossing martingale equals its initial
value. -/
theorem crossMartingale_tree {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u k i : Fin n)
    (hp : 0 < p) (hp1 : p < 1) (huk : (u : ℕ) ≤ (k : ℕ)) (hki : (k : ℕ) < (i : ℕ)) :
    ∀ (m : ℕ) (t : Record n),
      treeWeight hn p ε u (fun s => crossMartingale p k i s) m t = crossMartingale p k i t := by
  intro m
  induction m with
  | zero => intro t; simp only [treeWeight]
  | succ m ih =>
    intro t
    have hsum : (∑ b : Bool, stepWeight hn p ε u t b) = 1 := by
      unfold stepWeight
      rw [Fintype.sum_bool]
      simpa [add_comm] using! answerLikelihood_sum u (cutAt hn p ε t) p
    have hzero := crossStep_drift_zero hn p ε u k i hp hp1 huk hki t
    calc (∑ b : Bool, stepWeight hn p ε u t b
        * treeWeight hn p ε u (fun s => crossMartingale p k i s) m (extend hn p ε t b))
        = ∑ b : Bool, stepWeight hn p ε u t b
          * (crossMartingale p k i t
            + (stepScore k i (cutAt hn p ε t, b)
              - (1 - 2 * p) * stepCount k i (cutAt hn p ε t, b))) := by
          exact sum_congr'
              (fun b => by rw [ih (extend hn p ε t b), crossMartingale_step hn p ε k i t b])
      _ = crossMartingale p k i t * (∑ b : Bool, stepWeight hn p ε u t b)
          + (∑ b : Bool, stepWeight hn p ε u t b
            * (stepScore k i (cutAt hn p ε t, b)
              - (1 - 2 * p) * stepCount k i (cutAt hn p ε t, b))) := by
          simp only [Fintype.sum_bool]
          ring
      _ = crossMartingale p k i t := by rw [hsum, hzero]; ring

/-- The crossing martingale is zero at the empty record. -/
theorem crossMartingale_nil {n : ℕ} (p : ℝ) (k i : Fin n) :
    crossMartingale p k i [] = 0 := by
  simp [crossMartingale, crossScore, crossCount, crossTrue, crossFalse]

/-- For `u ≤ k < i` and `0 < p < 1`, the weighted next squared crossing martingale equals its
current square plus `4 * p * (1 - p)` at a crossing cut. -/
theorem stepSq_sum {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u k i : Fin n)
    (hp : 0 < p) (hp1 : p < 1) (huk : (u : ℕ) ≤ (k : ℕ)) (hki : (k : ℕ) < (i : ℕ))
    (t : Record n) :
    (∑ b : Bool, stepWeight hn p ε u t b
      * (crossMartingale p k i (extend hn p ε t b)) ^ 2)
      = (crossMartingale p k i t) ^ 2
        + (if IsCrossing k i (cutAt hn p ε t, true) then 4 * p * (1 - p) else 0) := by
  have hsum : (∑ b : Bool, stepWeight hn p ε u t b) = 1 := by
    unfold stepWeight
    rw [Fintype.sum_bool]
    simpa [add_comm] using! answerLikelihood_sum u (cutAt hn p ε t) p
  have hzero := crossStep_drift_zero hn p ε u k i hp hp1 huk hki t
  have hsq := crossStep_sq_drift hn p ε u k i hp hp1 huk hki t
  have hs : stepWeight hn p ε u t true + stepWeight hn p ε u t false = 1 := by
    simpa [Fintype.sum_bool] using! hsum
  have hz :
      (stepWeight hn p ε u t true
          * (stepScore k i (cutAt hn p ε t, true)
              - (1 - 2 * p) * stepCount k i (cutAt hn p ε t, true))
        + stepWeight hn p ε u t false
          * (stepScore k i (cutAt hn p ε t, false)
              - (1 - 2 * p) * stepCount k i (cutAt hn p ε t, false))) = 0 := by
    simpa [Fintype.sum_bool] using! hzero
  have hq :
      (stepWeight hn p ε u t true
          * (stepScore k i (cutAt hn p ε t, true)
              - (1 - 2 * p) * stepCount k i (cutAt hn p ε t, true)) ^ 2
        + stepWeight hn p ε u t false
          * (stepScore k i (cutAt hn p ε t, false)
              - (1 - 2 * p) * stepCount k i (cutAt hn p ε t, false)) ^ 2)
        = (if IsCrossing k i (cutAt hn p ε t, true) then 4 * p * (1 - p) else 0) := by
    simpa [Fintype.sum_bool] using! hsq
  simp only [Fintype.sum_bool]
  rw [crossMartingale_step hn p ε k i t true, crossMartingale_step hn p ε k i t false]
  have hsq' :
      stepWeight hn p ε u t true
          * (crossMartingale p k i t
              + (stepScore k i (cutAt hn p ε t, true)
                  - (1 - 2 * p) * stepCount k i (cutAt hn p ε t, true))) ^ 2
        + stepWeight hn p ε u t false
          * (crossMartingale p k i t
              + (stepScore k i (cutAt hn p ε t, false)
                  - (1 - 2 * p) * stepCount k i (cutAt hn p ε t, false))) ^ 2
        = (crossMartingale p k i t) ^ 2
            * (stepWeight hn p ε u t true + stepWeight hn p ε u t false)
          + 2 * (crossMartingale p k i t)
            * (stepWeight hn p ε u t true
                * (stepScore k i (cutAt hn p ε t, true)
                    - (1 - 2 * p) * stepCount k i (cutAt hn p ε t, true))
              + stepWeight hn p ε u t false
                * (stepScore k i (cutAt hn p ε t, false)
                    - (1 - 2 * p) * stepCount k i (cutAt hn p ε t, false)))
          + (stepWeight hn p ε u t true
                * (stepScore k i (cutAt hn p ε t, true)
                    - (1 - 2 * p) * stepCount k i (cutAt hn p ε t, true)) ^ 2
            + stepWeight hn p ε u t false
                * (stepScore k i (cutAt hn p ε t, false)
                    - (1 - 2 * p) * stepCount k i (cutAt hn p ε t, false)) ^ 2) := by
    ring
  rw [hsq', hs, hz, hq]
  ring

/-- For `u ≤ k < i` and `0 < p < 1`, the tree crossing variance equals the tree-weighted squared
crossing martingale minus its initial square. -/
theorem treeCrossVar_eq {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u k i : Fin n)
    (hp : 0 < p) (hp1 : p < 1) (huk : (u : ℕ) ≤ (k : ℕ)) (hki : (k : ℕ) < (i : ℕ)) :
    ∀ (m : ℕ) (t : Record n),
      treeCrossVar hn p ε u k i m t
        = treeWeight hn p ε u (fun s => (crossMartingale p k i s) ^ 2) m t
          - (crossMartingale p k i t) ^ 2 := by
  intro m
  induction m with
  | zero =>
    intro t
    simp only [treeCrossVar, treeWeight]
    ring
  | succ m ih =>
    intro t
    have hIH : ∀ b : Bool,
        treeCrossVar hn p ε u k i m (extend hn p ε t b)
          + (crossMartingale p k i (extend hn p ε t b)) ^ 2
          = treeWeight hn p ε u (fun s => (crossMartingale p k i s) ^ 2) m (extend hn p ε t b) := by
      intro b
      have h := ih (extend hn p ε t b)
      linarith
    have hsq :
        stepWeight hn p ε u t true * (crossMartingale p k i (extend hn p ε t true)) ^ 2
          + stepWeight hn p ε u t false * (crossMartingale p k i (extend hn p ε t false)) ^ 2
          = (crossMartingale p k i t) ^ 2
            + (if IsCrossing k i (cutAt hn p ε t, true) then 4 * p * (1 - p) else 0) := by
      simpa [Fintype.sum_bool] using! stepSq_sum hn p ε u k i hp hp1 huk hki t
    have hexp :
        (stepWeight hn p ε u t true
              * (treeCrossVar hn p ε u k i m (extend hn p ε t true)
                + (crossMartingale p k i (extend hn p ε t true)) ^ 2)
            + stepWeight hn p ε u t false
              * (treeCrossVar hn p ε u k i m (extend hn p ε t false)
                + (crossMartingale p k i (extend hn p ε t false)) ^ 2))
        = (stepWeight hn p ε u t true * treeCrossVar hn p ε u k i m (extend hn p ε t true)
            + stepWeight hn p ε u t false * treeCrossVar hn p ε u k i m (extend hn p ε t false))
          + (stepWeight hn p ε u t true * (crossMartingale p k i (extend hn p ε t true)) ^ 2
            + stepWeight hn p ε u t false * (crossMartingale p k i (extend hn p ε t false)) ^ 2) := by
      ring
    have hregroup :
        (stepWeight hn p ε u t true * treeCrossVar hn p ε u k i m (extend hn p ε t true)
          + stepWeight hn p ε u t false * treeCrossVar hn p ε u k i m (extend hn p ε t false))
          + (if IsCrossing k i (cutAt hn p ε t, true) then 4 * p * (1 - p) else 0)
        = ((stepWeight hn p ε u t true
              * (treeCrossVar hn p ε u k i m (extend hn p ε t true)
                + (crossMartingale p k i (extend hn p ε t true)) ^ 2)
            + stepWeight hn p ε u t false
              * (treeCrossVar hn p ε u k i m (extend hn p ε t false)
                + (crossMartingale p k i (extend hn p ε t false)) ^ 2))
            - (crossMartingale p k i t) ^ 2) := by
      rw [hexp, hsq]
      ring
    simp only [treeCrossVar, treeWeight, Fintype.sum_bool]
    rw [hregroup, hIH true, hIH false]

/-- For `0 < p < 1`, the tree crossing variance after `m` steps is at most `4 * p * (1 - p) *
m`. -/
theorem treeCrossVar_le {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u k i : Fin n)
    (hp : 0 < p) (hp1 : p < 1) :
    ∀ (m : ℕ) (t : Record n),
      treeCrossVar hn p ε u k i m t ≤ 4 * p * (1 - p) * (m : ℝ) := by
  intro m
  induction m with
  | zero =>
    intro t
    simp only [treeCrossVar, Nat.cast_zero, mul_zero]
    linarith
  | succ m ih =>
    intro t
    have hsum : (∑ b : Bool, stepWeight hn p ε u t b) = 1 := by
      unfold stepWeight
      rw [Fintype.sum_bool]
      simpa [add_comm] using! answerLikelihood_sum u (cutAt hn p ε t) p
    have hs : stepWeight hn p ε u t true + stepWeight hn p ε u t false = 1 := by
      simpa [Fintype.sum_bool] using! hsum
    have hstep : (if IsCrossing k i (cutAt hn p ε t, true) then 4 * p * (1 - p) else 0)
        ≤ 4 * p * (1 - p) := by
      by_cases hc : IsCrossing k i (cutAt hn p ε t, true)
      · simp [hc]
      · simp [hc]
        have hnonneg : 0 ≤ 4 * p * (1 - p) := by
          have := mul_nonneg (le_of_lt hp) (sub_nonneg.mpr (le_of_lt hp1))
          linarith
        linarith
    have hper : ∀ b : Bool,
        stepWeight hn p ε u t b * treeCrossVar hn p ε u k i m (extend hn p ε t b)
          ≤ stepWeight hn p ε u t b * (4 * p * (1 - p) * (m : ℝ)) := by
      intro b
      have hwb : 0 ≤ stepWeight hn p ε u t b := by
        unfold stepWeight
        exact le_of_lt (answerLikelihood_pos u (cutAt hn p ε t) p b hp hp1)
      exact mul_le_mul_of_nonneg_left (ih (extend hn p ε t b)) hwb
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    have h3 : (stepWeight hn p ε u t true * (4 * p * (1 - p) * (m : ℝ))
          + stepWeight hn p ε u t false * (4 * p * (1 - p) * (m : ℝ)))
          = 4 * p * (1 - p) * (m : ℝ) := by
      have hfac : stepWeight hn p ε u t true * (4 * p * (1 - p) * (m : ℝ))
          + stepWeight hn p ε u t false * (4 * p * (1 - p) * (m : ℝ))
          = (4 * p * (1 - p) * (m : ℝ))
            * (stepWeight hn p ε u t true + stepWeight hn p ε u t false) := by ring
      rw [hfac, hs]
      ring
    simp only [treeCrossVar, Fintype.sum_bool]
    have h1 := hper true
    have h2 := hper false
    rw [hcast]
    linarith

/-- When `p > 1 / 2`, the crossing martingale is at least the crossing score. -/
theorem crossScore_le_martingale {n : ℕ} (p : ℝ) (k i : Fin n) (hhalf : 1 / 2 < p)
    (t : Record n) :
    crossMartingale p k i t ≥ crossScore k i t := by
  have hcount : 0 ≤ crossCount k i t := by
    simp only [crossCount]
    have h1 : (0 : ℝ) ≤ (crossTrue k i t : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ (crossFalse k i t : ℝ) := Nat.cast_nonneg _
    linarith
  have hneg : 1 - 2 * p <= 0 := by linarith
  have hmul : (1 - 2 * p) * crossCount k i t <= 0 :=
    mul_nonpos_of_nonpos_of_nonneg hneg hcount
  simp only [crossMartingale]
  linarith

/-- For `u ≤ k < i` and `1 / 2 < p < 1`, the tree count of crossing scores at least `r > 0` is
at most `4 * p * (1 - p) * m / r^2`. -/
theorem crossScore_tail_bound {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u k i : Fin n) (r : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hhalf : 1 / 2 < p) (huk : (u : ℕ) ≤ (k : ℕ))
    (hki : (k : ℕ) < (i : ℕ)) (hr : 0 < r) :
    ∀ (m : ℕ),
      treeCount hn p ε u (fun t => r ≤ crossScore k i t) m []
        ≤ 4 * p * (1 - p) * (m : ℝ) / r ^ 2 := by
  intro m
  have hge : ∀ s : Record n, r ≤ crossScore k i s → r ≤ crossMartingale p k i s := by
    intro s hs
    have h1 := crossScore_le_martingale p k i hhalf s
    linarith
  have hind : ∀ s : Record n,
      (if r <= crossMartingale p k i s then 1 else 0)
        <= (crossMartingale p k i s) ^ 2 / r ^ 2 := by
    intro s
    by_cases h : r <= crossMartingale p k i s
    · rw [if_pos h]
      have hM2 : r ^ 2 <= (crossMartingale p k i s) ^ 2 := by nlinarith
      have h1 : 1 <= (crossMartingale p k i s) ^ 2 / r ^ 2 := by
        rw [le_div_iff₀ (by exact sq_pos_of_pos hr)]
        nlinarith
      linarith
    · rw [if_neg h]
      have h1 : 0 <= (crossMartingale p k i s) ^ 2 / r ^ 2 := by positivity
      linarith
  have h1 := treeCount_eq_indicator hn p ε u (fun t => r <= crossScore k i t) m []
  have h2 := treeWeight_mono hn p ε u hp hp1
    (V := fun s => if r <= crossScore k i s then 1 else 0)
    (W := fun s => if r <= crossMartingale p k i s then 1 else 0)
    (fun s => by

      by_cases hs : r <= crossScore k i s
      · have hm := hge s hs
        simp [hs, hm]
      · by_cases hm : r <= crossMartingale p k i s
        · simp [hs, hm]
        · simp [hs, hm]) m []
  have h3 := treeWeight_mono hn p ε u hp hp1
    (V := fun s => if r <= crossMartingale p k i s then 1 else 0)
    (W := fun s => (crossMartingale p k i s) ^ 2 / r ^ 2)
    (fun s => hind s) m []
  have h4 := treeWeight_const_mul hn p ε u (1 / r ^ 2)
    (fun s => (crossMartingale p k i s) ^ 2) m []
  have h5 := treeCrossVar_eq hn p ε u k i hp hp1 huk hki m []
  have h6 := crossMartingale_nil p k i
  have h7 := treeCrossVar_le hn p ε u k i hp hp1 m []
  have hvar : treeWeight hn p ε u (fun s => (crossMartingale p k i s) ^ 2) m []
      = treeCrossVar hn p ε u k i m [] := by
    rw [h5, h6]
    ring
  have hdiv : (fun s => (crossMartingale p k i s) ^ 2 / r ^ 2)
      = (fun s => (1 / r ^ 2) * (crossMartingale p k i s) ^ 2) := by
    funext s
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hfinal : (1 / r ^ 2) * treeCrossVar hn p ε u k i m []
      <= 4 * p * (1 - p) * (m : ℝ) / r ^ 2 := by
    have hmul : treeCrossVar hn p ε u k i m [] * (1 / r ^ 2)
        ≤ (4 * p * (1 - p) * (m : ℝ)) * (1 / r ^ 2) :=
      mul_le_mul_of_nonneg_right (a := 1 / r ^ 2) h7 (by positivity)
    calc (1 / r ^ 2) * treeCrossVar hn p ε u k i m []
        = treeCrossVar hn p ε u k i m [] * (1 / r ^ 2) := by ring
      _ <= (4 * p * (1 - p) * (m : ℝ)) * (1 / r ^ 2) := hmul
      _ = 4 * p * (1 - p) * (m : ℝ) / r ^ 2 := by ring
  calc treeCount hn p ε u (fun t => r <= crossScore k i t) m []
      = treeWeight hn p ε u (fun s => if r <= crossScore k i s then 1 else 0) m [] := h1
    _ <= treeWeight hn p ε u (fun s => if r <= crossMartingale p k i s then 1 else 0) m [] := h2
    _ <= treeWeight hn p ε u (fun s => (crossMartingale p k i s) ^ 2 / r ^ 2) m [] := h3
    _ = (1 / r ^ 2) * treeWeight hn p ε u (fun s => (crossMartingale p k i s) ^ 2) m [] := by
        rw [hdiv, h4]
    _ = (1 / r ^ 2) * treeCrossVar hn p ε u k i m [] := by rw [hvar]
    _ <= 4 * p * (1 - p) * (m : ℝ) / r ^ 2 := hfinal

/-- For `k < i` and `1 / 2 < p < 1`, a record ratio at least `(p / (1 - p)) ^ r` forces crossing
score at least `r`. -/
theorem crossScore_of_ratio_pow {n : ℕ} (p : ℝ) (k i : Fin n) (hp : 0 < p) (hp1 : p < 1)
    (hhalf : 1 / 2 < p) (hki : k.val < i.val) (t : Record n) (r : ℕ) :
    (p / (1 - p)) ^ r ≤ recordRatio t k i p → (r : ℝ) ≤ crossScore k i t := by
  intro h
  have hq : 1 < p / (1 - p) := by
    rw [lt_div_iff₀ (by linarith)]
    linarith
  have hR : 0 < (p / (1 - p)) ^ r := by positivity
  have hlog : 0 < Real.log (p / (1 - p)) := Real.log_pos hq
  have hstep := crossScore_of_ratio_ge p k i hp hp1 hki t hR h
  rw [Real.log_pow] at hstep
  nlinarith

/-- For `u ≤ k < i`, `1 / 2 < p < 1`, and positive integer `r`, the tree count of ratios at
least `(p / (1 - p)) ^ r` is at most `4 * p * (1 - p) * m / r^2`. -/
theorem crossScore_ratio_tail {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u k i : Fin n) (r : ℕ)
    (hp : 0 < p) (hp1 : p < 1) (hhalf : 1 / 2 < p) (huk : (u : ℕ) ≤ (k : ℕ))
    (hki : (k : ℕ) < (i : ℕ)) (hr : 0 < r) :
    ∀ (m : ℕ),
      treeCount hn p ε u (fun t => (p / (1 - p)) ^ r <= recordRatio t k i p) m []
        <= 4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2 := by
  intro m
  have hmono := treeCount_mono hn p ε u
    (ψ := fun t => (r : ℝ) <= crossScore k i t)
    (fun t ht => crossScore_of_ratio_pow p k i hp hp1 hhalf hki t r ht) hp hp1 m []
  have h1 := crossScore_tail_bound hn p ε u k i (r : ℝ) hp hp1 hhalf huk hki
    (by exact_mod_cast (Nat.cast_pos.mpr hr)) m
  linarith

/-- If `4 * p * (1 - p) * m ≤ δ * r^2`, the crossing-score tail count is at most `δ` under the
stated ordering and noise hypotheses. -/
theorem crossScore_tail_calibration {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u k i : Fin n)
    (δ : ℝ) (r : ℕ)
    (hp : 0 < p) (hp1 : p < 1) (hhalf : 1 / 2 < p) (huk : (u : ℕ) ≤ (k : ℕ))
    (hki : (k : ℕ) < (i : ℕ)) (hr : 0 < r) :
    ∀ (m : ℕ),
      4 * p * (1 - p) * (m : ℝ) <= δ * (r : ℝ) ^ 2 ->
        treeCount hn p ε u (fun t => (r : ℝ) <= crossScore k i t) m [] <= δ := by
  intro m hcal
  have h1 := crossScore_tail_bound hn p ε u k i (r : ℝ) hp hp1 hhalf huk hki
    (by exact_mod_cast (Nat.cast_pos.mpr hr)) m
  have hr2 : 0 < (r : ℝ) ^ 2 := by positivity
  rw [le_div_iff₀ hr2] at h1
  have h2 : treeCount hn p ε u (fun t => (r : ℝ) <= crossScore k i t) m [] * (r : ℝ) ^ 2
      <= δ * (r : ℝ) ^ 2 := by linarith
  have h3 : (r : ℝ) ^ 2 * treeCount hn p ε u (fun t => (r : ℝ) <= crossScore k i t) m []
      <= (r : ℝ) ^ 2 * δ := by simpa [mul_comm] using! h2
  exact le_of_mul_le_mul_left h3 hr2

/-- Under the stated window separation and threshold conditions, the heavy-cell and preceding
light-witness event has tree count at most the window cardinality times `4 * p * (1 - p) * m
/ r^2`. -/
theorem window_light_tail_bound {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u i : Fin n) (l r : ℕ)
    (hp : 0 < p) (hp1 : p < 1) (hhalf : 1 / 2 < p) (hε : 0 < ε) (hl : 0 < l)
    (hil : l <= (i : ℕ)) (hul : (u : ℕ) + l <= (i : ℕ)) (hr : 0 < r)
    (hthr : ε * (l : ℝ) >= (p / (1 - p)) ^ r) :
    ∀ (m : ℕ),
      treeCount hn p ε u
        (fun t => ε <= recordPosterior t p i ∧
          ∃ k, k ∈ windowCells i l ∧ recordPosterior t p k <= 1 / (l : ℝ)) m []
        <= (windowCells i l).card * (4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2) := by
  intro m
  let φ : Fin n → Record n → Prop := fun k t =>
    ε <= recordPosterior t p i ∧ (p / (1 - p)) ^ r <= recordRatio t k i p
  have hmono1 : treeCount hn p ε u
        (fun t => ε <= recordPosterior t p i ∧
          ∃ k, k ∈ windowCells i l ∧ recordPosterior t p k <= 1 / (l : ℝ)) m []
      <= treeCount hn p ε u
        (fun t => ∃ k ∈ windowCells i l, φ k t) m [] :=
    treeCount_mono hn p ε u (fun t ht => by
      obtain ⟨k, hk, hlight⟩ := ht.2
      have hratio := halt_forces_light_ratio hn p ε hp hp1 t i k l hl hε ht.1 hlight
      exact ⟨k, hk, ht.1, le_trans hthr hratio⟩) hp hp1 m []
  have hunion := treeCount_exists_le_finset hn p ε u (windowCells i l) φ hp hp1 m []
  have hsum := treeCountFinset_eq_sum hn p ε u (windowCells i l) φ m []
  have hper : ∀ k ∈ windowCells i l,
      treeCount hn p ε u (φ k) m []
        <= 4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2 := by
    intro k hk
    have hku : (u : ℕ) <= (k : ℕ) := by
      have hk1 := (Finset.mem_filter.mp hk).2.1
      omega
    have hki : (k : ℕ) < (i : ℕ) := (Finset.mem_filter.mp hk).2.2
    have hm := treeCount_mono hn p ε u
      (φ := fun t => ε <= recordPosterior t p i ∧ (p / (1 - p)) ^ r <= recordRatio t k i p)
      (ψ := fun t => (p / (1 - p)) ^ r <= recordRatio t k i p)
      (fun t ht => ht.2) hp hp1 m []
    have hrt := crossScore_ratio_tail hn p ε u k i r hp hp1 hhalf hku hki hr m
    linarith
  calc treeCount hn p ε u
        (fun t => ε <= recordPosterior t p i ∧
          ∃ k, k ∈ windowCells i l ∧ recordPosterior t p k <= 1 / (l : ℝ)) m []
      <= treeCount hn p ε u (fun t => ∃ k ∈ windowCells i l, φ k t) m [] := hmono1
    _ <= treeCountFinset hn p ε u (windowCells i l) φ m [] := hunion
    _ = ∑ k ∈ windowCells i l, treeCount hn p ε u (φ k) m [] := hsum
    _ <= ∑ k ∈ windowCells i l, 4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro k hk
        exact hper k hk
    _ = (windowCells i l).card * (4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2) := by
        rw [Finset.sum_const]
        simp [nsmul_eq_mul]

/-- Collects the crossing variance identity, its linear growth bound, score and ratio tail
bounds, and the resulting preceding-window concentration estimate. -/
theorem clause13_concentration_endpoint :
    (∀ (n : ℕ) (p ε : ℝ) (u k i : Fin n) (hn : 0 < n) (hp : 0 < p) (hp1 : p < 1)
      (huk : (u : ℕ) ≤ (k : ℕ)) (hki : (k : ℕ) < (i : ℕ)) (m : ℕ) (t : Record n),
      treeCrossVar hn p ε u k i m t
        = treeWeight hn p ε u (fun s => (crossMartingale p k i s) ^ 2) m t
          - (crossMartingale p k i t) ^ 2) ∧
    (∀ (n : ℕ) (p ε : ℝ) (u k i : Fin n) (hn : 0 < n) (hp : 0 < p) (hp1 : p < 1)
      (m : ℕ) (t : Record n),
      treeCrossVar hn p ε u k i m t ≤ 4 * p * (1 - p) * (m : ℝ)) ∧
    (∀ (n : ℕ) (p ε : ℝ) (u k i : Fin n) (hn : 0 < n) (r : ℝ) (hp : 0 < p) (hp1 : p < 1)
      (hhalf : 1 / 2 < p) (huk : (u : ℕ) ≤ (k : ℕ)) (hki : (k : ℕ) < (i : ℕ))
      (hr : 0 < r) (m : ℕ),
      treeCount hn p ε u (fun t => r ≤ crossScore k i t) m []
        ≤ 4 * p * (1 - p) * (m : ℝ) / r ^ 2) ∧
    (∀ (n : ℕ) (p ε : ℝ) (u k i : Fin n) (hn : 0 < n) (r : ℕ) (hp : 0 < p) (hp1 : p < 1)
      (hhalf : 1 / 2 < p) (huk : (u : ℕ) ≤ (k : ℕ)) (hki : (k : ℕ) < (i : ℕ))
      (hr : 0 < r) (m : ℕ),
      treeCount hn p ε u (fun t => (p / (1 - p)) ^ r ≤ recordRatio t k i p) m []
        ≤ 4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2) ∧
    (∀ (n : ℕ) (p ε : ℝ) (u i : Fin n) (hn : 0 < n) (l r : ℕ) (hp : 0 < p) (hp1 : p < 1)
      (hhalf : 1 / 2 < p) (hε : 0 < ε) (hl : 0 < l) (hil : l ≤ (i : ℕ))
      (hul : (u : ℕ) + l ≤ (i : ℕ)) (hr : 0 < r)
      (hthr : ε * (l : ℝ) ≥ (p / (1 - p)) ^ r) (m : ℕ),
      treeCount hn p ε u
        (fun t => ε ≤ recordPosterior t p i ∧
          ∃ k, k ∈ windowCells i l ∧ recordPosterior t p k ≤ 1 / (l : ℝ)) m []
        ≤ (windowCells i l).card * (4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n p ε u k i hn hp hp1 huk hki m t
    exact treeCrossVar_eq hn p ε u k i hp hp1 huk hki m t
  · intro n p ε u k i hn hp hp1 m t
    exact treeCrossVar_le hn p ε u k i hp hp1 m t
  · intro n p ε u k i hn r hp hp1 hhalf huk hki hr m
    exact crossScore_tail_bound hn p ε u k i r hp hp1 hhalf huk hki hr m
  · intro n p ε u k i hn r hp hp1 hhalf huk hki hr m
    exact crossScore_ratio_tail hn p ε u k i r hp hp1 hhalf huk hki hr m
  · intro n p ε u i hn l r hp hp1 hhalf hε hl hil hul hr hthr m
    exact window_light_tail_bound hn p ε u i l r hp hp1 hhalf hε hl hil hul hr hthr m

/-- An adaptive record extension adds the new observation's `stepUpperScore` to the upper
crossing score. -/
theorem upperScore_step {n : ℕ} (hn : 0 < n) (p ε : ℝ) (i k : Fin n) (t : Record n) (b : Bool) :
    upperScore i k (extend hn p ε t b)
      = upperScore i k t + stepUpperScore i k (cutAt hn p ε t, b) := by
  have h1 := crossTrue_append i k t (cutAt hn p ε t, b)
  have h2 := crossFalse_append i k t (cutAt hn p ε t, b)
  simp only [extend, upperScore]
  rw [h1, h2]
  by_cases hc : IsCrossing i k (cutAt hn p ε t, b)
  · cases b with
    | true =>
      simp [stepUpperScore, hc] <;> push_cast <;> ring
    | false =>
      simp [stepUpperScore, hc] <;> push_cast <;> ring
  · cases b with
    | true =>
      have hct : ¬ IsCrossing i k (cutAt hn p ε t, true) := by
        intro h
        exact hc (by simpa only [Prod.fst] using! h)
      simp [stepUpperScore, hc, hct] <;> push_cast <;> ring
    | false =>
      have hcf : ¬ IsCrossing i k (cutAt hn p ε t, false) := by
        intro h
        exact hc (by simpa only [Prod.fst] using! h)
      simp [stepUpperScore, hc, hcf] <;> push_cast <;> ring

/-- An adaptive extension changes the upper martingale by `stepUpperScore + (2 * p - 1) *
stepCount` for the new observation. -/
theorem upperMartingale_step {n : ℕ} (hn : 0 < n) (p ε : ℝ) (i k : Fin n) (t : Record n)
    (b : Bool) :
    upperMartingale p i k (extend hn p ε t b)
      = upperMartingale p i k t
        + (stepUpperScore i k (cutAt hn p ε t, b)
          + (2 * p - 1) * stepCount i k (cutAt hn p ε t, b)) := by
  have h1 := upperScore_step hn p ε i k t b
  have h2 := crossCount_step hn p ε i k t b
  simp only [upperMartingale]
  rw [h1, h2]
  ring

/-- For `i < k ≤ u` and `0 < p < 1`, the centered upper-score increment has weighted mean zero. -/
theorem upperStep_drift_zero {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u i k : Fin n)
    (hp : 0 < p) (hp1 : p < 1) (hku : (k : ℕ) ≤ (u : ℕ)) (hik : (i : ℕ) < (k : ℕ))
    (t : Record n) :
    (∑ b : Bool, stepWeight hn p ε u t b
      * (stepUpperScore i k (cutAt hn p ε t, b)
        + (2 * p - 1) * stepCount i k (cutAt hn p ε t, b))) = 0 := by
  by_cases hc : IsCrossing i k (cutAt hn p ε t, true)
  · have hc' : (i : ℕ) < (cutAt hn p ε t).val ∧ (cutAt hn p ε t).val ≤ (k : ℕ) := by
      simpa only [IsCrossing, Prod.fst] using! hc
    have hcu : (cutAt hn p ε t).val ≤ (u : ℕ) := by omega
    have hlikT : answerLikelihood u (cutAt hn p ε t) p true = p := by
      simp [answerLikelihood, bayesTrueLikelihood, hcu]
    have hlikF : answerLikelihood u (cutAt hn p ε t) p false = 1 - p := by
      simp [answerLikelihood, bayesFalseLikelihood, hcu]
    have hcf : IsCrossing i k (cutAt hn p ε t, false) := by
      simpa only [Prod.fst] using! hc
    simp only [Fintype.sum_bool, stepWeight]
    rw [hlikF, hlikT]
    simp [stepUpperScore, stepCount, hc, hcf] <;> ring
  · have hcf : ¬ IsCrossing i k (cutAt hn p ε t, false) := by
      intro h
      exact hc (by simpa only [Prod.fst] using! h)
    simp only [Fintype.sum_bool, stepWeight]
    simp [stepUpperScore, stepCount, hc, hcf] <;> ring

/-- For `i < k ≤ u` and `0 < p < 1`, the centered upper-score increment has weighted second
moment `4 * p * (1 - p)` at a crossing cut and zero otherwise. -/
theorem upperStep_sq_drift {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u i k : Fin n)
    (hp : 0 < p) (hp1 : p < 1) (hku : (k : ℕ) ≤ (u : ℕ)) (hik : (i : ℕ) < (k : ℕ))
    (t : Record n) :
    (∑ b : Bool, stepWeight hn p ε u t b
      * (stepUpperScore i k (cutAt hn p ε t, b)
        + (2 * p - 1) * stepCount i k (cutAt hn p ε t, b)) ^ 2)
      = (if IsCrossing i k (cutAt hn p ε t, true) then 4 * p * (1 - p) else 0) := by
  by_cases hc : IsCrossing i k (cutAt hn p ε t, true)
  · have hc' : (i : ℕ) < (cutAt hn p ε t).val ∧ (cutAt hn p ε t).val ≤ (k : ℕ) := by
      simpa only [IsCrossing, Prod.fst] using! hc
    have hcu : (cutAt hn p ε t).val ≤ (u : ℕ) := by omega
    have hlikT : answerLikelihood u (cutAt hn p ε t) p true = p := by
      simp [answerLikelihood, bayesTrueLikelihood, hcu]
    have hlikF : answerLikelihood u (cutAt hn p ε t) p false = 1 - p := by
      simp [answerLikelihood, bayesFalseLikelihood, hcu]
    have hcf : IsCrossing i k (cutAt hn p ε t, false) := by
      simpa only [Prod.fst] using! hc
    simp only [Fintype.sum_bool, stepWeight]
    rw [hlikF, hlikT]
    simp [stepUpperScore, stepCount, hc, hcf] <;> ring
  · have hcf : ¬ IsCrossing i k (cutAt hn p ε t, false) := by
      intro h
      exact hc (by simpa only [Prod.fst] using! h)
    simp only [Fintype.sum_bool, stepWeight]
    simp [stepUpperScore, stepCount, hc, hcf] <;> ring

/-- The upper martingale is zero at the empty record. -/
theorem upperMartingale_nil {n : ℕ} (p : ℝ) (i k : Fin n) :
    upperMartingale p i k [] = 0 := by
  simp [upperMartingale, upperScore, crossScore, crossCount, crossTrue, crossFalse]

/-- For `i < k ≤ u` and `0 < p < 1`, the tree-weighted upper martingale equals its initial
value. -/
theorem upperMartingale_tree {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u i k : Fin n)
    (hp : 0 < p) (hp1 : p < 1) (hku : (k : ℕ) ≤ (u : ℕ)) (hik : (i : ℕ) < (k : ℕ)) :
    ∀ (m : ℕ) (t : Record n),
      treeWeight hn p ε u (fun s => upperMartingale p i k s) m t = upperMartingale p i k t := by
  intro m
  induction m with
  | zero => intro t; simp only [treeWeight]
  | succ m ih =>
    intro t
    have hsum : (∑ b : Bool, stepWeight hn p ε u t b) = 1 := by
      unfold stepWeight
      rw [Fintype.sum_bool]
      simpa [add_comm] using! answerLikelihood_sum u (cutAt hn p ε t) p
    have hzero := upperStep_drift_zero hn p ε u i k hp hp1 hku hik t
    calc (∑ b : Bool, stepWeight hn p ε u t b
        * treeWeight hn p ε u (fun s => upperMartingale p i k s) m (extend hn p ε t b))
        = ∑ b : Bool, stepWeight hn p ε u t b
          * (upperMartingale p i k t
            + (stepUpperScore i k (cutAt hn p ε t, b)
              + (2 * p - 1) * stepCount i k (cutAt hn p ε t, b))) := by
          exact sum_congr' (fun b => by
            rw [ih (extend hn p ε t b), upperMartingale_step hn p ε i k t b])
      _ = upperMartingale p i k t * (∑ b : Bool, stepWeight hn p ε u t b)
          + (∑ b : Bool, stepWeight hn p ε u t b
              * (stepUpperScore i k (cutAt hn p ε t, b)
                + (2 * p - 1) * stepCount i k (cutAt hn p ε t, b))) := by
          simp only [Fintype.sum_bool]
          ring
      _ = upperMartingale p i k t := by rw [hsum, hzero]; ring

/-- For `i < k ≤ u` and `0 < p < 1`, the weighted next squared upper martingale equals its
current square plus `4 * p * (1 - p)` at a crossing cut. -/
theorem upperStepSq_sum {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u i k : Fin n)
    (hp : 0 < p) (hp1 : p < 1) (hku : (k : ℕ) ≤ (u : ℕ)) (hik : (i : ℕ) < (k : ℕ))
    (t : Record n) :
    (∑ b : Bool, stepWeight hn p ε u t b
      * (upperMartingale p i k (extend hn p ε t b)) ^ 2)
      = (upperMartingale p i k t) ^ 2
        + (if IsCrossing i k (cutAt hn p ε t, true) then 4 * p * (1 - p) else 0) := by
  have hsum : (∑ b : Bool, stepWeight hn p ε u t b) = 1 := by
    unfold stepWeight
    rw [Fintype.sum_bool]
    simpa [add_comm] using! answerLikelihood_sum u (cutAt hn p ε t) p
  have hzero := upperStep_drift_zero hn p ε u i k hp hp1 hku hik t
  have hsq := upperStep_sq_drift hn p ε u i k hp hp1 hku hik t
  have hs : stepWeight hn p ε u t true + stepWeight hn p ε u t false = 1 := by
    simpa [Fintype.sum_bool] using! hsum
  have hz :
      (stepWeight hn p ε u t true
          * (stepUpperScore i k (cutAt hn p ε t, true)
              + (2 * p - 1) * stepCount i k (cutAt hn p ε t, true))
        + stepWeight hn p ε u t false
          * (stepUpperScore i k (cutAt hn p ε t, false)
              + (2 * p - 1) * stepCount i k (cutAt hn p ε t, false))) = 0 := by
    simpa [Fintype.sum_bool] using! hzero
  have hq :
      (stepWeight hn p ε u t true
          * (stepUpperScore i k (cutAt hn p ε t, true)
              + (2 * p - 1) * stepCount i k (cutAt hn p ε t, true)) ^ 2
        + stepWeight hn p ε u t false
          * (stepUpperScore i k (cutAt hn p ε t, false)
              + (2 * p - 1) * stepCount i k (cutAt hn p ε t, false)) ^ 2)
        = (if IsCrossing i k (cutAt hn p ε t, true) then 4 * p * (1 - p) else 0) := by
    simpa [Fintype.sum_bool] using! hsq
  simp only [Fintype.sum_bool]
  rw [upperMartingale_step hn p ε i k t true, upperMartingale_step hn p ε i k t false]
  have hsq' :
      stepWeight hn p ε u t true
          * (upperMartingale p i k t
              + (stepUpperScore i k (cutAt hn p ε t, true)
                  + (2 * p - 1) * stepCount i k (cutAt hn p ε t, true))) ^ 2
        + stepWeight hn p ε u t false
          * (upperMartingale p i k t
              + (stepUpperScore i k (cutAt hn p ε t, false)
                  + (2 * p - 1) * stepCount i k (cutAt hn p ε t, false))) ^ 2
        = (upperMartingale p i k t) ^ 2
            * (stepWeight hn p ε u t true + stepWeight hn p ε u t false)
          + 2 * (upperMartingale p i k t)
            * (stepWeight hn p ε u t true
                * (stepUpperScore i k (cutAt hn p ε t, true)
                    + (2 * p - 1) * stepCount i k (cutAt hn p ε t, true))
              + stepWeight hn p ε u t false
                * (stepUpperScore i k (cutAt hn p ε t, false)
                    + (2 * p - 1) * stepCount i k (cutAt hn p ε t, false)))
          + (stepWeight hn p ε u t true
                * (stepUpperScore i k (cutAt hn p ε t, true)
                    + (2 * p - 1) * stepCount i k (cutAt hn p ε t, true)) ^ 2
            + stepWeight hn p ε u t false
                * (stepUpperScore i k (cutAt hn p ε t, false)
                    + (2 * p - 1) * stepCount i k (cutAt hn p ε t, false)) ^ 2) := by
    ring
  rw [hsq', hs, hz, hq]
  ring

/-- For `i < k ≤ u` and `0 < p < 1`, the tree crossing variance equals the tree-weighted squared
upper martingale minus its initial square. -/
theorem treeUpperVar_eq {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u i k : Fin n)
    (hp : 0 < p) (hp1 : p < 1) (hku : (k : ℕ) ≤ (u : ℕ)) (hik : (i : ℕ) < (k : ℕ)) :
    ∀ (m : ℕ) (t : Record n),
      treeCrossVar hn p ε u i k m t
        = treeWeight hn p ε u (fun s => (upperMartingale p i k s) ^ 2) m t
          - (upperMartingale p i k t) ^ 2 := by
  intro m
  induction m with
  | zero =>
    intro t
    simp only [treeCrossVar, treeWeight]
    ring
  | succ m ih =>
    intro t
    have hIH : ∀ b : Bool,
        treeCrossVar hn p ε u i k m (extend hn p ε t b)
          + (upperMartingale p i k (extend hn p ε t b)) ^ 2
        = treeWeight hn p ε u (fun s => (upperMartingale p i k s) ^ 2) m (extend hn p ε t b) := by
      intro b
      have h := ih (extend hn p ε t b)
      linarith
    have hsq :
        stepWeight hn p ε u t true * (upperMartingale p i k (extend hn p ε t true)) ^ 2
          + stepWeight hn p ε u t false * (upperMartingale p i k (extend hn p ε t false)) ^ 2
        = (upperMartingale p i k t) ^ 2
            + (if IsCrossing i k (cutAt hn p ε t, true) then 4 * p * (1 - p) else 0) := by
      simpa [Fintype.sum_bool] using! upperStepSq_sum hn p ε u i k hp hp1 hku hik t
    have hexp :
        (stepWeight hn p ε u t true
              * (treeCrossVar hn p ε u i k m (extend hn p ε t true)
                + (upperMartingale p i k (extend hn p ε t true)) ^ 2)
            + stepWeight hn p ε u t false
              * (treeCrossVar hn p ε u i k m (extend hn p ε t false)
                + (upperMartingale p i k (extend hn p ε t false)) ^ 2))
        = (stepWeight hn p ε u t true * treeCrossVar hn p ε u i k m (extend hn p ε t true)
            + stepWeight hn p ε u t false * treeCrossVar hn p ε u i k m (extend hn p ε t false))
          + (stepWeight hn p ε u t true * (upperMartingale p i k (extend hn p ε t true)) ^ 2
            + stepWeight hn p ε u t false * (upperMartingale p i k (extend hn p ε t false)) ^ 2) := by
      ring
    have hregroup :
        (stepWeight hn p ε u t true * treeCrossVar hn p ε u i k m (extend hn p ε t true)
          + stepWeight hn p ε u t false * treeCrossVar hn p ε u i k m (extend hn p ε t false))
          + (if IsCrossing i k (cutAt hn p ε t, true) then 4 * p * (1 - p) else 0)
        = ((stepWeight hn p ε u t true
              * (treeCrossVar hn p ε u i k m (extend hn p ε t true)
                + (upperMartingale p i k (extend hn p ε t true)) ^ 2)
            + stepWeight hn p ε u t false
              * (treeCrossVar hn p ε u i k m (extend hn p ε t false)
                + (upperMartingale p i k (extend hn p ε t false)) ^ 2))
            - (upperMartingale p i k t) ^ 2) := by
      rw [hexp, hsq]
      ring
    simp only [treeCrossVar, treeWeight, Fintype.sum_bool]
    rw [hregroup, hIH true, hIH false]

/-- When `p > 1 / 2`, the upper martingale is at least the upper crossing score. -/
theorem upperScore_le_martingale {n : ℕ} (p : ℝ) (i k : Fin n) (hhalf : 1 / 2 < p)
    (t : Record n) :
    upperMartingale p i k t ≥ upperScore i k t := by
  have hcount : 0 ≤ crossCount i k t := by
    simp only [crossCount]
    have h1 : (0 : ℝ) ≤ (crossTrue i k t : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ (crossFalse i k t : ℝ) := Nat.cast_nonneg _
    linarith
  have hpos : 0 ≤ 2 * p - 1 := by linarith
  have hmul : 0 ≤ (2 * p - 1) * crossCount i k t :=
    mul_nonneg hpos hcount
  simp only [upperMartingale]
  linarith

/-- For `i < k ≤ u` and `1 / 2 < p < 1`, the tree count of upper scores at least `r > 0` is at
most `4 * p * (1 - p) * m / r^2`. -/
theorem upperScore_tail_bound {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u i k : Fin n) (r : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hhalf : 1 / 2 < p) (hku : (k : ℕ) ≤ (u : ℕ))
    (hik : (i : ℕ) < (k : ℕ)) (hr : 0 < r) :
    ∀ (m : ℕ),
      treeCount hn p ε u (fun t => r ≤ upperScore i k t) m []
        ≤ 4 * p * (1 - p) * (m : ℝ) / r ^ 2 := by
  intro m
  have hge : ∀ s : Record n, r ≤ upperScore i k s → r ≤ upperMartingale p i k s := by
    intro s hs
    have h1 := upperScore_le_martingale p i k hhalf s
    linarith
  have hind : ∀ s : Record n,
      (if r <= upperMartingale p i k s then 1 else 0)
        <= (upperMartingale p i k s) ^ 2 / r ^ 2 := by
    intro s
    by_cases h : r <= upperMartingale p i k s
    · rw [if_pos h]
      have hM2 : r ^ 2 <= (upperMartingale p i k s) ^ 2 := by nlinarith
      have h1 : 1 <= (upperMartingale p i k s) ^ 2 / r ^ 2 := by
        rw [le_div_iff₀ (by exact sq_pos_of_pos hr)]
        nlinarith
      linarith
    · rw [if_neg h]
      have h1 : 0 <= (upperMartingale p i k s) ^ 2 / r ^ 2 := by positivity
      linarith
  have h1 := treeCount_eq_indicator hn p ε u (fun t => r <= upperScore i k t) m []
  have h2 := treeWeight_mono hn p ε u hp hp1
    (V := fun s => if r <= upperScore i k s then 1 else 0)
    (W := fun s => if r <= upperMartingale p i k s then 1 else 0)
    (fun s => by

      by_cases hs : r <= upperScore i k s
      · have hm := hge s hs
        simp [hs, hm]
      · by_cases hm : r <= upperMartingale p i k s
        · simp [hs, hm]
        · simp [hs, hm]) m []
  have h3 := treeWeight_mono hn p ε u hp hp1
    (V := fun s => if r <= upperMartingale p i k s then 1 else 0)
    (W := fun s => (upperMartingale p i k s) ^ 2 / r ^ 2)
    (fun s => hind s) m []
  have h4 := treeWeight_const_mul hn p ε u (1 / r ^ 2)
    (fun s => (upperMartingale p i k s) ^ 2) m []
  have h5 := treeUpperVar_eq hn p ε u i k hp hp1 hku hik m []
  have h6 := upperMartingale_nil p i k
  have h7 := treeCrossVar_le hn p ε u i k hp hp1 m []
  have hvar : treeWeight hn p ε u (fun s => (upperMartingale p i k s) ^ 2) m []
      = treeCrossVar hn p ε u i k m [] := by
    rw [h5, h6]
    ring
  have hdiv : (fun s => (upperMartingale p i k s) ^ 2 / r ^ 2)
      = (fun s => (1 / r ^ 2) * (upperMartingale p i k s) ^ 2) := by
    funext s
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hfinal : (1 / r ^ 2) * treeCrossVar hn p ε u i k m []
      <= 4 * p * (1 - p) * (m : ℝ) / r ^ 2 := by
    have hmul : treeCrossVar hn p ε u i k m [] * (1 / r ^ 2)
        ≤ (4 * p * (1 - p) * (m : ℝ)) * (1 / r ^ 2) :=
      mul_le_mul_of_nonneg_right (a := 1 / r ^ 2) h7 (by positivity)
    calc (1 / r ^ 2) * treeCrossVar hn p ε u i k m []
        = treeCrossVar hn p ε u i k m [] * (1 / r ^ 2) := by ring
      _ <= (4 * p * (1 - p) * (m : ℝ)) * (1 / r ^ 2) := hmul
      _ = 4 * p * (1 - p) * (m : ℝ) / r ^ 2 := by ring
  calc treeCount hn p ε u (fun t => r <= upperScore i k t) m []
      = treeWeight hn p ε u (fun s => if r <= upperScore i k s then 1 else 0) m [] := h1
    _ <= treeWeight hn p ε u (fun s => if r <= upperMartingale p i k s then 1 else 0) m [] := h2
    _ <= treeWeight hn p ε u (fun s => (upperMartingale p i k s) ^ 2 / r ^ 2) m [] := h3
    _ = (1 / r ^ 2) * treeWeight hn p ε u (fun s => (upperMartingale p i k s) ^ 2) m [] := by
        rw [hdiv, h4]
    _ = (1 / r ^ 2) * treeCrossVar hn p ε u i k m [] := by rw [hvar]
    _ <= 4 * p * (1 - p) * (m : ℝ) / r ^ 2 := hfinal

/-- For `0 < p < 1`, the record ratios for two opposite cell orderings multiply to one. -/
theorem recordRatio_inv {n : ℕ} (t : Record n) (u v : Fin n) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    recordRatio t u v p * recordRatio t v u p = 1 := by
  unfold recordRatio
  have h1 : recordLikelihood t u p ≠ 0 := ne_of_gt (recordLikelihood_pos p hp hp1 t u)
  have h2 : recordLikelihood t v p ≠ 0 := ne_of_gt (recordLikelihood_pos p hp hp1 t v)
  field_simp

/-- For `i < k` and `1 / 2 < p < 1`, a ratio of cell `i` to cell `k` at least `(p / (1 - p)) ^
r` forces upper score at least `r`. -/
theorem upperScore_of_ratio_ge {n : ℕ} (p : ℝ) (i k : Fin n) (hp : 0 < p) (hp1 : p < 1)
    (hhalf : 1 / 2 < p) (hik : i.val < k.val) (t : Record n) (r : ℕ) :
    (p / (1 - p)) ^ r ≤ recordRatio t k i p → (r : ℝ) ≤ upperScore i k t := by
  intro h
  have hq : 1 < p / (1 - p) := by
    rw [lt_div_iff₀ (by linarith)]
    linarith
  have hlog : 0 < Real.log (p / (1 - p)) := Real.log_pos hq
  have hR : 0 < (p / (1 - p)) ^ r := by positivity
  have hposI : 0 < recordRatio t i k p := by
    unfold recordRatio
    exact div_pos (recordLikelihood_pos p hp hp1 t k) (recordLikelihood_pos p hp hp1 t i)
  have hinv : recordRatio t k i p = 1 / recordRatio t i k p := by
    have hh := recordRatio_inv t k i p hp hp1
    have hne : recordRatio t i k p ≠ 0 := ne_of_gt hposI
    exact (eq_div_iff hne).mpr hh
  have hmul : (p / (1 - p)) ^ r * recordRatio t i k p ≤ 1 := by
    rw [hinv] at h
    rw [le_div_iff₀ hposI] at h
    exact h
  have hle : recordRatio t i k p ≤ 1 / (p / (1 - p)) ^ r := by
    rw [le_div_iff₀ hR]
    nlinarith [hmul]
  have hposQ : 0 < 1 / (p / (1 - p)) ^ r := div_pos (by positivity) hR
  have hmono : Real.log (recordRatio t i k p) ≤ Real.log (1 / (p / (1 - p)) ^ r) :=
    Real.strictMonoOn_log.monotoneOn hposI hposQ hle
  have hlog2 : Real.log (1 / (p / (1 - p)) ^ r) = -(r : ℝ) * Real.log (p / (1 - p)) := by
    rw [Real.log_div (by norm_num) (by positivity : (p / (1 - p)) ^ r ≠ 0),
      Real.log_one, Real.log_pow]
    ring
  rw [hlog2] at hmono
  rw [crossRatio_log p i k hp hp1 hik t] at hmono
  have hneg : upperScore i k t = -(crossScore i k t) := by
    simp only [upperScore, crossScore]
    push_cast
    ring
  rw [hneg]
  nlinarith [hmono]

/-- For `i < k ≤ u`, `1 / 2 < p < 1`, and positive integer `r`, the tree count of ratios at
least `(p / (1 - p)) ^ r` is at most `4 * p * (1 - p) * m / r^2`. -/
theorem upperScore_ratio_tail {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u i k : Fin n) (r : ℕ)
    (hp : 0 < p) (hp1 : p < 1) (hhalf : 1 / 2 < p) (hku : (k : ℕ) ≤ (u : ℕ))
    (hik : (i : ℕ) < (k : ℕ)) (hr : 0 < r) :
    ∀ (m : ℕ),
      treeCount hn p ε u (fun t => (p / (1 - p)) ^ r ≤ recordRatio t k i p) m []
        <= 4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2 := by
  intro m
  have hmono := treeCount_mono hn p ε u
    (ψ := fun t => (r : ℝ) <= upperScore i k t)
    (fun t ht => upperScore_of_ratio_ge p i k hp hp1 hhalf hik t r ht) hp hp1 m []
  have h1 := upperScore_tail_bound hn p ε u i k (r : ℝ) hp hp1 hhalf hku hik
    (by exact_mod_cast (Nat.cast_pos.mpr hr)) m
  linarith

/-- If `4 * p * (1 - p) * m ≤ δ * r^2`, the upper-score tail count is at most `δ` under the
stated ordering and noise hypotheses. -/
theorem upperScore_tail_calibration {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u i k : Fin n)
    (δ : ℝ) (r : ℕ)
    (hp : 0 < p) (hp1 : p < 1) (hhalf : 1 / 2 < p) (hku : (k : ℕ) ≤ (u : ℕ))
    (hik : (i : ℕ) < (k : ℕ)) (hr : 0 < r) :
    ∀ (m : ℕ),
      4 * p * (1 - p) * (m : ℝ) <= δ * (r : ℝ) ^ 2 ->
        treeCount hn p ε u (fun t => (r : ℝ) <= upperScore i k t) m [] <= δ := by
  intro m hcal
  have h1 := upperScore_tail_bound hn p ε u i k (r : ℝ) hp hp1 hhalf hku hik
    (by exact_mod_cast (Nat.cast_pos.mpr hr)) m
  have hr2 : 0 < (r : ℝ) ^ 2 := by positivity
  rw [le_div_iff₀ hr2] at h1
  have h2 : treeCount hn p ε u (fun t => (r : ℝ) <= upperScore i k t) m [] * (r : ℝ) ^ 2
      <= δ * (r : ℝ) ^ 2 := by linarith
  have h3 : (r : ℝ) ^ 2 * treeCount hn p ε u (fun t => (r : ℝ) <= upperScore i k t) m []
      <= (r : ℝ) ^ 2 * δ := by simpa [mul_comm] using! h2
  exact le_of_mul_le_mul_left h3 hr2

/-- If `i + l < n`, the window above `i` contains exactly `l` cells. -/
theorem windowCellsAbove_card {n : ℕ} (i : Fin n) (l : ℕ) (hin : (i : ℕ) + l < n) :
    (windowCellsAbove i l).card = l := by
  classical
  have himg : (windowCellsAbove i l).image Fin.val = Finset.Icc ((i : ℕ) + 1) ((i : ℕ) + l) := by
    ext m
    constructor
    · intro hm
      rw [Finset.mem_image] at hm
      obtain ⟨k, hkW, hmk⟩ := hm
      have hkW' : (i : ℕ) < (k : ℕ) ∧ (k : ℕ) ≤ (i : ℕ) + l := by
        simpa [windowCellsAbove, Finset.mem_filter, Finset.mem_univ, true_and] using! hkW
      obtain ⟨hk1, hk2⟩ := hkW'
      rw [Finset.mem_Icc]
      constructor
      · omega
      · omega
    · intro hm
      rw [Finset.mem_Icc] at hm
      obtain ⟨hm1, hm2⟩ := hm
      refine Finset.mem_image.mpr ⟨⟨m, lt_of_le_of_lt hm2 hin⟩, ?_, rfl⟩
      simp only [windowCellsAbove, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
  rw [← Finset.card_image_of_injOn (fun x _ y _ h => Fin.val_injective h), himg,
    Nat.card_Icc]
  omega

/-- A normalized nonnegative mass function has a cell of mass at most `1 / l` in the upper
window whenever `l > 0` and `i + l < n`. -/
theorem window_light_cell_above {n : ℕ} (a : Fin n → ℝ) (i : Fin n) (l : ℕ)
    (hl : 0 < l) (hin : (i : ℕ) + l < n) (ha0 : ∀ m, 0 ≤ a m) (hsum : (∑ m, a m) = 1) :
    ∃ k : Fin n, k ∈ windowCellsAbove i l ∧ a k ≤ 1 / (l : ℝ) := by
  classical
  set W : Finset (Fin n) := windowCellsAbove i l with hWdef
  have hcard : W.card = l := by
    rw [hWdef]
    exact windowCellsAbove_card i l hin
  by_contra hcon
  push Not at hcon
  have hWne : W.Nonempty := Finset.card_pos.mp (by rw [hcard]; omega)
  have hone : (1 : ℝ) = ∑ k ∈ W, 1 / (l : ℝ) := by
    have h1 : (∑ k ∈ W, 1 / (l : ℝ)) = (∑ _k ∈ W, (1 : ℝ)) / (l : ℝ) :=
      (Finset.sum_div _ _ _).symm
    have h2 : (∑ _k ∈ W, (1 : ℝ)) = (W.card : ℝ) := by
      rw [Finset.sum_const, Nat.smul_one_eq_cast]
    have hlR : ((l : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hl)
    rw [h1, h2, hcard, div_self hlR]
  have hlt : (∑ k ∈ W, 1 / (l : ℝ)) < ∑ k ∈ W, a k := by
    refine Finset.sum_lt_sum_of_nonempty hWne fun k hk => ?_
    simp only [hWdef, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact hcon k hk
  have hle : ∑ k ∈ W, a k ≤ ∑ m, a m := by
    apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun m _ _ => ha0 m)
    rw [hWdef]
    exact Finset.filter_subset _ _
  linarith

/-- Under the stated upper-window separation and threshold conditions, the heavy-cell and upper
light-witness event has tree count at most the window cardinality times `4 * p * (1 - p) * m
/ r^2`. -/
theorem upperWindow_light_tail_bound {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u i : Fin n) (l r : ℕ)
    (hp : 0 < p) (hp1 : p < 1) (hhalf : 1 / 2 < p) (hε : 0 < ε) (hl : 0 < l)
    (hin : (i : ℕ) + l < n) (hku : (i : ℕ) + l ≤ (u : ℕ)) (hr : 0 < r)
    (hthr : ε * (l : ℝ) ≥ (p / (1 - p)) ^ r) :
    ∀ (m : ℕ),
      treeCount hn p ε u
        (fun t => ε <= recordPosterior t p i ∧
          ∃ k, k ∈ windowCellsAbove i l ∧ recordPosterior t p k <= 1 / (l : ℝ)) m []
        <= (windowCellsAbove i l).card * (4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2) := by
  intro m
  let φ : Fin n → Record n → Prop := fun k t =>
    ε <= recordPosterior t p i ∧ (p / (1 - p)) ^ r <= recordRatio t k i p
  have hmono1 : treeCount hn p ε u
        (fun t => ε <= recordPosterior t p i ∧
          ∃ k, k ∈ windowCellsAbove i l ∧ recordPosterior t p k <= 1 / (l : ℝ)) m []
      <= treeCount hn p ε u
        (fun t => ∃ k ∈ windowCellsAbove i l, φ k t) m [] :=
    treeCount_mono hn p ε u (fun t ht => by
      obtain ⟨k, hk, hlight⟩ := ht.2
      have hratio := halt_forces_light_ratio hn p ε hp hp1 t i k l hl hε ht.1 hlight
      exact ⟨k, hk, ht.1, le_trans hthr hratio⟩) hp hp1 m []
  have hunion := treeCount_exists_le_finset hn p ε u (windowCellsAbove i l) φ hp hp1 m []
  have hsum := treeCountFinset_eq_sum hn p ε u (windowCellsAbove i l) φ m []
  have hper : ∀ k ∈ windowCellsAbove i l,
      treeCount hn p ε u (φ k) m []
        <= 4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2 := by
    intro k hk
    have hk1 : (k : ℕ) ≤ (i : ℕ) + l := (Finset.mem_filter.mp hk).2.2
    have hik : (i : ℕ) < (k : ℕ) := (Finset.mem_filter.mp hk).2.1
    have hku' : (k : ℕ) ≤ (u : ℕ) := by omega
    have hm := treeCount_mono hn p ε u
      (φ := fun t => ε <= recordPosterior t p i ∧ (p / (1 - p)) ^ r <= recordRatio t k i p)
      (ψ := fun t => (p / (1 - p)) ^ r <= recordRatio t k i p)
      (fun t ht => ht.2) hp hp1 m []
    have hrt := upperScore_ratio_tail hn p ε u i k r hp hp1 hhalf hku' hik hr m
    linarith
  calc treeCount hn p ε u
        (fun t => ε <= recordPosterior t p i ∧
          ∃ k, k ∈ windowCellsAbove i l ∧ recordPosterior t p k <= 1 / (l : ℝ)) m []
      <= treeCount hn p ε u (fun t => ∃ k ∈ windowCellsAbove i l, φ k t) m [] := hmono1
    _ <= treeCountFinset hn p ε u (windowCellsAbove i l) φ m [] := hunion
    _ = ∑ k ∈ windowCellsAbove i l, treeCount hn p ε u (φ k) m [] := hsum
    _ <= ∑ k ∈ windowCellsAbove i l, 4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro k hk
        exact hper k hk
    _ = (windowCellsAbove i l).card * (4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2) := by
        rw [Finset.sum_const]
        simp [nsmul_eq_mul]

/-- Collects the upper-martingale variance identity, upper-score and ratio tail bounds, and the
upper-window concentration estimate. -/
theorem clause13_symmetric_endpoint :
    (∀ (n : ℕ) (p ε : ℝ) (u i k : Fin n) (hn : 0 < n) (hp : 0 < p) (hp1 : p < 1)
      (hku : (k : ℕ) ≤ (u : ℕ)) (hik : (i : ℕ) < (k : ℕ)) (m : ℕ) (t : Record n),
      treeCrossVar hn p ε u i k m t
        = treeWeight hn p ε u (fun s => (upperMartingale p i k s) ^ 2) m t
          - (upperMartingale p i k t) ^ 2) ∧
    (∀ (n : ℕ) (p ε : ℝ) (u i k : Fin n) (hn : 0 < n) (r : ℝ) (hp : 0 < p) (hp1 : p < 1)
      (hhalf : 1 / 2 < p) (hku : (k : ℕ) ≤ (u : ℕ)) (hik : (i : ℕ) < (k : ℕ))
      (hr : 0 < r) (m : ℕ),
      treeCount hn p ε u (fun t => r ≤ upperScore i k t) m []
        ≤ 4 * p * (1 - p) * (m : ℝ) / r ^ 2) ∧
    (∀ (n : ℕ) (p ε : ℝ) (u i k : Fin n) (hn : 0 < n) (r : ℕ) (hp : 0 < p) (hp1 : p < 1)
      (hhalf : 1 / 2 < p) (hku : (k : ℕ) ≤ (u : ℕ)) (hik : (i : ℕ) < (k : ℕ))
      (hr : 0 < r) (m : ℕ),
      treeCount hn p ε u (fun t => (p / (1 - p)) ^ r ≤ recordRatio t k i p) m []
        ≤ 4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2) ∧
    (∀ (n : ℕ) (p ε : ℝ) (u i : Fin n) (hn : 0 < n) (l r : ℕ) (hp : 0 < p) (hp1 : p < 1)
      (hhalf : 1 / 2 < p) (hε : 0 < ε) (hl : 0 < l) (hin : (i : ℕ) + l < n)
      (hku : (i : ℕ) + l ≤ (u : ℕ)) (hr : 0 < r)
      (hthr : ε * (l : ℝ) ≥ (p / (1 - p)) ^ r) (m : ℕ),
      treeCount hn p ε u
        (fun t => ε ≤ recordPosterior t p i ∧
          ∃ k, k ∈ windowCellsAbove i l ∧ recordPosterior t p k ≤ 1 / (l : ℝ)) m []
        ≤ (windowCellsAbove i l).card * (4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n p ε u i k hn hp hp1 hku hik m t
    exact treeUpperVar_eq hn p ε u i k hp hp1 hku hik m t
  · intro n p ε u i k hn r hp hp1 hhalf hku hik hr m
    exact upperScore_tail_bound hn p ε u i k r hp hp1 hhalf hku hik hr m
  · intro n p ε u i k hn r hp hp1 hhalf hku hik hr m
    exact upperScore_ratio_tail hn p ε u i k r hp hp1 hhalf hku hik hr m
  · intro n p ε u i hn l r hp hp1 hhalf hε hl hin hku hr hthr m
    exact upperWindow_light_tail_bound hn p ε u i l r hp hp1 hhalf hε hl hin hku hr hthr m

/-- For `0 < p < 1`, the tree count of a union of two record predicates is at most the sum of
their individual tree counts. -/
theorem treeCount_union_le {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u : Fin n)
    (hp : 0 < p) (hp1 : p < 1) {φ ψ : Record n → Prop} :
    ∀ (m : ℕ) (t : Record n),
      treeCount hn p ε u (fun s => φ s ∨ ψ s) m t
        ≤ treeCount hn p ε u φ m t + treeCount hn p ε u ψ m t := by
  intro m
  induction m with
  | zero =>
    intro t
    simp only [treeCount]
    by_cases ho : φ t ∨ ψ t
    · rw [if_pos ho]
      by_cases h : φ t
      · by_cases h2 : ψ t
        · simp [h, h2] <;> ring
        · simp [h, h2] <;> ring
      · have h2 : ψ t := ho.resolve_left h
        simp [h, h2] <;> ring
    · rw [if_neg ho]
      have h1 : ¬ φ t := fun hh => ho (Or.inl hh)
      have h2 : ¬ ψ t := fun hh => ho (Or.inr hh)
      rw [if_neg h1, if_neg h2]
      linarith
  | succ m ih =>
    intro t
    have hsplit :
        (∑ b : Bool, stepWeight hn p ε u t b
            * (treeCount hn p ε u φ m (extend hn p ε t b)
              + treeCount hn p ε u ψ m (extend hn p ε t b)))
          = (∑ b : Bool, stepWeight hn p ε u t b
              * treeCount hn p ε u φ m (extend hn p ε t b))
            + (∑ b : Bool, stepWeight hn p ε u t b
              * treeCount hn p ε u ψ m (extend hn p ε t b)) := by
      rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
      ring
    have hper : ∀ b : Bool,
        stepWeight hn p ε u t b * treeCount hn p ε u (fun s => φ s ∨ ψ s) m (extend hn p ε t b)
          ≤ stepWeight hn p ε u t b
            * (treeCount hn p ε u φ m (extend hn p ε t b)
              + treeCount hn p ε u ψ m (extend hn p ε t b)) := by
      intro b
      have hwb : 0 ≤ stepWeight hn p ε u t b := by
        unfold stepWeight
        exact le_of_lt (answerLikelihood_pos u (cutAt hn p ε t) p b hp hp1)
      exact mul_le_mul_of_nonneg_left (ih (extend hn p ε t b)) hwb
    calc treeCount hn p ε u (fun s => φ s ∨ ψ s) (m + 1) t
        = ∑ b : Bool, stepWeight hn p ε u t b
            * treeCount hn p ε u (fun s => φ s ∨ ψ s) m (extend hn p ε t b) := by
          simp only [treeCount]
      _ ≤ ∑ b : Bool, stepWeight hn p ε u t b
            * (treeCount hn p ε u φ m (extend hn p ε t b)
              + treeCount hn p ε u ψ m (extend hn p ε t b)) := by
          exact Finset.sum_le_sum (fun b _ => hper b)
      _ = (∑ b : Bool, stepWeight hn p ε u t b
            * treeCount hn p ε u φ m (extend hn p ε t b))
          + (∑ b : Bool, stepWeight hn p ε u t b
            * treeCount hn p ε u ψ m (extend hn p ε t b)) := hsplit
      _ = treeCount hn p ε u φ (m + 1) t + treeCount hn p ε u ψ (m + 1) t := by
          simp only [treeCount]

/-- For `u ≤ k < i`, a heavy cell `i` and light cell `k` have joint tree count at most `4 * p *
(1 - p) * m / r^2` under the stated ratio-threshold conditions. -/
theorem light_cell_ratio_tail {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u i k : Fin n) (l r : ℕ)
    (hp : 0 < p) (hp1 : p < 1) (hhalf : 1 / 2 < p) (hε : 0 < ε) (hl : 0 < l)
    (huk : (u : ℕ) ≤ (k : ℕ)) (hki : (k : ℕ) < (i : ℕ)) (hr : 0 < r)
    (hthr : ε * (l : ℝ) ≥ (p / (1 - p)) ^ r) :
    ∀ (m : ℕ),
      treeCount hn p ε u
        (fun t => ε ≤ recordPosterior t p i ∧ recordPosterior t p k ≤ 1 / (l : ℝ)) m []
        ≤ 4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2 := by
  intro m
  have hmono := treeCount_mono hn p ε u
    (φ := fun t => ε ≤ recordPosterior t p i ∧ recordPosterior t p k ≤ 1 / (l : ℝ))
    (ψ := fun t => ε ≤ recordPosterior t p i ∧ (p / (1 - p)) ^ r ≤ recordRatio t k i p)
    (fun t ht => by
      have hratio := halt_forces_light_ratio hn p ε hp hp1 t i k l hl hε ht.1 ht.2
      exact ⟨ht.1, le_trans hthr hratio⟩) hp hp1 m []
  have hm := treeCount_mono hn p ε u
    (φ := fun t => ε ≤ recordPosterior t p i ∧ (p / (1 - p)) ^ r ≤ recordRatio t k i p)
    (ψ := fun t => (p / (1 - p)) ^ r ≤ recordRatio t k i p)
    (fun t ht => ht.2) hp hp1 m []
  have hrt := crossScore_ratio_tail hn p ε u k i r hp hp1 hhalf huk hki hr m
  linarith

/-- For `i < k ≤ u`, a heavy cell `i` and light cell `k` have joint tree count at most `4 * p *
(1 - p) * m / r^2` under the stated ratio-threshold conditions. -/
theorem upper_light_cell_ratio_tail {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u i k : Fin n) (l r : ℕ)
    (hp : 0 < p) (hp1 : p < 1) (hhalf : 1 / 2 < p) (hε : 0 < ε) (hl : 0 < l)
    (hku : (k : ℕ) ≤ (u : ℕ)) (hik : (i : ℕ) < (k : ℕ)) (hr : 0 < r)
    (hthr : ε * (l : ℝ) ≥ (p / (1 - p)) ^ r) :
    ∀ (m : ℕ),
      treeCount hn p ε u
        (fun t => ε ≤ recordPosterior t p i ∧ recordPosterior t p k ≤ 1 / (l : ℝ)) m []
        ≤ 4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2 := by
  intro m
  have hmono := treeCount_mono hn p ε u
    (φ := fun t => ε ≤ recordPosterior t p i ∧ recordPosterior t p k ≤ 1 / (l : ℝ))
    (ψ := fun t => ε ≤ recordPosterior t p i ∧ (p / (1 - p)) ^ r ≤ recordRatio t k i p)
    (fun t ht => by
      have hratio := halt_forces_light_ratio hn p ε hp hp1 t i k l hl hε ht.1 ht.2
      exact ⟨ht.1, le_trans hthr hratio⟩) hp hp1 m []
  have hm := treeCount_mono hn p ε u
    (φ := fun t => ε ≤ recordPosterior t p i ∧ (p / (1 - p)) ^ r ≤ recordRatio t k i p)
    (ψ := fun t => (p / (1 - p)) ^ r ≤ recordRatio t k i p)
    (fun t ht => ht.2) hp hp1 m []
  have hrt := upperScore_ratio_tail hn p ε u i k r hp hp1 hhalf hku hik hr m
  linarith

/-- Under the stated threshold conditions, a heavy cell with a light witness between it and the
truth in either window has tree count bounded by the sum of the window cardinalities times
`4 * p * (1 - p) * m / r^2`. -/
theorem clause13_window_two_arm {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u i : Fin n) (l r : ℕ)
    (hp : 0 < p) (hp1 : p < 1) (hhalf : 1 / 2 < p) (hε : 0 < ε) (hl : 0 < l)
    (hin : (i : ℕ) + l < n) (hr : 0 < r)
    (hthr : ε * (l : ℝ) ≥ (p / (1 - p)) ^ r) :
    ∀ (m : ℕ),
      treeCount hn p ε u
        (fun t => ε ≤ recordPosterior t p i ∧
          ((∃ k, k ∈ windowCells i l ∧ recordPosterior t p k ≤ 1 / (l : ℝ) ∧ (u : ℕ) ≤ (k : ℕ))
            ∨ (∃ k, k ∈ windowCellsAbove i l ∧ recordPosterior t p k ≤ 1 / (l : ℝ)
              ∧ (k : ℕ) ≤ (u : ℕ))))
        m []
        ≤ ((windowCells i l).card + (windowCellsAbove i l).card)
            * (4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2) := by
  intro m
  let φ1 : Fin n → Record n → Prop := fun k t =>
    ε ≤ recordPosterior t p i ∧ recordPosterior t p k ≤ 1 / (l : ℝ) ∧ (u : ℕ) ≤ (k : ℕ)
  let φ2 : Fin n → Record n → Prop := fun k t =>
    ε ≤ recordPosterior t p i ∧ recordPosterior t p k ≤ 1 / (l : ℝ) ∧ (k : ℕ) ≤ (u : ℕ)
  let E1 : Record n → Prop := fun t => ∃ k, k ∈ windowCells i l ∧ φ1 k t
  let E2 : Record n → Prop := fun t => ∃ k, k ∈ windowCellsAbove i l ∧ φ2 k t
  have hmain : treeCount hn p ε u
        (fun t => ε ≤ recordPosterior t p i ∧
          ((∃ k, k ∈ windowCells i l ∧ recordPosterior t p k ≤ 1 / (l : ℝ) ∧ (u : ℕ) ≤ (k : ℕ))
            ∨ (∃ k, k ∈ windowCellsAbove i l ∧ recordPosterior t p k ≤ 1 / (l : ℝ)
              ∧ (k : ℕ) ≤ (u : ℕ)))) m []
      ≤ treeCount hn p ε u (fun t => E1 t ∨ E2 t) m [] := by
    refine treeCount_mono hn p ε u
      (φ := fun t => ε ≤ recordPosterior t p i ∧
          ((∃ k, k ∈ windowCells i l ∧ recordPosterior t p k ≤ 1 / (l : ℝ) ∧ (u : ℕ) ≤ (k : ℕ))
            ∨ (∃ k, k ∈ windowCellsAbove i l ∧ recordPosterior t p k ≤ 1 / (l : ℝ)
              ∧ (k : ℕ) ≤ (u : ℕ))))
      (ψ := fun t => E1 t ∨ E2 t)
      (fun t ht => ?_) hp hp1 m []
    rcases ht.2 with hlo | hhi
    · refine Or.inl ?_
      obtain ⟨k, hk, hlight, huk⟩ := hlo
      exact ⟨k, hk, ht.1, hlight, huk⟩
    · refine Or.inr ?_
      obtain ⟨k, hk, hlight, hku⟩ := hhi
      exact ⟨k, hk, ht.1, hlight, hku⟩
  have hunion := treeCount_union_le hn p ε u hp hp1 (φ := E1) (ψ := E2) m []
  have hE1 : treeCount hn p ε u E1 m []
      ≤ treeCount hn p ε u (fun t => ∃ k, k ∈ windowCells i l ∧ φ1 k t) m [] := by
    refine treeCount_mono hn p ε u (φ := E1)
      (ψ := fun t => ∃ k, k ∈ windowCells i l ∧ φ1 k t)
      (fun t ht => ht) hp hp1 m []
  have hE1f := treeCount_exists_le_finset hn p ε u (windowCells i l) φ1 hp hp1 m []
  have hE1s := treeCountFinset_eq_sum hn p ε u (windowCells i l) φ1 m []
  have hX : 0 ≤ 4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2 := by
    have h1 : 0 ≤ 1 - p := by linarith
    have h2 : 0 ≤ (m : ℝ) := by positivity
    have h3 : 0 < (r : ℝ) ^ 2 := by positivity
    have h4 : 0 ≤ 4 * p * (1 - p) := by nlinarith
    exact div_nonneg (mul_nonneg h4 h2) (le_of_lt h3)
  have hE1per : ∀ k ∈ windowCells i l,
      treeCount hn p ε u (φ1 k) m [] ≤ 4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2 := by
    intro k hk
    by_cases huk : (u : ℕ) ≤ (k : ℕ)
    · have hki : (k : ℕ) < (i : ℕ) := (Finset.mem_filter.mp hk).2.2
      have htail := light_cell_ratio_tail hn p ε u i k l r hp hp1 hhalf hε hl huk hki hr hthr m
      have hmono := treeCount_mono hn p ε u
        (φ := φ1 k)
        (ψ := fun t => ε ≤ recordPosterior t p i ∧ recordPosterior t p k ≤ 1 / (l : ℝ))
        (fun t ht => ⟨ht.1, ht.2.1⟩) hp hp1 m []
      linarith
    · have hzero : ∀ (m : ℕ) (t : Record n), treeCount hn p ε u (φ1 k) m t = 0 := by
        intro m
        induction m with
        | zero =>
          intro t
          simp only [treeCount]
          have hne : ¬ φ1 k t := by
            intro hh
            exact huk hh.2.2
          rw [if_neg hne]
        | succ m ih =>
          intro t
          simp only [treeCount, Fintype.sum_bool]
          simp [ih]
      have hz := hzero m []
      linarith
  have hE2 : treeCount hn p ε u E2 m []
      ≤ treeCount hn p ε u (fun t => ∃ k, k ∈ windowCellsAbove i l ∧ φ2 k t) m [] := by
    refine treeCount_mono hn p ε u (φ := E2)
      (ψ := fun t => ∃ k, k ∈ windowCellsAbove i l ∧ φ2 k t)
      (fun t ht => ht) hp hp1 m []
  have hE2f := treeCount_exists_le_finset hn p ε u (windowCellsAbove i l) φ2 hp hp1 m []
  have hE2s := treeCountFinset_eq_sum hn p ε u (windowCellsAbove i l) φ2 m []
  have hE2per : ∀ k ∈ windowCellsAbove i l,
      treeCount hn p ε u (φ2 k) m [] ≤ 4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2 := by
    intro k hk
    by_cases hku : (k : ℕ) ≤ (u : ℕ)
    · have hik : (i : ℕ) < (k : ℕ) := (Finset.mem_filter.mp hk).2.1
      have htail := upper_light_cell_ratio_tail hn p ε u i k l r hp hp1 hhalf hε hl hku hik hr
        hthr m
      have hmono := treeCount_mono hn p ε u
        (φ := φ2 k)
        (ψ := fun t => ε ≤ recordPosterior t p i ∧ recordPosterior t p k ≤ 1 / (l : ℝ))
        (fun t ht => ⟨ht.1, ht.2.1⟩) hp hp1 m []
      linarith
    · have hzero : ∀ (m : ℕ) (t : Record n), treeCount hn p ε u (φ2 k) m t = 0 := by
        intro m
        induction m with
        | zero =>
          intro t
          simp only [treeCount]
          have hne : ¬ φ2 k t := by
            intro hh
            exact hku hh.2.2
          rw [if_neg hne]
        | succ m ih =>
          intro t
          simp only [treeCount, Fintype.sum_bool]
          simp [ih]
      have hz := hzero m []
      linarith
  have hE1' : treeCount hn p ε u E1 m []
      ≤ (windowCells i l).card * (4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2) := by
    calc treeCount hn p ε u E1 m []
        ≤ treeCount hn p ε u (fun t => ∃ k, k ∈ windowCells i l ∧ φ1 k t) m [] := hE1
      _ ≤ treeCountFinset hn p ε u (windowCells i l) φ1 m [] := hE1f
      _ = ∑ k ∈ windowCells i l, treeCount hn p ε u (φ1 k) m [] := hE1s
      _ ≤ ∑ k ∈ windowCells i l, 4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2 := by
          apply Finset.sum_le_sum
          intro k hk
          exact hE1per k hk
      _ = (windowCells i l).card * (4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2) := by
          rw [Finset.sum_const]
          simp [nsmul_eq_mul]
  have hE2' : treeCount hn p ε u E2 m []
      ≤ (windowCellsAbove i l).card * (4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2) := by
    calc treeCount hn p ε u E2 m []
        ≤ treeCount hn p ε u (fun t => ∃ k, k ∈ windowCellsAbove i l ∧ φ2 k t) m [] := hE2
      _ ≤ treeCountFinset hn p ε u (windowCellsAbove i l) φ2 m [] := hE2f
      _ = ∑ k ∈ windowCellsAbove i l, treeCount hn p ε u (φ2 k) m [] := hE2s
      _ ≤ ∑ k ∈ windowCellsAbove i l, 4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2 := by
          apply Finset.sum_le_sum
          intro k hk
          exact hE2per k hk
      _ = (windowCellsAbove i l).card * (4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2) := by
          rw [Finset.sum_const]
          simp [nsmul_eq_mul]
  calc treeCount hn p ε u
        (fun t => ε ≤ recordPosterior t p i ∧
          ((∃ k, k ∈ windowCells i l ∧ recordPosterior t p k ≤ 1 / (l : ℝ) ∧ (u : ℕ) ≤ (k : ℕ))
            ∨ (∃ k, k ∈ windowCellsAbove i l ∧ recordPosterior t p k ≤ 1 / (l : ℝ)
              ∧ (k : ℕ) ≤ (u : ℕ)))) m []
      ≤ treeCount hn p ε u (fun t => E1 t ∨ E2 t) m [] := hmain
    _ ≤ treeCount hn p ε u E1 m [] + treeCount hn p ε u E2 m [] := hunion
    _ ≤ (windowCells i l).card * (4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2)
        + (windowCellsAbove i l).card * (4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2) := by
          have h1 := hE1'
          have h2 := hE2'
          linarith
    _ = ((windowCells i l).card + (windowCellsAbove i l).card)
        * (4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2) := by ring

/-- For valid windows on both sides of `i`, the two-window heavy-cell and light-witness event
has tree count at most `2 * l` times `4 * p * (1 - p) * m / r^2` under the stated threshold
conditions. -/
theorem clause13_window_two_arm_card {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u i : Fin n) (l r : ℕ)
    (hp : 0 < p) (hp1 : p < 1) (hhalf : 1 / 2 < p) (hε : 0 < ε) (hl : 0 < l)
    (hil : l ≤ (i : ℕ)) (hin : (i : ℕ) + l < n) (hr : 0 < r)
    (hthr : ε * (l : ℝ) ≥ (p / (1 - p)) ^ r) :
    ∀ (m : ℕ),
      treeCount hn p ε u
        (fun t => ε ≤ recordPosterior t p i ∧
          ((∃ k, k ∈ windowCells i l ∧ recordPosterior t p k ≤ 1 / (l : ℝ) ∧ (u : ℕ) ≤ (k : ℕ))
            ∨ (∃ k, k ∈ windowCellsAbove i l ∧ recordPosterior t p k ≤ 1 / (l : ℝ)
              ∧ (k : ℕ) ≤ (u : ℕ))))
        m []
        ≤ 2 * l * (4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2) := by
  intro m
  have htwo := clause13_window_two_arm hn p ε u i l r hp hp1 hhalf hε hl hin hr hthr m
  have hcardle := windowCells_card_le i l hil
  have hcardeq := windowCellsAbove_card i l hin
  have hsum : (windowCells i l).card + (windowCellsAbove i l).card ≤ 2 * l := by
    omega
  have hX : 0 ≤ 4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2 := by
    have h1 : 0 ≤ 1 - p := by linarith
    have h2 : 0 ≤ (m : ℝ) := by positivity
    have h3 : 0 < (r : ℝ) ^ 2 := by positivity
    have h4 : 0 ≤ 4 * p * (1 - p) := by nlinarith
    exact div_nonneg (mul_nonneg h4 h2) (le_of_lt h3)
  calc treeCount hn p ε u
        (fun t => ε ≤ recordPosterior t p i ∧
          ((∃ k, k ∈ windowCells i l ∧ recordPosterior t p k ≤ 1 / (l : ℝ) ∧ (u : ℕ) ≤ (k : ℕ))
            ∨ (∃ k, k ∈ windowCellsAbove i l ∧ recordPosterior t p k ≤ 1 / (l : ℝ)
              ∧ (k : ℕ) ≤ (u : ℕ)))) m []
      ≤ ((windowCells i l).card + (windowCellsAbove i l).card)
          * (4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2) := htwo
    _ ≤ 2 * l * (4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2) := by
        have hsum' : ((windowCells i l).card + (windowCellsAbove i l).card : ℝ) ≤ (2 * l : ℝ) := by
          exact_mod_cast hsum
        have hmul := mul_le_mul_of_nonneg_right hsum' hX
        exact hmul

/-- If cell `i` has posterior at least positive `ε` and the truth lies below its window, a
preceding-window cell has posterior at most `1 / l` and lies at or above the truth. -/
theorem deviation_below_forces_light_cell {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u i : Fin n)
    (l : ℕ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 < ε) (hl : 0 < l)
    (t : Record n) (hhi : ε ≤ recordPosterior t p i) (hdev : TruthBelowWindow u i l) :
    ∃ k : Fin n, k ∈ windowCells i l ∧ recordPosterior t p k ≤ 1 / (l : ℝ)
      ∧ (u : ℕ) ≤ (k : ℕ) := by
  have hdev' : (u : ℕ) + l < (i : ℕ) := hdev
  have hil : l ≤ (i : ℕ) := by omega
  obtain ⟨k, hk, hlight⟩ :=
    window_light_cell (recordPosterior t p) i l hl hil
      (fun m => le_of_lt (recordPosterior_pos hn p hp hp1 t m))
      (recordPosterior_sum hn p hp hp1 t)
  refine ⟨k, hk, hlight, ?_⟩
  have hk1 : (i : ℕ) - l ≤ (k : ℕ) := (Finset.mem_filter.mp hk).2.1
  have hk2 : (k : ℕ) < (i : ℕ) := (Finset.mem_filter.mp hk).2.2
  omega

/-- If cell `i` has posterior at least positive `ε` and the truth lies above its window, an
upper-window cell has posterior at most `1 / l` and lies at or below the truth. -/
theorem deviation_above_forces_light_cell {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u i : Fin n)
    (l : ℕ) (hp : 0 < p) (hp1 : p < 1) (hε : 0 < ε) (hl : 0 < l)
    (t : Record n) (hhi : ε ≤ recordPosterior t p i) (hdev : TruthAboveWindow u i l) :
    ∃ k : Fin n, k ∈ windowCellsAbove i l ∧ recordPosterior t p k ≤ 1 / (l : ℝ)
      ∧ (k : ℕ) ≤ (u : ℕ) := by
  have hdev' : (i : ℕ) + l < (u : ℕ) := hdev
  have hin : (i : ℕ) + l < n := by omega
  obtain ⟨k, hk, hlight⟩ :=
    window_light_cell_above (recordPosterior t p) i l hl hin
      (fun m => le_of_lt (recordPosterior_pos hn p hp hp1 t m))
      (recordPosterior_sum hn p hp hp1 t)
  refine ⟨k, hk, hlight, ?_⟩
  have hk1 : (i : ℕ) < (k : ℕ) := (Finset.mem_filter.mp hk).2.1
  have hk2 : (k : ℕ) ≤ (i : ℕ) + l := (Finset.mem_filter.mp hk).2.2
  omega

/-- When the truth lies below the window of `i`, the tree count of posterior mass at least `ε`
at `i` is bounded by the preceding-window cardinality times `4 * p * (1 - p) * m / r^2`
under the stated hypotheses. -/
theorem clause13_deviation_below_bound {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u i : Fin n) (l r : ℕ)
    (hp : 0 < p) (hp1 : p < 1) (hhalf : 1 / 2 < p) (hε : 0 < ε) (hl : 0 < l) (hr : 0 < r)
    (hthr : ε * (l : ℝ) ≥ (p / (1 - p)) ^ r) (hdev : TruthBelowWindow u i l) :
    ∀ (m : ℕ),
      treeCount hn p ε u (fun t => ε ≤ recordPosterior t p i) m []
        ≤ (windowCells i l).card * (4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2) := by
  intro m
  have hdev' : (u : ℕ) + l < (i : ℕ) := hdev
  have hil : l ≤ (i : ℕ) := by omega
  have hul : (u : ℕ) + l ≤ (i : ℕ) := by omega
  have hmono : treeCount hn p ε u (fun t => ε ≤ recordPosterior t p i) m []
      ≤ treeCount hn p ε u
        (fun t => ε ≤ recordPosterior t p i ∧
          ∃ k, k ∈ windowCells i l ∧ recordPosterior t p k ≤ 1 / (l : ℝ)) m [] := by
    refine treeCount_mono hn p ε u (fun t ht => ?_) hp hp1 m []
    obtain ⟨k, hk, hlight, hku⟩ :=
      deviation_below_forces_light_cell hn p ε u i l hp hp1 hε hl t ht hdev'
    exact ⟨ht, k, hk, hlight⟩
  have h1 := window_light_tail_bound hn p ε u i l r hp hp1 hhalf hε hl hil hul hr hthr m
  linarith

/-- When the truth lies above the window of `i`, the tree count of posterior mass at least `ε`
at `i` is bounded by the upper-window cardinality times `4 * p * (1 - p) * m / r^2` under
the stated hypotheses. -/
theorem clause13_deviation_above_bound {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u i : Fin n) (l r : ℕ)
    (hp : 0 < p) (hp1 : p < 1) (hhalf : 1 / 2 < p) (hε : 0 < ε) (hl : 0 < l) (hr : 0 < r)
    (hthr : ε * (l : ℝ) ≥ (p / (1 - p)) ^ r) (hdev : TruthAboveWindow u i l) :
    ∀ (m : ℕ),
      treeCount hn p ε u (fun t => ε ≤ recordPosterior t p i) m []
        ≤ (windowCellsAbove i l).card * (4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2) := by
  intro m
  have hdev' : (i : ℕ) + l < (u : ℕ) := hdev
  have hin : (i : ℕ) + l < n := by omega
  have hku : (i : ℕ) + l ≤ (u : ℕ) := by omega
  have hmono : treeCount hn p ε u (fun t => ε ≤ recordPosterior t p i) m []
      ≤ treeCount hn p ε u
        (fun t => ε ≤ recordPosterior t p i ∧
          ∃ k, k ∈ windowCellsAbove i l ∧ recordPosterior t p k ≤ 1 / (l : ℝ)) m [] := by
    refine treeCount_mono hn p ε u (fun t ht => ?_) hp hp1 m []
    obtain ⟨k, hk, hlight, hku'⟩ :=
      deviation_above_forces_light_cell hn p ε u i l hp hp1 hε hl t ht hdev'
    exact ⟨ht, k, hk, hlight⟩
  have h1 := upperWindow_light_tail_bound hn p ε u i l r hp hp1 hhalf hε hl hin hku hr hthr m
  linarith

/-- Under the stated threshold conditions, the tree count of any cell with posterior at least
`ε` at distance greater than `l` from the truth is at most `2 * n * l` times `4 * p * (1 -
p) * m / r^2`. -/
theorem clause13_deviation_bound {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u : Fin n) (l r : ℕ)
    (hp : 0 < p) (hp1 : p < 1) (hhalf : 1 / 2 < p) (hε : 0 < ε) (hl : 0 < l) (hr : 0 < r)
    (hthr : ε * (l : ℝ) ≥ (p / (1 - p)) ^ r) :
    ∀ (m : ℕ),
      treeCount hn p ε u
        (fun t => ∃ i : Fin n, ε ≤ recordPosterior t p i ∧
          ((u : ℕ) + l < (i : ℕ) ∨ (i : ℕ) + l < (u : ℕ))) m []
        ≤ 2 * (n : ℝ) * (l : ℝ) * (4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2) := by
  intro m
  have hX : 0 ≤ 4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2 := by
    have h1 : 0 ≤ 1 - p := by linarith
    have h2 : 0 ≤ (m : ℝ) := by positivity
    have h3 : 0 < (r : ℝ) ^ 2 := by positivity
    have h4 : 0 ≤ 4 * p * (1 - p) := by nlinarith
    exact div_nonneg (mul_nonneg h4 h2) (le_of_lt h3)
  let φL : Fin n → Record n → Prop := fun i t =>
    ε ≤ recordPosterior t p i ∧ (u : ℕ) + l < (i : ℕ)
  let φU : Fin n → Record n → Prop := fun i t =>
    ε ≤ recordPosterior t p i ∧ (i : ℕ) + l < (u : ℕ)
  have hlR : 0 ≤ (l : ℝ) := Nat.cast_nonneg l
  have hlX : 0 ≤ (l : ℝ) * (4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2) := mul_nonneg hlR hX

  have hsplit : treeCount hn p ε u
        (fun t => ∃ i : Fin n, ε ≤ recordPosterior t p i ∧
          ((u : ℕ) + l < (i : ℕ) ∨ (i : ℕ) + l < (u : ℕ))) m []
      ≤ treeCount hn p ε u (fun t => (∃ i, φL i t) ∨ (∃ i, φU i t)) m [] := by
    refine treeCount_mono hn p ε u (fun t ht => ?_) hp hp1 m []
    obtain ⟨i, hi⟩ := ht
    rcases hi.2 with hlo | hhi
    · exact Or.inl ⟨i, ⟨hi.1, hlo⟩⟩
    · exact Or.inr ⟨i, ⟨hi.1, hhi⟩⟩

  have hperL : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      treeCount hn p ε u (φL i) m [] ≤ (l : ℝ) * (4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2) := by
    intro i _
    by_cases hdev : (u : ℕ) + l < (i : ℕ)
    · have hlink : treeCount hn p ε u (φL i) m []
          ≤ treeCount hn p ε u
            (fun t => ε ≤ recordPosterior t p i ∧
              ∃ k, k ∈ windowCells i l ∧ recordPosterior t p k ≤ 1 / (l : ℝ)) m [] := by
        refine treeCount_mono hn p ε u (fun t ht => ?_) hp hp1 m []
        obtain ⟨k, hk, hlight, hku⟩ :=
          deviation_below_forces_light_cell hn p ε u i l hp hp1 hε hl t ht.1 hdev
        exact ⟨ht.1, k, hk, hlight⟩
      have hsub : treeCount hn p ε u
            (fun t => ε ≤ recordPosterior t p i ∧
              ∃ k, k ∈ windowCells i l ∧ recordPosterior t p k ≤ 1 / (l : ℝ)) m []
          ≤ treeCount hn p ε u (fun t => ε ≤ recordPosterior t p i) m [] :=
        treeCount_mono hn p ε u (fun t ht => ht.1) hp hp1 m []
      have hb := clause13_deviation_below_bound hn p ε u i l r hp hp1 hhalf hε hl hr hthr hdev m
      have hcardle := windowCells_card_le i l (by omega)
      have hcard : ((windowCells i l).card : ℝ) ≤ (l : ℝ) := by exact_mod_cast hcardle
      have hmul := mul_le_mul_of_nonneg_right hcard hX
      linarith
    · have hz : treeCount hn p ε u (φL i) m [] ≤ 0 := by
        refine (treeCount_mono hn p ε u (φ := φL i) (ψ := fun _ => False) ?_ hp hp1 m []).trans_eq
          (treeCount_false hn p ε u m [])
        intro t ht
        exact False.elim (hdev ht.2)
      linarith
  have hperU : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      treeCount hn p ε u (φU i) m [] ≤ (l : ℝ) * (4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2) := by
    intro i _
    by_cases hdev : (i : ℕ) + l < (u : ℕ)
    · have hlink : treeCount hn p ε u (φU i) m []
          ≤ treeCount hn p ε u
            (fun t => ε ≤ recordPosterior t p i ∧
              ∃ k, k ∈ windowCellsAbove i l ∧ recordPosterior t p k ≤ 1 / (l : ℝ)) m [] := by
        refine treeCount_mono hn p ε u (fun t ht => ?_) hp hp1 m []
        obtain ⟨k, hk, hlight, hku'⟩ :=
          deviation_above_forces_light_cell hn p ε u i l hp hp1 hε hl t ht.1 hdev
        exact ⟨ht.1, k, hk, hlight⟩
      have hsub : treeCount hn p ε u
            (fun t => ε ≤ recordPosterior t p i ∧
              ∃ k, k ∈ windowCellsAbove i l ∧ recordPosterior t p k ≤ 1 / (l : ℝ)) m []
          ≤ treeCount hn p ε u (fun t => ε ≤ recordPosterior t p i) m [] :=
        treeCount_mono hn p ε u (fun t ht => ht.1) hp hp1 m []
      have hb := clause13_deviation_above_bound hn p ε u i l r hp hp1 hhalf hε hl hr hthr hdev m
      have hcardeq := windowCellsAbove_card i l (by omega)
      have hcard : ((windowCellsAbove i l).card : ℝ) ≤ (l : ℝ) := by exact_mod_cast hcardeq.le
      have hmul := mul_le_mul_of_nonneg_right hcard hX
      linarith
    · have hz : treeCount hn p ε u (φU i) m [] ≤ 0 := by
        refine (treeCount_mono hn p ε u (φ := φU i) (ψ := fun _ => False) ?_ hp hp1 m []).trans_eq
          (treeCount_false hn p ε u m [])
        intro t ht
        exact False.elim (hdev ht.2)
      linarith

  have hunion := treeCount_union_le hn p ε u hp hp1
    (φ := fun t => ∃ i, φL i t) (ψ := fun t => ∃ i, φU i t) m []
  have hfinL : treeCount hn p ε u (fun t => ∃ i, φL i t) m []
      ≤ treeCountFinset hn p ε u (Finset.univ : Finset (Fin n)) φL m [] := by
    have hmono : treeCount hn p ε u (fun t => ∃ i, φL i t) m []
        ≤ treeCount hn p ε u
          (fun t => ∃ k ∈ (Finset.univ : Finset (Fin n)), φL k t) m [] := by
      refine treeCount_mono hn p ε u (φ := fun t => ∃ i, φL i t)
        (ψ := fun t => ∃ k ∈ (Finset.univ : Finset (Fin n)), φL k t)
        (fun t ht => ?_) hp hp1 m []
      obtain ⟨i, hi⟩ := ht
      exact ⟨i, Finset.mem_univ i, hi⟩
    exact hmono.trans
      (treeCount_exists_le_finset hn p ε u (Finset.univ : Finset (Fin n)) φL hp hp1 m [])
  have hfinU : treeCount hn p ε u (fun t => ∃ i, φU i t) m []
      ≤ treeCountFinset hn p ε u (Finset.univ : Finset (Fin n)) φU m [] := by
    have hmono : treeCount hn p ε u (fun t => ∃ i, φU i t) m []
        ≤ treeCount hn p ε u
          (fun t => ∃ k ∈ (Finset.univ : Finset (Fin n)), φU k t) m [] := by
      refine treeCount_mono hn p ε u (φ := fun t => ∃ i, φU i t)
        (ψ := fun t => ∃ k ∈ (Finset.univ : Finset (Fin n)), φU k t)
        (fun t ht => ?_) hp hp1 m []
      obtain ⟨i, hi⟩ := ht
      exact ⟨i, Finset.mem_univ i, hi⟩
    exact hmono.trans
      (treeCount_exists_le_finset hn p ε u (Finset.univ : Finset (Fin n)) φU hp hp1 m [])
  have hsumL := treeCountFinset_eq_sum hn p ε u (Finset.univ : Finset (Fin n)) φL m []
  have hsumU := treeCountFinset_eq_sum hn p ε u (Finset.univ : Finset (Fin n)) φU m []
  calc treeCount hn p ε u
        (fun t => ∃ i : Fin n, ε ≤ recordPosterior t p i ∧
          ((u : ℕ) + l < (i : ℕ) ∨ (i : ℕ) + l < (u : ℕ))) m []
      ≤ treeCount hn p ε u (fun t => (∃ i, φL i t) ∨ (∃ i, φU i t)) m [] := hsplit
    _ ≤ treeCount hn p ε u (fun t => ∃ i, φL i t) m []
        + treeCount hn p ε u (fun t => ∃ i, φU i t) m [] := hunion
    _ ≤ treeCountFinset hn p ε u (Finset.univ : Finset (Fin n)) φL m []
        + treeCountFinset hn p ε u (Finset.univ : Finset (Fin n)) φU m [] := by
      have h1 := hfinL
      have h2 := hfinU
      linarith
    _ = (∑ i ∈ (Finset.univ : Finset (Fin n)), treeCount hn p ε u (φL i) m [])
        + (∑ i ∈ (Finset.univ : Finset (Fin n)), treeCount hn p ε u (φU i) m []) := by
      rw [hsumL, hsumU]
    _ ≤ (∑ _i ∈ (Finset.univ : Finset (Fin n)), (l : ℝ) * (4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2))
        + (∑ _i ∈ (Finset.univ : Finset (Fin n)), (l : ℝ) * (4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2)) := by
      have h1 : (∑ i ∈ (Finset.univ : Finset (Fin n)), treeCount hn p ε u (φL i) m [])
          ≤ (∑ _i ∈ (Finset.univ : Finset (Fin n)),
              (l : ℝ) * (4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2)) :=
        Finset.sum_le_sum fun i _ => hperL i (Finset.mem_univ i)
      have h2 : (∑ i ∈ (Finset.univ : Finset (Fin n)), treeCount hn p ε u (φU i) m [])
          ≤ (∑ _i ∈ (Finset.univ : Finset (Fin n)),
              (l : ℝ) * (4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2)) :=
        Finset.sum_le_sum fun i _ => hperU i (Finset.mem_univ i)
      linarith
    _ = 2 * (n : ℝ) * (l : ℝ) * (4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2) := by
      rw [Finset.sum_const, Finset.card_univ]
      simp [nsmul_eq_mul]
      ring

/-- If `2 * n * l * 4 * p * (1 - p) * m ≤ δ * r^2`, the distant heavy-cell event has tree count
at most positive `δ` under the stated threshold conditions. -/
theorem clause13_deviation_calibration {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u : Fin n) (l r : ℕ)
    (hp : 0 < p) (hp1 : p < 1) (hhalf : 1 / 2 < p) (hε : 0 < ε) (hl : 0 < l) (hr : 0 < r)
    (hthr : ε * (l : ℝ) ≥ (p / (1 - p)) ^ r) (δ : ℝ) (hδ : 0 < δ) :
    ∀ (m : ℕ),
      2 * (n : ℝ) * (l : ℝ) * 4 * p * (1 - p) * (m : ℝ) ≤ δ * (r : ℝ) ^ 2 →
        treeCount hn p ε u
          (fun t => ∃ i : Fin n, ε ≤ recordPosterior t p i ∧
            ((u : ℕ) + l < (i : ℕ) ∨ (i : ℕ) + l < (u : ℕ))) m [] ≤ δ := by
  intro m hcal
  have h1 := clause13_deviation_bound hn p ε u l r hp hp1 hhalf hε hl hr hthr m
  have hr2 : 0 < (r : ℝ) ^ 2 := by positivity
  have hr2ne : (r : ℝ) ^ 2 ≠ 0 := ne_of_gt hr2
  have hmul : treeCount hn p ε u
        (fun t => ∃ i : Fin n, ε ≤ recordPosterior t p i ∧
          ((u : ℕ) + l < (i : ℕ) ∨ (i : ℕ) + l < (u : ℕ))) m []
        * (r : ℝ) ^ 2
      ≤ (2 * (n : ℝ) * (l : ℝ) * (4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2)) * (r : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right h1 (le_of_lt hr2)
  have heq : (2 * (n : ℝ) * (l : ℝ) * (4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2)) * (r : ℝ) ^ 2
      = 2 * (n : ℝ) * (l : ℝ) * 4 * p * (1 - p) * (m : ℝ) := by
    field_simp
    <;> ring
  have h2 : treeCount hn p ε u
        (fun t => ∃ i : Fin n, ε ≤ recordPosterior t p i ∧
          ((u : ℕ) + l < (i : ℕ) ∨ (i : ℕ) + l < (u : ℕ))) m []
        * (r : ℝ) ^ 2 ≤ 2 * (n : ℝ) * (l : ℝ) * 4 * p * (1 - p) * (m : ℝ) := by
    rw [heq] at hmul
    exact hmul
  have h3 : treeCount hn p ε u
        (fun t => ∃ i : Fin n, ε ≤ recordPosterior t p i ∧
          ((u : ℕ) + l < (i : ℕ) ∨ (i : ℕ) + l < (u : ℕ))) m []
        * (r : ℝ) ^ 2 ≤ δ * (r : ℝ) ^ 2 := by linarith
  have h4 : (r : ℝ) ^ 2 * treeCount hn p ε u
        (fun t => ∃ i : Fin n, ε ≤ recordPosterior t p i ∧
          ((u : ℕ) + l < (i : ℕ) ∨ (i : ℕ) + l < (u : ℕ))) m []
        ≤ (r : ℝ) ^ 2 * δ := by simpa [mul_comm] using! h3
  exact le_of_mul_le_mul_left h4 hr2

/-- Collects light-cell witnesses for deviations on either side, the corresponding concentration
bounds, their union bound, and calibration to `δ`. These give the stated finite-tree
deviation estimates associated with [Ben-Or and Hassidim, Lemma 2.5][BenOrHassidim2007]. -/
theorem clause13_deviation_endpoint :
    (∀ (n : ℕ) (p ε : ℝ) (u i : Fin n) (l : ℕ) (hn : 0 < n) (hp : 0 < p) (hp1 : p < 1)
      (hε : 0 < ε) (hl : 0 < l) (t : Record n),
      ε ≤ recordPosterior t p i → TruthBelowWindow u i l →
        ∃ k, k ∈ windowCells i l ∧ recordPosterior t p k ≤ 1 / (l : ℝ) ∧ (u : ℕ) ≤ (k : ℕ)) ∧
    (∀ (n : ℕ) (p ε : ℝ) (u i : Fin n) (l : ℕ) (hn : 0 < n) (hp : 0 < p) (hp1 : p < 1)
      (hε : 0 < ε) (hl : 0 < l) (t : Record n),
      ε ≤ recordPosterior t p i → TruthAboveWindow u i l →
        ∃ k, k ∈ windowCellsAbove i l ∧ recordPosterior t p k ≤ 1 / (l : ℝ)
          ∧ (k : ℕ) ≤ (u : ℕ)) ∧
    (∀ (n : ℕ) (p ε : ℝ) (u i : Fin n) (l r : ℕ) (hn : 0 < n) (hp : 0 < p) (hp1 : p < 1)
      (hhalf : 1 / 2 < p) (hε : 0 < ε) (hl : 0 < l) (hr : 0 < r)
      (hthr : ε * (l : ℝ) ≥ (p / (1 - p)) ^ r) (hdev : TruthBelowWindow u i l) (m : ℕ),
      treeCount hn p ε u (fun t => ε ≤ recordPosterior t p i) m []
        ≤ (windowCells i l).card * (4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2)) ∧
    (∀ (n : ℕ) (p ε : ℝ) (u i : Fin n) (l r : ℕ) (hn : 0 < n) (hp : 0 < p) (hp1 : p < 1)
      (hhalf : 1 / 2 < p) (hε : 0 < ε) (hl : 0 < l) (hr : 0 < r)
      (hthr : ε * (l : ℝ) ≥ (p / (1 - p)) ^ r) (hdev : TruthAboveWindow u i l) (m : ℕ),
      treeCount hn p ε u (fun t => ε ≤ recordPosterior t p i) m []
        ≤ (windowCellsAbove i l).card * (4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2)) ∧
    (∀ (n : ℕ) (p ε : ℝ) (u : Fin n) (l r : ℕ) (hn : 0 < n) (hp : 0 < p) (hp1 : p < 1)
      (hhalf : 1 / 2 < p) (hε : 0 < ε) (hl : 0 < l) (hr : 0 < r)
      (hthr : ε * (l : ℝ) ≥ (p / (1 - p)) ^ r) (m : ℕ),
      treeCount hn p ε u
        (fun t => ∃ i : Fin n, ε ≤ recordPosterior t p i ∧
          ((u : ℕ) + l < (i : ℕ) ∨ (i : ℕ) + l < (u : ℕ))) m []
        ≤ 2 * (n : ℝ) * (l : ℝ) * (4 * p * (1 - p) * (m : ℝ) / (r : ℝ) ^ 2)) ∧
    (∀ (n : ℕ) (p ε : ℝ) (u : Fin n) (l r : ℕ) (hn : 0 < n) (hp : 0 < p) (hp1 : p < 1)
      (hhalf : 1 / 2 < p) (hε : 0 < ε) (hl : 0 < l) (hr : 0 < r)
      (hthr : ε * (l : ℝ) ≥ (p / (1 - p)) ^ r) (δ : ℝ) (hδ : 0 < δ) (m : ℕ),
      2 * (n : ℝ) * (l : ℝ) * 4 * p * (1 - p) * (m : ℝ) ≤ δ * (r : ℝ) ^ 2 →
        treeCount hn p ε u
          (fun t => ∃ i : Fin n, ε ≤ recordPosterior t p i ∧
            ((u : ℕ) + l < (i : ℕ) ∨ (i : ℕ) + l < (u : ℕ))) m [] ≤ δ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n p ε u i l hn hp hp1 hε hl t hhi hdev
    exact deviation_below_forces_light_cell hn p ε u i l hp hp1 hε hl t hhi hdev
  · intro n p ε u i l hn hp hp1 hε hl t hhi hdev
    exact deviation_above_forces_light_cell hn p ε u i l hp hp1 hε hl t hhi hdev
  · intro n p ε u i l r hn hp hp1 hhalf hε hl hr hthr hdev m
    exact clause13_deviation_below_bound hn p ε u i l r hp hp1 hhalf hε hl hr hthr hdev m
  · intro n p ε u i l r hn hp hp1 hhalf hε hl hr hthr hdev m
    exact clause13_deviation_above_bound hn p ε u i l r hp hp1 hhalf hε hl hr hthr hdev m
  · intro n p ε u l r hn hp hp1 hhalf hε hl hr hthr m
    exact clause13_deviation_bound hn p ε u l r hp hp1 hhalf hε hl hr hthr m
  · intro n p ε u l r hn hp hp1 hhalf hε hl hr hthr δ hδ m hcal
    exact clause13_deviation_calibration hn p ε u l r hp hp1 hhalf hε hl hr hthr δ hδ m hcal

/-- The sum of true- and false-crossing counts equals the number of crossing observations in the
record. -/
theorem crossTrue_add_crossFalse {n : ℕ} (k i : Fin n) (t : Record n) :
    crossTrue k i t + crossFalse k i t = (t.filter (fun obs => IsCrossing k i obs)).length := by
  induction t with
  | nil => rfl
  | cons obs t ih =>
    by_cases hc : IsCrossing k i obs
    · by_cases hb : obs.2
      · simp only [crossTrue, crossFalse, List.filter_cons]
        simp [hc, hb]
        omega
      · simp only [crossTrue, crossFalse, List.filter_cons]
        simp [hc, hb]
        omega
    · simp only [crossTrue, crossFalse, List.filter_cons]
      simp [hc]
      omega

/-- The cut of every observation in a record belongs to its cut list. -/
theorem mem_cutList {n : ℕ} (t : Record n) (obs : Comparison n) (hobs : obs ∈ t) :
    obs.1 ∈ cutList t := by
  induction t with
  | nil => simp at hobs
  | cons o t ih =>
    simp only [cutList, List.mem_cons] at *
    rcases hobs with h | h
    · subst h
      exact Or.inl rfl
    · exact Or.inr (ih h)

/-- A record satisfying `NoDupCuts` has a cut list without repetitions. -/
theorem cutList_nodup {n : ℕ} (t : Record n) (hnd : NoDupCuts t) : (cutList t).Nodup := by
  induction t with
  | nil => simp [cutList, NoDupCuts]
  | cons obs t ih =>
    simp only [cutList] at *
    exact List.nodup_cons.mpr ⟨hnd.1, ih hnd.2⟩

/-- If a record has no repeated cuts, the natural-number cuts of its crossing observations have
no repetitions. -/
theorem crossing_cuts_nodup {n : ℕ} (k i : Fin n) (t : Record n) (hnd : NoDupCuts t) :
    ((t.filter (fun obs => IsCrossing k i obs)).map (fun obs => (obs.1 : ℕ))).Nodup := by
  induction t with
  | nil => simp
  | cons obs t ih =>
    have hnd' := hnd
    simp only [NoDupCuts] at hnd'
    have htail : ((t.filter (fun o => IsCrossing k i o)).map (fun o => (o.1 : ℕ))).Nodup :=
      ih hnd'.2
    by_cases hc : IsCrossing k i obs
    · have hfilter : (obs :: t).filter (fun o => IsCrossing k i o)
          = obs :: (t.filter (fun o => IsCrossing k i o)) := by
        simp [hc]
      rw [hfilter]
      refine List.nodup_cons.mpr ⟨?_, htail⟩
      intro hmem
      simp only [List.mem_map, List.mem_filter] at hmem
      obtain ⟨obs2, hobs2, hfst⟩ := hmem
      have hval : (obs2.1 : ℕ) = (obs.1 : ℕ) := hfst
      have hfin : obs2.1 = obs.1 := Fin.val_injective hval
      have hobs2mem : obs2 ∈ t := hobs2.1
      have hcl : obs.1 ∈ cutList t := by
        have h2 := mem_cutList t obs2 hobs2mem
        rwa [hfin] at h2
      exact hnd'.1 hcl
    · have hfilter : (obs :: t).filter (fun o => IsCrossing k i o)
          = t.filter (fun o => IsCrossing k i o) := by
        simp [hc]
      rw [hfilter]
      exact htail

/-- Every observation crossing from `k` to `i` has its cut strictly above `k` and at most `i`. -/
theorem crossing_cuts_mem_window {n : ℕ} (k i : Fin n) (t : Record n)
    (obs : Comparison n) (hmem : obs ∈ t.filter (fun o => IsCrossing k i o)) :
    (k : ℕ) < obs.1.val ∧ obs.1.val ≤ (i : ℕ) := by
  have h := (List.mem_filter.mp hmem).2
  have h2 : IsCrossing k i obs := of_decide_eq_true h
  exact h2

/-- For `k < i` and a record without repeated cuts, the total crossing count is at most `i - k`. -/
theorem cross_steps_le_span {n : ℕ} (k i : Fin n) (t : Record n) (hnd : NoDupCuts t)
    (hki : (k : ℕ) < (i : ℕ)) :
    crossTrue k i t + crossFalse k i t ≤ (i : ℕ) - (k : ℕ) := by
  have hnodup := crossing_cuts_nodup k i t hnd
  have hcard :
      ((t.filter (fun obs => IsCrossing k i obs)).map (fun obs => (obs.1 : ℕ))).toFinset.card
        ≤ ((Finset.Icc ((k : ℕ) + 1) (i : ℕ)) : Finset ℕ).card := by
    refine Finset.card_le_card ?_
    intro x hx
    simp only [List.mem_toFinset, List.mem_map] at hx
    obtain ⟨obs, hobs, hfst⟩ := hx
    have hwin := crossing_cuts_mem_window k i t obs hobs
    rw [← hfst]
    simp only [Finset.mem_Icc]
    omega
  have hcard2 :
      ((t.filter (fun obs => IsCrossing k i obs)).map (fun obs => (obs.1 : ℕ))).toFinset.card
        = (t.filter (fun obs => IsCrossing k i obs)).length := by
    calc ((t.filter (fun obs => IsCrossing k i obs)).map (fun obs => (obs.1 : ℕ))).toFinset.card
        = ((t.filter (fun obs => IsCrossing k i obs)).map (fun obs => (obs.1 : ℕ))).length :=
          List.toFinset_card_of_nodup hnodup
      _ = (t.filter (fun obs => IsCrossing k i obs)).length := by rw [List.length_map]
  have hcard3 : ((Finset.Icc ((k : ℕ) + 1) (i : ℕ)) : Finset ℕ).card
      = (i : ℕ) + 1 - ((k : ℕ) + 1) := Nat.card_Icc _ _
  have hlen := crossTrue_add_crossFalse k i t
  rw [hlen]
  omega

/-- For `k < i` and a record without repeated cuts, the true-crossing count is at most `i - k`. -/
theorem crossTrue_le_span {n : ℕ} (k i : Fin n) (t : Record n) (hnd : NoDupCuts t)
    (hki : (k : ℕ) < (i : ℕ)) :
    crossTrue k i t ≤ (i : ℕ) - (k : ℕ) := by
  have h := cross_steps_le_span k i t hnd hki
  omega

/-- For `k < i`, no repeated cuts, and `1 / 2 < p < 1`, the record ratio is at most `(p / (1 -
p)) ^ (i - k)`. -/
theorem recordRatio_le_span_pow {n : ℕ} (p : ℝ) (k i : Fin n) (t : Record n) (hnd : NoDupCuts t)
    (hki : (k : ℕ) < (i : ℕ)) (hp : 0 < p) (hp1 : p < 1) (hhalf : 1 / 2 < p) :
    recordRatio t k i p ≤ (p / (1 - p)) ^ ((i : ℕ) - (k : ℕ)) := by
  have hq : 1 ≤ p / (1 - p) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have htrue := crossTrue_le_span k i t hnd hki
  have hfalse : crossFalse k i t ≤ (i : ℕ) - (k : ℕ) := by
    have h := cross_steps_le_span k i t hnd hki
    omega
  have hpow : (p / (1 - p)) ^ crossTrue k i t
      ≤ (p / (1 - p)) ^ ((i : ℕ) - (k : ℕ)) := by
    exact pow_le_pow_right₀ hq htrue
  have hinv : ((1 - p) / p) ^ crossFalse k i t ≤ 1 := by
    have hbase : (1 - p) / p ≤ 1 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < p)]
      linarith
    exact pow_le_one₀ (by positivity : 0 ≤ (1 - p) / p) hbase
  rw [recordRatio_eq_crossFactors p k i hp hp1 hki t]
  calc (p / (1 - p)) ^ crossTrue k i t * ((1 - p) / p) ^ crossFalse k i t
      ≤ (p / (1 - p)) ^ ((i : ℕ) - (k : ℕ)) * ((1 - p) / p) ^ crossFalse k i t :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
    _ ≤ (p / (1 - p)) ^ ((i : ℕ) - (k : ℕ)) * 1 :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = (p / (1 - p)) ^ ((i : ℕ) - (k : ℕ)) := by ring

/-- For `k < i`, no repeated cuts, and `1 / 2 < p < 1`, a record ratio at least `(p / (1 - p)) ^
r` implies `r ≤ i - k`. -/
theorem r_le_span_of_ratio {n : ℕ} (p : ℝ) (k i : Fin n) (t : Record n) (hnd : NoDupCuts t)
    (hki : (k : ℕ) < (i : ℕ)) (hp : 0 < p) (hp1 : p < 1) (hhalf : 1 / 2 < p) (r : ℕ)
    (hratio : (p / (1 - p)) ^ r ≤ recordRatio t k i p) :
    r ≤ (i : ℕ) - (k : ℕ) := by
  have hq : 1 < p / (1 - p) := by
    rw [lt_div_iff₀ (by linarith)]
    linarith
  have hspan := recordRatio_le_span_pow p k i t hnd hki hp hp1 hhalf
  have hle : (p / (1 - p)) ^ r ≤ (p / (1 - p)) ^ ((i : ℕ) - (k : ℕ)) :=
    le_trans hratio hspan
  exact (pow_le_pow_iff_right₀ hq).mp hle

/-- The noisy probability of a true comparison answer equals the Bayesian true-answer
likelihood. -/
theorem noisyAnswerProb_eq_bayesTrueLikelihood {n : ℕ} (j c : Fin n) (p : ℝ) :
    noisyAnswerProb j c p = bayesTrueLikelihood c j p := rfl

/-- The complement of the noisy true-answer probability equals the Bayesian false-answer
likelihood. -/
theorem noisyAnswerProb_compl_eq_bayesFalseLikelihood {n : ℕ} (j c : Fin n) (p : ℝ) :
    1 - noisyAnswerProb j c p = bayesFalseLikelihood c j p := by
  by_cases h : (c : ℕ) ≤ (j : ℕ)
  · simp [noisyAnswerProb, bayesFalseLikelihood, h]
  · simp [noisyAnswerProb, bayesFalseLikelihood, h]

/-- The false-answer Bayesian likelihood is positive when `0 < p < 1`. -/
theorem bayesFalseLikelihood_pos {n : ℕ} (c m : Fin n) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    0 < bayesFalseLikelihood c m p := by
  by_cases h : (c : ℕ) <= (m : ℕ)
  · unfold bayesFalseLikelihood; rw [if_pos h]; linarith
  · unfold bayesFalseLikelihood; rw [if_neg h]; linarith

/-- A pointwise positive prior on a nonempty search space gives a positive false-answer
normalizer when `0 < p < 1`. -/
theorem bayesFalseNorm_pos {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (c : Fin n) (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hpos : ∀ j, 0 < a j) : 0 < bayesFalseNorm a c p := by
  unfold bayesFalseNorm
  refine Finset.sum_pos' (s := (Finset.univ : Finset (Fin n))) (fun j _ => ?_) ?_
  · exact le_of_lt (mul_pos (hpos j) (bayesFalseLikelihood_pos c j p hp hp1))
  · exact ⟨⟨0, hn⟩, Finset.mem_univ _,
      mul_pos (hpos ⟨0, hn⟩) (bayesFalseLikelihood_pos c ⟨0, hn⟩ p hp hp1)⟩

/-- A pointwise positive prior on a nonempty search space gives a positive true-answer
normalizer when `0 < p < 1`. -/
theorem bayesTrueNorm_pos {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (c : Fin n) (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hpos : ∀ j, 0 < a j) : 0 < bayesTrueNorm a c p := by
  unfold bayesTrueNorm
  refine Finset.sum_pos' (s := (Finset.univ : Finset (Fin n))) (fun j _ => ?_) ?_
  · exact le_of_lt (mul_pos (hpos j) (bayesTrueLikelihood_pos c j p hp hp1))
  · exact ⟨⟨0, hn⟩, Finset.mem_univ _,
      mul_pos (hpos ⟨0, hn⟩) (bayesTrueLikelihood_pos c ⟨0, hn⟩ p hp hp1)⟩

/-- A pointwise positive prior on a nonempty search space gives a pointwise positive
false-answer posterior when `0 < p < 1`. -/
theorem bayesFalsePost_pos {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (c : Fin n) (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hpos : ∀ j, 0 < a j) : ∀ j, 0 < bayesFalsePost a c p j := by
  intro j
  have hN : 0 < bayesFalseNorm a c p := bayesFalseNorm_pos hn a c p hp hp1 hpos
  have hnum : 0 < a j * bayesFalseLikelihood c j p :=
    mul_pos (hpos j) (bayesFalseLikelihood_pos c j p hp hp1)
  unfold bayesFalsePost
  exact div_pos hnum hN

/-- A pointwise positive prior on a nonempty search space gives a pointwise positive true-answer
posterior when `0 < p < 1`. -/
theorem bayesTruePost_pos {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (c : Fin n) (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hpos : ∀ j, 0 < a j) : ∀ j, 0 < bayesTruePost a c p j := by
  intro j
  have hN : 0 < bayesTrueNorm a c p := bayesTrueNorm_pos hn a c p hp hp1 hpos
  have hnum : 0 < a j * bayesTrueLikelihood c j p :=
    mul_pos (hpos j) (bayesTrueLikelihood_pos c j p hp hp1)
  unfold bayesTruePost
  exact div_pos hnum hN

/-- Multiplying a false-answer posterior-weighted sum by its nonzero normalizer recovers the
prior-and-likelihood-weighted sum. -/
theorem bayesFalsePost_mul_norm {n : ℕ} (a : Fin n → ℝ) (c : Fin n) (p : ℝ)
    (f : Fin n → ℝ) (hN : bayesFalseNorm a c p ≠ 0) :
    bayesFalseNorm a c p * ∑ j, bayesFalsePost a c p j * f j
      = ∑ j, a j * bayesFalseLikelihood c j p * f j := by
  simp only [bayesFalsePost]
  calc bayesFalseNorm a c p * ∑ j, (a j * bayesFalseLikelihood c j p / bayesFalseNorm a c p) * f j
      = ∑ j, bayesFalseNorm a c p * ((a j * bayesFalseLikelihood c j p / bayesFalseNorm a c p) * f j) := by
        rw [Finset.mul_sum]
    _ = ∑ j, (a j * bayesFalseLikelihood c j p) * f j := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        field_simp [hN]
    _ = ∑ j, a j * bayesFalseLikelihood c j p * f j := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring

/-- Multiplying a true-answer posterior-weighted sum by its nonzero normalizer recovers the
prior-and-likelihood-weighted sum. -/
theorem bayesTruePost_mul_norm {n : ℕ} (a :Fin n → ℝ) (c : Fin n) (p : ℝ)
    (f : Fin n → ℝ) (hN : bayesTrueNorm a c p ≠ 0) :
    bayesTrueNorm a c p * ∑ j, bayesTruePost a c p j * f j
      = ∑ j, a j * bayesTrueLikelihood c j p * f j := by
  simp only [bayesTruePost]
  calc bayesTrueNorm a c p * ∑ j, (a j * bayesTrueLikelihood c j p / bayesTrueNorm a c p) * f j
      = ∑ j, bayesTrueNorm a c p * ((a j * bayesTrueLikelihood c j p / bayesTrueNorm a c p) * f j) := by
        rw [Finset.mul_sum]
    _ = ∑ j, (a j * bayesTrueLikelihood c j p) * f j := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        field_simp [hN]
    _ = ∑ j, a j * bayesTrueLikelihood c j p * f j := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring

/-- For a positive normalized prior on a nonempty search space and `0 < p < 1`, weighted tree
depth equals the initial weight times the prior average of inputwise noisy expected queries. -/
theorem treeDepth_eq_avg {n : ℕ} (hn : 0 < n) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (tr : BoolQueryTree (Fin n) (Fin n)) :
    ∀ (a : Fin n → ℝ) (W : ℝ),
      (∑ j, a j) = 1 → (∀ j, 0 < a j) →
      treeDepth p tr a W = W * ∑ j, a j * noisyExpectedQueries j p tr := by
  induction tr with
  | halt o =>
    intro a W hsum hpos
    simp [treeDepth, noisyExpectedQueries]
  | ask c onFalse onTrue ihF ihT =>
    intro a W hsum hpos
    have hNF : 0 < bayesFalseNorm a c p := bayesFalseNorm_pos hn a c p hp hp1 hpos
    have hNT : 0 < bayesTrueNorm a c p := bayesTrueNorm_pos hn a c p hp hp1 hpos
    have hNF0 : bayesFalseNorm a c p ≠ 0 := ne_of_gt hNF
    have hNT0 : bayesTrueNorm a c p ≠ 0 := ne_of_gt hNT
    have hsumF : (∑ j, bayesFalsePost a c p j) = 1 :=
      bayesFalsePost_sum a c p (fun j => le_of_lt (hpos j)) hsum hp hp1
    have hsumT : (∑ j, bayesTruePost a c p j) = 1 :=
      bayesTruePost_sum a c p (fun j => le_of_lt (hpos j)) hsum hp hp1
    have hposF : ∀ j, 0 < bayesFalsePost a c p j :=
      bayesFalsePost_pos hn a c p hp hp1 hpos
    have hposT : ∀ j, 0 < bayesTruePost a c p j :=
      bayesTruePost_pos hn a c p hp hp1 hpos
    have hF := ihF (bayesFalsePost a c p) (W * bayesFalseNorm a c p) hsumF hposF
    have hT := ihT (bayesTruePost a c p) (W * bayesTrueNorm a c p) hsumT hposT
    have hkeyF : bayesFalseNorm a c p
          * ∑ j, bayesFalsePost a c p j * noisyExpectedQueries j p onFalse
        = ∑ j, a j * bayesFalseLikelihood c j p * noisyExpectedQueries j p onFalse := by
      exact bayesFalsePost_mul_norm a c p (fun j => noisyExpectedQueries j p onFalse) hNF0
    have hkeyT : bayesTrueNorm a c p
          * ∑ j, bayesTruePost a c p j * noisyExpectedQueries j p onTrue
        = ∑ j, a j * bayesTrueLikelihood c j p * noisyExpectedQueries j p onTrue := by
      exact bayesTruePost_mul_norm a c p (fun j => noisyExpectedQueries j p onTrue) hNT0
    simp only [treeDepth]
    rw [hF, hT]
    rw [mul_assoc, mul_assoc]
    rw [hkeyF, hkeyT]
    calc W + W * (∑ j, a j * bayesFalseLikelihood c j p
            * noisyExpectedQueries j p onFalse)
        + W * (∑ j, a j * bayesTrueLikelihood c j p
            * noisyExpectedQueries j p onTrue)
        = W * (1 + (∑ j, a j * bayesFalseLikelihood c j p
              * noisyExpectedQueries j p onFalse)
          + (∑ j, a j * bayesTrueLikelihood c j p
              * noisyExpectedQueries j p onTrue)) := by ring
      _ = W * ((∑ j, a j) + ((∑ j, a j * bayesFalseLikelihood c j p
              * noisyExpectedQueries j p onFalse)
          + (∑ j, a j * bayesTrueLikelihood c j p
              * noisyExpectedQueries j p onTrue))) := by rw [hsum]; ring
      _ = W * ∑ j, (a j + (a j * bayesFalseLikelihood c j p
            * noisyExpectedQueries j p onFalse
          + a j * bayesTrueLikelihood c j p
            * noisyExpectedQueries j p onTrue)) := by
            rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      _ = W * ∑ j, a j * (1 + (bayesFalseLikelihood c j p
            * noisyExpectedQueries j p onFalse
          + bayesTrueLikelihood c j p * noisyExpectedQueries j p onTrue)) := by
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            ring
      _ = W * ∑ j, a j * noisyExpectedQueries j p (.ask c onFalse onTrue) := by
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            simp only [noisyExpectedQueries]
            rw [noisyAnswerProb_compl_eq_bayesFalseLikelihood]
            rw [noisyAnswerProb_eq_bayesTrueLikelihood]
            ring

/-- For a nonempty search space and `0 < p < 1`, uniform expected queries equal the arithmetic
mean of inputwise noisy expected query counts. -/
theorem uniformExpectedQueries_eq_avg {n : ℕ} (hn : 0 < n) (p : ℝ) (hp : 0 < p)
    (hp1 : p < 1) (tr : BoolQueryTree (Fin n) (Fin n)) :
    uniformExpectedQueries p tr = (1 / n) * ∑ j, noisyExpectedQueries j p tr := by
  have hpos : ∀ j, 0 < uniformPosterior (n := n) j := by
    intro j
    simp only [uniformPosterior]
    exact div_pos (by norm_num) (by exact_mod_cast (Nat.cast_pos.mpr hn))
  have h1 := treeDepth_eq_avg hn p hp hp1 tr (uniformPosterior (n := n)) 1
    (uniform_sum hn) hpos
  rw [show uniformExpectedQueries p tr = treeDepth p tr (uniformPosterior (n := n)) 1 from rfl]
  rw [h1]
  simp only [uniformPosterior]
  rw [← Finset.mul_sum]
  ring

/-- The number of oracle applications in a record equals its query count. -/
theorem oracleApplications_eq_recordQueries {n : ℕ} (t : Record n) :
    oracleApplications t = recordQueries t := rfl

/-- For a nonempty search space and `0 < p < 1`, uniform expected queries equal the average of
inputwise expected oracle applications. -/
theorem levelExpectedOracleApplications_eq_avg {n : ℕ} (hn : 0 < n) (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (tr : BoolQueryTree (Fin n) (Fin n)) :
    uniformExpectedQueries p tr
      = (1 / n) * ∑ j, noisyExpectedOracleApplications j p tr := by
  rw [uniformExpectedQueries_eq_avg hn p hp hp1 tr]
  rfl

/-- For a nonempty search space and `0 < p < 1`, recursive expected oracle applications equal `1
/ n` times the sum of inputwise expected oracle applications across levels. -/
theorem recursiveExpectedOracleApplications_eq_sum {n : ℕ} (hn : 0 < n) (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (levels : List (BoolQueryTree (Fin n) (Fin n))) :
    recursiveExpectedOracleApplications p levels
      = (1 / n) * levels.foldr
          (fun tr acc => ∑ j, noisyExpectedOracleApplications j p tr + acc) 0 := by
  induction levels with
  | nil =>
    simp [recursiveExpectedOracleApplications]
  | cons tr levels ih =>
    have htr := levelExpectedOracleApplications_eq_avg hn p hp hp1 tr
    have hsplit : recursiveExpectedOracleApplications p (tr :: levels)
        = uniformExpectedQueries p tr + recursiveExpectedOracleApplications p levels := by
      simp only [recursiveExpectedOracleApplications, List.foldr_cons]
    rw [hsplit, ih, htr]
    simp only [List.foldr_cons, noisyExpectedOracleApplications]
    ring

/-- Collects the answer-probability semantics, posterior normalization, uniform averaging of
expected queries, and equality and additivity of oracle-application costs. -/
theorem clause16_cost_endpoint :
    (∀ (n : ℕ) (j c : Fin n) (p : ℝ),
      noisyAnswerProb j c p = bayesTrueLikelihood c j p) ∧
    (∀ (n : ℕ) (j c : Fin n) (p : ℝ),
      1 - noisyAnswerProb j c p = bayesFalseLikelihood c j p) ∧
    (∀ (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ) (c : Fin n) (p : ℝ)
      (ha : ∀ j, 0 ≤ a j) (hsum : (∑ j, a j) = 1) (hp : 0 < p) (hp1 : p < 1),
      (∑ j, bayesFalsePost a c p j) = 1 ∧ (∑ j, bayesTruePost a c p j) = 1) ∧
    (∀ (n : ℕ) (hn : 0 < n) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
      (tr : BoolQueryTree (Fin n) (Fin n)),
      uniformExpectedQueries p tr = (1 / n) * ∑ j, noisyExpectedQueries j p tr) ∧
    (∀ (n : ℕ) (t : Record n), oracleApplications t = recordQueries t) ∧
    (∀ (n : ℕ) (hn : 0 < n) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
      (levels : List (BoolQueryTree (Fin n) (Fin n))),
      recursiveExpectedOracleApplications p levels
        = (1 / n) * levels.foldr
            (fun tr acc => ∑ j, noisyExpectedOracleApplications j p tr + acc) 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n j c p
    exact noisyAnswerProb_eq_bayesTrueLikelihood j c p
  · intro n j c p
    exact noisyAnswerProb_compl_eq_bayesFalseLikelihood j c p
  · intro n hn a c p ha hsum hp hp1
    exact ⟨bayesFalsePost_sum a c p ha hsum hp hp1, bayesTruePost_sum a c p ha hsum hp hp1⟩
  · intro n hn p hp hp1 tr
    exact uniformExpectedQueries_eq_avg hn p hp hp1 tr
  · intro n t
    exact oracleApplications_eq_recordQueries t
  · intro n hn p hp hp1 levels
    exact recursiveExpectedOracleApplications_eq_sum hn p hp hp1 levels

end Qatlib.Concepts.OrderedBayes.BayesRatioCore.OrderedSearch

end

set_option autoImplicit false
