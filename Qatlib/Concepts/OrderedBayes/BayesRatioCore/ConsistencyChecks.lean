/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma23Quan
import Qatlib.Concepts.OrderedBayes.BayesRatioCore.BayesTruthDefs
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
set_option warningAsError false

open Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma23Quan
open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore.ConsistencyChecks
open Qatlib.Concepts.OrderedBayes.BayesRatioCore
open scoped Matrix

theorem reported_quantum_coefficient_exceeds_printed_constant :
    (6 : ℝ) / (297 / 16) > 32 / 100 := by norm_num

noncomputable def badOracle : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = j then (4 : ℂ) / 5 else 3/5

theorem printed_noisy_oracle_valid_amplitudes :
    (1/2 : ℝ) < 16/25 ∧ (16/25 : ℝ) < 1 ∧
      (4/5 : ℝ)^2 + (3/5 : ℝ)^2 = 1 := by norm_num

theorem printed_noisy_oracle_not_unitary : badOracle.conjTranspose * badOracle ≠ 1 := by
  intro h
  have z := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  norm_num [badOracle, Matrix.mul_apply, Fin.sum_univ_two, map_ofNat] at z

theorem printed_lower_bound_numerator_exceeds_single_query_information :
    queryInfo (3/4) < Real.log 2 / Real.log 2 - Real.log (4/3) / Real.log 2 := by
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1:ℝ)<2)).ne'
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  have h34 : Real.log ((3:ℝ)/4) = Real.log 3 - Real.log 4 :=
      Real.log_div (by norm_num) (by norm_num)
  have h14 : Real.log ((1:ℝ)/4) = -Real.log 4 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
  have h43 : Real.log ((4:ℝ)/3) = Real.log 4 - Real.log 3 :=
      Real.log_div (by norm_num) (by norm_num)
  unfold queryInfo binEntropy
  rw [show (1:ℝ)-3/4=1/4 by norm_num, h34,h14,h43,h4]
  field_simp
  nlinarith

open Qatlib
open scoped ENNReal NNReal

noncomputable def oneComparison (truth : Bool) : CostedLaw Bool :=
  (PMF.bernoulli (3 / 4 : ℝ≥0) (by exact_mod_cast (show (3:ℝ)/4 ≤ 1 by norm_num))).bind fun correct =>
    PMF.pure ((if correct then truth else !truth), 1)

theorem one_comparison_success (truth : Bool) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (oneComparison truth) (fun x => x.1 = truth) = (3 / 4 : ℝ≥0∞) := by
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event oneComparison
  rw [expectation_bernoulli_branches]
  cases truth <;> norm_num [ENNReal.coe_sub, NNReal.coe_le_coe]

theorem one_comparison_expected_queries (truth : Bool) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (oneComparison truth) = 1 := by
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost oneComparison
  rw [expectation_bernoulli_branches]
  have hq : (3/4 : ℝ≥0) ≤ 1 := by exact_mod_cast (show (3:ℝ)/4 ≤ 1 by norm_num)
  simpa only [Nat.cast_one, mul_one, ENNReal.coe_add, ENNReal.coe_one] using
    congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) (add_tsub_cancel_of_le hq)

noncomputable def printedBound (n : ℕ) (p τ : ℝ) : ℝ :=
  (Real.log n / Real.log 2 - Real.log (1 / (1 - τ)) / Real.log 2) / queryInfo p

theorem printed_lower_bound_exceeds_one : 1 < printedBound 2 (3/4) (1/4) := by
  have hpos : 0 < queryInfo (3/4) := by
    have z := zoo_bayes_queryInfo_quadratic_lower (p := 3/4) (by norm_num) (by norm_num)
    nlinarith
  unfold printedBound
  apply (lt_div_iff₀ hpos).2
  have hτ : (1 : ℝ) / (1 - 1/4) = 4/3 := by norm_num
  simpa only [Nat.cast_ofNat, one_mul, hτ] using
    printed_lower_bound_numerator_exceeds_single_query_information

noncomputable def rankTrueMass (a : Fin 3 → ℝ) (c : Fin 3) (p : ℝ) : ℝ :=
  ∑ j, a j * if c.val ≤ j.val then p else 1-p

theorem equality_cut_posterior_mismatch : rankTrueMass uniformPosterior 1 (3/4) = 7/12 ∧
    normTrue (uniformPosterior : Fin 3 → ℝ) 1 (3/4) = 5/12 ∧
    updateTrue (uniformPosterior : Fin 3 → ℝ) 1 (3/4) 1 = 1/5 ∧
    (uniformPosterior : Fin 3 → ℝ) 1 * (3/4) /
      rankTrueMass uniformPosterior 1 (3/4) = 3/7 := by
  norm_num [rankTrueMass, uniformPosterior, normTrue, normFalse, prefixMass,
    updateTrue, Fin.sum_univ_succ]

theorem classical_expected_lower_bound_counterexample (truth : Bool) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (oneComparison truth) (fun x => x.1 = truth) = (3/4 : ℝ≥0∞) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (oneComparison truth) = 1 ∧
    (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (oneComparison truth)).toReal < printedBound 2 (3/4) (1/4) := by
  refine ⟨one_comparison_success truth, one_comparison_expected_queries truth, ?_⟩
  rw [one_comparison_expected_queries truth, ENNReal.toReal_one]
  exact printed_lower_bound_exceeds_one

end Qatlib.Concepts.OrderedBayes.BayesRatioCore.ConsistencyChecks
