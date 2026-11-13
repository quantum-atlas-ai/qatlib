/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.GeneralizedMarkovStat
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.FiniteStoppingTail
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Generalized Markov inequality for discrete laws

This module proves `generalizedMarkov_answer`, the generalized Markov estimate used in the
ordered search analysis of [BenOrHassidim2007]. A nonnegative random variable with mean at most
a and probability at least 1 - β of being at least b satisfies an upper-tail bound of (a - b +
βb) / (c - b) when 0 ≤ b ≤ a < c and 0 ≤ β ≤ 1.

## Main statements

* `generalizedMarkov_answer`: the probability of X > c satisfies the stated estimate for any
  probability mass function.

## References

* [Ben-Or and Hassidim, Lemma 2.8][BenOrHassidim2007]
-/

set_option autoImplicit false
namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore
open Qatlib
open scoped ENNReal

/-- Proves `GeneralizedMarkov`: a nonnegative discrete X with mean at most a and P(X ≥ b) ≥ 1 -
β satisfies P(X > c) ≤ (a - b + βb)/(c - b) when 0 ≤ β ≤ 1 and 0 ≤ b ≤ a < c [Ben-Or and
Hassidim, Lemma 2.8][BenOrHassidim2007]. -/
theorem generalizedMarkov_answer : GeneralizedMarkov := by
  intro α μ X a b β c _hX hmean hβ0 hβ1 hb0 hba hprob hac
  classical
  have hbc : b < c := hba.trans_lt hac
  have hd : 0 < c - b := sub_pos.mpr hbc
  let E := Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event μ (fun x => b ≤ X x)
  let F := Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event μ (fun x => c < X x)
  have hEfin : E ≠ ∞ :=
      ne_top_of_le_ne_top (by simp)
      (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_le_one μ _)
  have hFfin : F ≠ ∞ :=
      ne_top_of_le_ne_top (by simp)
      (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_le_one μ _)
  have hpoint (x : α) :
      ENNReal.ofReal b * (if b ≤ X x then 1 else 0) +
        ENNReal.ofReal (c - b) * (if c < X x then 1 else 0) ≤ ENNReal.ofReal (X x) := by
    by_cases hb : b ≤ X x <;> by_cases hc : c < X x
    · simp only [if_pos hb, if_pos hc, mul_one]
      rw [← ENNReal.ofReal_add hb0 hd.le]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    · simp only [if_pos hb, if_neg hc, mul_one, mul_zero, add_zero]
      exact ENNReal.ofReal_le_ofReal hb
    · exact False.elim (hb (hbc.le.trans hc.le))
    · simp [hb, hc]
  have hweighted : ENNReal.ofReal b * E + ENNReal.ofReal (c - b) * F ≤
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation μ (fun x => ENNReal.ofReal (X x)) := by
    dsimp only [E, F, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation]
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    apply ENNReal.tsum_le_tsum
    intro x
    calc
      ENNReal.ofReal b * (μ x * (if b ≤ X x then 1 else 0)) +
          ENNReal.ofReal (c - b) * (μ x * (if c < X x then 1 else 0)) =
          μ x * (ENNReal.ofReal b * (if b ≤ X x then 1 else 0) +
            ENNReal.ofReal (c - b) * (if c < X x then 1 else 0)) := by ring
      _ ≤ _ := mul_le_mul_right (hpoint x) _
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hweighted.trans hmean)
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEfin)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hFfin),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hb0,
    ENNReal.toReal_ofReal hd.le, ENNReal.toReal_ofReal (hb0.trans hba)] at hreal
  have hlower := ENNReal.toReal_mono hEfin hprob
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hβ1)] at hlower
  have hnum : 0 ≤ a - b + β * b := by nlinarith [mul_nonneg hβ0 hb0]
  apply (ENNReal.le_ofReal_iff_toReal_le hFfin (div_nonneg hnum hd.le)).mpr
  apply (le_div_iff₀ hd).mpr
  have hmass := mul_le_mul_of_nonneg_left hlower hb0
  nlinarith

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
