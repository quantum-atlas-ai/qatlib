/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.GeneralizedMarkovQuan
import Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma23Quan
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Tail bounds from ordered-search cost estimates

Defines the mean, lower-threshold, and exceptional-probability expressions used in the tail
estimate of [BenOrHassidim2007]. `source_lemma2_9_tail` applies a generalized Markov bound to a
nonnegative query cost with the stated expectation and lower-tail hypotheses.

## Main statements

* `source_lemma2_9_tail`: bounds the probability of exceeding the corrected mean threshold by `1
  / χ`.

## References

* [Ben-Or and Hassidim, 2007][BenOrHassidim2007]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.OrderedBayes.BayesRatioCore
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma23Quan
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open scoped ENNReal

namespace Qatlib.Papers.OrderedList07.MainResults

/-- For `L ≥ 4`, twice the base-two logarithm of `L` is at most `L`. -/
lemma two_mul_logb_two_le (L : ℝ) (hL : 4 ≤ L) :
    2 * (Real.log L / Real.log 2) ≤ L := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLpos : 0 < L := by linarith
  rw [show 2 * (Real.log L / Real.log 2) = (2 * Real.log L) / Real.log 2 by ring]
  rw [div_le_iff₀ h2]
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have ht : 0 < L / 4 := by positivity
  have hsplit : Real.log L = Real.log 4 + Real.log (L / 4) := by
    nth_rewrite 1 [show L = 4 * (L / 4) by field_simp]
    rw [Real.log_mul (by norm_num) ht.ne']
  have hlog : Real.log (L / 4) ≤ L / 4 - 1 := Real.log_le_sub_one_of_pos ht
  have h14 : (1 : ℝ) ≤ L / 4 := by linarith
  have hlt : (1 : ℝ) / 2 < Real.log 2 := by
    have h := Real.log_two_gt_d9
    linarith
  have hp : 0 ≤ (L - 4) * (Real.log 2 - 1 / 2) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [hsplit, hlog, h4, h2, hlt, hL, hp]

/-- The mean-cost expression `log₂ n / queryInfo p` with the prescribed logarithmic error
correction. -/
noncomputable def tailMean (n : ℕ) (p c₁ δ : ℝ) : ℝ :=
  Real.log n / Real.log 2 / queryInfo p
    + c₁ * (Real.log (Real.log n / Real.log 2) / Real.log 2)
        * (Real.log (1 / δ) / Real.log 2) / queryInfo p

/-- The lower-cost threshold obtained by subtracting `2 * log₂ (log₂ n) / queryInfo p` from the
leading cost. -/
noncomputable def tailLower (n : ℕ) (p : ℝ) : ℝ :=
  Real.log n / Real.log 2 / queryInfo p
    - 2 * (Real.log (Real.log n / Real.log 2) / Real.log 2) / queryInfo p

/-- The exceptional-probability parameter `2 / log₂ n`. -/
noncomputable def tailBeta (n : ℕ) : ℝ := 2 / (Real.log n / Real.log 2)

/-- Under the stated parameter, mean-cost, and lower-tail hypotheses, the probability that `Q`
exceeds `tailMean + χ * (tailMean − tailLower + tailBeta * tailLower)` is at most `1 / χ`
[BenOrHassidim2007]. -/
theorem source_lemma2_9_tail
    {α : Type} (μ : PMF α) (Q : α → ℝ)
    (n : ℕ) (hn : 16 ≤ n) (p δ c₁ χ : ℝ)
    (hp : 1 / 2 < p) (hp1 : p < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hc₁ : 0 < c₁) (hχ : 1 < χ)
    (hQ : ∀ x, 0 ≤ Q x)
    (hmean : CostedLaw.expectation μ (fun x => ENNReal.ofReal (Q x))
      ≤ ENNReal.ofReal (tailMean n p c₁ δ))
    (hprob : ENNReal.ofReal (1 - tailBeta n)
      ≤ CostedLaw.event μ (fun x => tailLower n p ≤ Q x)) :
    CostedLaw.event μ
        (fun x => tailMean n p c₁ δ
          + χ * (tailMean n p c₁ δ - tailLower n p + tailBeta n * tailLower n p) < Q x)
      ≤ ENNReal.ofReal (1 / χ) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnR : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    push_cast
    ring
  have hlogmono : Real.log (16 : ℝ) ≤ Real.log n := Real.log_le_log (by norm_num) hnR
  have hL4 : 4 ≤ Real.log n / Real.log 2 := by
    rw [le_div_iff₀ h2]
    rw [hlog16] at hlogmono
    linarith
  have hL0 : 0 < Real.log n / Real.log 2 := by linarith
  have hlgLpos : 0 < Real.log (Real.log n / Real.log 2) / Real.log 2 :=
    div_pos (Real.log_pos (by linarith : 1 < Real.log n / Real.log 2)) h2
  have hlgL : 0 ≤ Real.log (Real.log n / Real.log 2) / Real.log 2 := hlgLpos.le
  have hI : 0 < queryInfo p := by
    have hi := zoo_bayes_queryInfo_quadratic_lower hp hp1
    nlinarith [sq_nonneg (p - 1 / 2)]
  have hδpos : 0 < 1 / δ := by positivity
  have hlogδ : 0 < Real.log (1 / δ) := by
    have hneg : Real.log δ < 0 := Real.log_neg hδ0 hδ1
    rw [Real.log_div (by norm_num) hδ0.ne', Real.log_one]
    linarith
  have hβ0 : 0 ≤ tailBeta n := by
    rw [tailBeta]
    exact div_nonneg (by norm_num) hL0.le
  have hβ1 : tailBeta n ≤ 1 := by
    rw [tailBeta, div_le_one hL0]
    linarith
  have hb0 : 0 ≤ tailLower n p := by
    have heq : tailLower n p
        = (Real.log n / Real.log 2
            - 2 * (Real.log (Real.log n / Real.log 2) / Real.log 2)) / queryInfo p := by
      rw [tailLower]
      ring
    rw [heq]
    exact div_nonneg (by linarith [two_mul_logb_two_le (Real.log n / Real.log 2) hL4]) hI.le
  have hgap : tailMean n p c₁ δ - tailLower n p
      = (c₁ * (Real.log (Real.log n / Real.log 2) / Real.log 2)
            * (Real.log (1 / δ) / Real.log 2)
          + 2 * (Real.log (Real.log n / Real.log 2) / Real.log 2)) / queryInfo p := by
    rw [tailMean, tailLower]
    ring
  have hc₁lg : 0 < c₁ * (Real.log (Real.log n / Real.log 2) / Real.log 2) :=
    mul_pos hc₁ hlgLpos
  have hgap_pos : 0 < tailMean n p c₁ δ - tailLower n p := by
    rw [hgap]
    apply div_pos _ hI
    have hB : 0 < Real.log (1 / δ) / Real.log 2 := div_pos hlogδ h2
    have hA : 0 < c₁ * (Real.log (Real.log n / Real.log 2) / Real.log 2)
        * (Real.log (1 / δ) / Real.log 2) := mul_pos hc₁lg hB
    linarith [hA, hlgL]
  have hba : tailLower n p ≤ tailMean n p c₁ δ := le_of_lt (sub_pos.mp hgap_pos)
  have hz : 0 < tailMean n p c₁ δ - tailLower n p + tailBeta n * tailLower n p := by
    have hb : 0 ≤ tailBeta n * tailLower n p := mul_nonneg hβ0 hb0
    linarith
  have hac : tailMean n p c₁ δ
      < tailMean n p c₁ δ
        + χ * (tailMean n p c₁ δ - tailLower n p + tailBeta n * tailLower n p) := by
    have : 0 < χ * (tailMean n p c₁ δ - tailLower n p + tailBeta n * tailLower n p) :=
      mul_pos (by linarith) hz
    linarith
  have hχz : 0 < χ * (tailMean n p c₁ δ - tailLower n p + tailBeta n * tailLower n p) :=
    mul_pos (by linarith) hz
  have hshift : (tailMean n p c₁ δ
        + χ * (tailMean n p c₁ δ - tailLower n p + tailBeta n * tailLower n p)) - tailLower n p
      = (tailMean n p c₁ δ - tailLower n p)
        + χ * (tailMean n p c₁ δ - tailLower n p + tailBeta n * tailLower n p) := by
    ring
  have hge : χ * (tailMean n p c₁ δ - tailLower n p + tailBeta n * tailLower n p)
      ≤ (tailMean n p c₁ δ
          + χ * (tailMean n p c₁ δ - tailLower n p + tailBeta n * tailLower n p)) - tailLower n p := by
    rw [hshift]
    linarith
  have hratio : (tailMean n p c₁ δ - tailLower n p + tailBeta n * tailLower n p)
      / ((tailMean n p c₁ δ
          + χ * (tailMean n p c₁ δ - tailLower n p + tailBeta n * tailLower n p)) - tailLower n p)
      ≤ 1 / χ := by
    have h1 := div_le_div_of_nonneg_left hz.le hχz hge
    have h2' : (tailMean n p c₁ δ - tailLower n p + tailBeta n * tailLower n p)
        / (χ * (tailMean n p c₁ δ - tailLower n p + tailBeta n * tailLower n p))
        = 1 / χ := by
      field_simp
    linarith [h1, h2'.le, h2'.ge]
  have hmain := generalizedMarkov_answer α μ Q (tailMean n p c₁ δ) (tailLower n p)
    (tailBeta n)
    (tailMean n p c₁ δ
      + χ * (tailMean n p c₁ δ - tailLower n p + tailBeta n * tailLower n p))
    hQ hmean hβ0 hβ1 hb0 hba hprob hac
  exact hmain.trans (ENNReal.ofReal_le_ofReal hratio)

end Qatlib.Papers.OrderedList07.MainResults
