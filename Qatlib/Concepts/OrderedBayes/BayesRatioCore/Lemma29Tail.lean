/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
import Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma23Quan
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Obstruction to the specified query tail contract

This module proves `lemma2_9Tail_obstruction`, refuting `Lemma2_9TailContract`, a formal
tail-bound contract associated with [BenOrHassidim2007]. A deterministic query-count random
variable at n = 4, p = 3/4, δ = 1/256, c₁ = 1, and χ = 2 satisfies its mean and lower-tail
hypotheses but violates its proposed upper-tail conclusion.

## Main statements

* `lemma2_9Tail_obstruction`: the specified tail contract is false.

## References

* [Ben-Or and Hassidim, Lemma 2.9][BenOrHassidim2007]
-/

set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma23Quan

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore
open Qatlib

/-- The formal tail proposition `Lemma2_9TailContract` associated with [Ben-Or and Hassidim,
Lemma 2.9][BenOrHassidim2007] is false, as witnessed by a deterministic nonnegative random
variable satisfying its mean and lower-tail hypotheses. -/
theorem lemma2_9Tail_obstruction : ¬ Lemma2_9TailContract := by
  intro h
  have hl2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hL : Real.log (4 : ℝ) / Real.log 2 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    field_simp
    norm_num
  have hD : Real.log (1 / (1 / 256 : ℝ)) / Real.log 2 = 8 := by
    rw [show (1 / (1 / 256 : ℝ)) = 2 ^ 8 by norm_num, Real.log_pow]
    field_simp
    norm_num
  have hD256 : Real.log (256 : ℝ) / Real.log 2 = 8 := by simpa using hD
  have hI : 0 < queryInfo (3 / 4) := by
    have hi := zoo_bayes_queryInfo_quadratic_lower (by norm_num : (1 / 2 : ℝ) < 3 / 4)
      (by norm_num : (3 / 4 : ℝ) < 1)
    norm_num at hi
    linarith
  let Q : Unit → ℝ := fun _ => 10 / queryInfo (3 / 4)
  have hQ : ∀ x, 0 ≤ Q x := by intro x; exact (div_pos (by norm_num) hI).le
  have hmean : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (PMF.pure ()) (fun x => ENNReal.ofReal (Q x)) ≤
      ENNReal.ofReal (2 / queryInfo (3 / 4) + 8 / queryInfo (3 / 4)) := by
    norm_num [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation, PMF.pure_apply, Q, ← add_div]
  have hbelow : ENNReal.ofReal (1 - 2 / (2 : ℝ)) ≤
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (PMF.pure ()) (fun x => 2 / queryInfo (3 / 4) - 2 / queryInfo (3 / 4) ≤ Q x) := by
    norm_num
  have ht := h 4 (3 / 4) (1 / 256) 1 2 Unit (PMF.pure ()) Q
    (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hI
  norm_num only [Nat.cast_ofNat] at ht
  simp only [hL, hD256, div_self hl2, one_mul, mul_one] at ht
  have ht' := ht hQ hmean hbelow
  have hupper : 2 / queryInfo (3 / 4) + 2 * (1 + 2) / queryInfo (3 / 4) < 10 / queryInfo (3 / 4) := by
    rw [← add_div]
    exact (div_lt_div_iff_of_pos_right hI).mpr (by norm_num)
  norm_num at hupper
  norm_num [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event, PMF.pure_apply, Q, hupper] at ht'

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
