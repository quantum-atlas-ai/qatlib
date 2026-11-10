/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum
import Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma22Stat

open scoped BigOperators

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

lemma zoo_bayes_weighted_log_le (x ε : ℝ) (hx : 0 ≤ x) (hε : 0 < ε)
    (hxe : x ≤ ε) :
    x * (Real.log x / Real.log 2) ≤ x * (Real.log ε / Real.log 2) := by
  rcases eq_or_lt_of_le hx with hzero | hpos
  · simp [← hzero]
  · exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right ((Real.log_le_log_iff hpos hε).2 hxe)
        (le_of_lt (Real.log_pos (by norm_num)))) hx

theorem zoo_bayes_entropy_lower_bound :
    ∀ (n : ℕ) (a : Fin n → ℝ) (ε : ℝ),
    (∀ i, 0 ≤ a i) → (∑ i, a i) = 1 → 0 < ε → (∀ i, a i < ε) →
    Real.log (1 / ε) / Real.log 2 ≤ - ∑ i, a i * (Real.log (a i) / Real.log 2) := by
  intro n a ε ha hsum hε hcap
  have hbound : (∑ i, a i * (Real.log (a i) / Real.log 2)) ≤
      Real.log ε / Real.log 2 := by
    calc
      _ ≤ ∑ i, a i * (Real.log ε / Real.log 2) :=
        Finset.sum_le_sum fun i _ =>
          zoo_bayes_weighted_log_le (a i) ε (ha i) hε (hcap i).le
      _ = Real.log ε / Real.log 2 := by rw [← Finset.sum_mul, hsum, one_mul]
  simpa only [one_div, Real.log_inv, neg_div] using neg_le_neg hbound

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
