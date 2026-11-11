/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum
import Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma22Stat

/-!
# Entropy lower bound from a mass cap

This module proves the base-two entropy bound used in the ordered search analysis of
[BenOrHassidim2007]. A nonnegative normalized finite prior with all masses below ε has entropy
at least log₂(1/ε). The helper `zoo_bayes_weighted_log_le` compares each weighted logarithm with
the logarithm of the cap.

## Main statements

* `zoo_bayes_entropy_lower_bound`: the mass cap yields the stated entropy lower bound.

## References

* [Ben-Or and Hassidim, Lemma 2.2][BenOrHassidim2007]
-/

open scoped BigOperators

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

/-- For 0 ≤ x ≤ ε and ε > 0, the weighted logarithm x log₂ x is at most x log₂ ε. -/
lemma zoo_bayes_weighted_log_le (x ε : ℝ) (hx : 0 ≤ x) (hε : 0 < ε)
    (hxe : x ≤ ε) :
    x * (Real.log x / Real.log 2) ≤ x * (Real.log ε / Real.log 2) := by
  rcases eq_or_lt_of_le hx with hzero | hpos
  · simp [← hzero]
  · exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right ((Real.log_le_log_iff hpos hε).2 hxe)
        (le_of_lt (Real.log_pos (by norm_num)))) hx

/-- A nonnegative normalized finite prior with every weight below a positive ε has base-two
entropy at least log₂(1/ε) [Ben-Or and Hassidim, Lemma 2.2][BenOrHassidim2007]. -/
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
