/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.VaRQuantile.StableQuantileFiniteRestrictedStat
import Qatlib.Concepts.RiskEstimation.VaRQuantile.VaRAlgorithmFiniteRestrictedQuan

/-!
# Failure events for separated quantiles

`risk_stable_wrong_index` shows that a wrong output index must violate the approximate quantile
bracket when the target index is separated from the target probability by the prescribed margin.
The argument uses monotonicity of `riskCDF` along sorted thresholds and supports the bisection
analysis in [WoernerEgger2019].

## Main statements

* `risk_stable_wrong_index`: include the wrong-index event in the approximate-bracket failure
  event.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018

open Matrix
open scoped Classical BigOperators ENNReal
set_option autoImplicit false

namespace Qatlib.Concepts.RiskEstimation.VaRQuantile

/-- On sorted thresholds with the stated CDF separation at `v` and all earlier indices, every
output index unequal to `v` is out of range or violates an approximate quantile-bracket
inequality. -/
theorem risk_stable_wrong_index {I : Type} [Fintype I] (A : Matrix I I ℂ) (j : I)
    (loss : I → ℚ) (xs : List ℚ) (q eps : ℝ) (v : ℕ) (hs : xs.SortedLE) (hv : v < xs.length)
    (habove : q+eps < riskCDF A j loss (xs.getD v 0))
    (hbelow : ∀ u : ℕ, u < v → riskCDF A j loss (xs.getD u 0) < q-eps)
    (z : ℕ × ℕ) (hz : z.1 ≠ v) :
    z.1 ≥ xs.length ∨ riskCDF A j loss (xs.getD z.1 0) < q-eps ∨
      (z.1 ≠ 0 ∧ q+eps < riskCDF A j loss (xs.getD (z.1-1) 0)) := by
  by_cases hlen : z.1 ≥ xs.length
  · exact Or.inl hlen
  · have hlen' : z.1 < xs.length := by omega
    rcases lt_or_gt_of_ne hz with hzlt | hzgt
    · exact Or.inr (Or.inl (hbelow _ hzlt))
    · refine Or.inr (Or.inr ⟨by omega, ?_⟩)
      exact habove.trans_le (riskCDF_indices A j loss xs hs v (z.1-1) hv (by omega) (by omega))
end Qatlib.Concepts.RiskEstimation.VaRQuantile
