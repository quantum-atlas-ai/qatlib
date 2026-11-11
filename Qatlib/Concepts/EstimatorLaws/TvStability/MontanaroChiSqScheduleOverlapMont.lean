/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EstimatorLaws.TvStability.MontanaroChiSqScheduleOverlapStat
import Qatlib.Concepts.EstimatorLaws.TvStability.MontanaroChiSqScheduleOverlapSubgoal

/-!
# Correctly normalized Gibbs overlap bound

Proves the corrected cooling-schedule overlap contract, including the partition-function factor
needed to normalize the chi-squared sum. The result connects a Chebyshev schedule inequality to
a lower bound on squared Gibbs overlap, as used in [Montanaro2015].

## Main statements

* `montanaro_normalized_gibbs_chi_sum` identifies the corrected expression with a sum over
  normalized Gibbs probabilities.
* `montanaroChiSqScheduleOverlapCorrectedSubgoal` proves the corrected identity and overlap
  lower bound.

## References

* [Montanaro, 2015][Montanaro2015]
-/

set_option autoImplicit false
open Qatlib.Concepts.EstimatorLaws.TvStability.Montanaro2015

namespace Qatlib.Concepts.EstimatorLaws.TvStability

open scoped Classical BigOperators

/-- Identifies the corrected Gibbs chi-squared sum with the sum of squared normalized
probabilities at `β₂` divided by normalized probabilities at `β₁`, assuming both partition
functions are positive. -/
theorem montanaro_normalized_gibbs_chi_sum (Ω : Type) [Fintype Ω] (H : Ω→ℕ) (β₁ β₂ : ℝ)
    (hZ₁ : 0<partitionFn H β₁) (hZ₂ : 0<partitionFn H β₂) :
    chiSqGibbsSumCorrected H β₁ β₂=
      ∑ x : Ω,(Real.exp (-(β₂*(H x:ℝ)))/partitionFn H β₂)^2/
        (Real.exp (-(β₁*(H x:ℝ)))/partitionFn H β₁) := by
  unfold chiSqGibbsSumCorrected chiSqGibbsSum
  rw [Finset.sum_div,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  field_simp [hZ₁.ne',hZ₂.ne',(Real.exp_pos (-(β₁*(H x:ℝ)))).ne']

/-- Proves the corrected cooling-schedule contract: the normalized chi-squared sum equals the
partition-function ratio, and the squared Gibbs overlap is at least `1 / B`. This is the
normalized overlap estimate used in [Montanaro2015]. -/
theorem montanaroChiSqScheduleOverlapCorrectedSubgoal : MontanaroChiSqScheduleOverlapCorrectedSubgoal := by
  intro Ω _ H β₁ β₂ B hβ hZ₁ hZ₂ hB hs
  constructor
  · rw [chiSqGibbsSumCorrected,montanaro_raw_gibbs_sum_identity Ω H β₁ β₂]
    ring
  · exact montanaro_schedule_overlap_bound Ω H β₁ β₂ B hβ hZ₁ hZ₂ hB hs
end Qatlib.Concepts.EstimatorLaws.TvStability
