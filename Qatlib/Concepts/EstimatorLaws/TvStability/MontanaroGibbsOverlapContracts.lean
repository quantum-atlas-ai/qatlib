/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.EstimatorLaws.TvStability.MontanaroChiSqOverlapSubgoalStat
import Qatlib.Concepts.EstimatorLaws.TvStability.MontanaroChebyshevProductIdentityStat

/-!
# Gibbs sums and overlap contracts

Defines the raw and correctly normalized Gibbs chi-squared sums and the normalized overlap
between Gibbs laws. It also records an original candidate schedule contract whose raw-sum
identity is refuted in the companion proof module; the corrected normalization supports the
cooling-schedule argument of [Montanaro2015].

## Main statements

* `chiSqGibbsSum` is the raw exponential ratio sum divided by the square of the final partition
  function.
* `gibbsOverlap` is the midpoint partition sum divided by the geometric mean of the endpoint
  partition functions.
* `chiSqGibbsSumCorrected` inserts the missing initial partition-function factor.

## References

* [Montanaro, 2015][Montanaro2015]
-/

open Qatlib.Concepts.EstimatorLaws.TvStability.Montanaro2015

namespace Qatlib.Concepts.EstimatorLaws.TvStability

/-- The raw Gibbs exponential ratio sum divided by `Z(β₂)²`; it does not include the initial
partition-function factor. -/
noncomputable def chiSqGibbsSum {Ω : Type} [Fintype Ω] (H : Ω → ℕ) (β₁ β₂ : ℝ) : ℝ :=
  (∑ x : Ω, (Real.exp (-(β₂ * (H x : ℝ)))) ^ 2 / Real.exp (-(β₁ * (H x : ℝ))))
    / partitionFn H β₂ ^ 2

/-- The overlap expression given by the partition sum at the midpoint temperature divided by
`sqrt (Z(β₁) * Z(β₂))`. -/
noncomputable def gibbsOverlap {Ω : Type} [Fintype Ω] (H : Ω → ℕ) (β₁ β₂ : ℝ) : ℝ :=
  (∑ x : Ω, Real.exp (-((β₁ + β₂) / 2 * (H x : ℝ))))
    / Real.sqrt (partitionFn H β₁ * partitionFn H β₂)

/-- The original candidate schedule contract, pairing a raw-sum identity with an overlap lower
bound. Its identity includes an extra initial partition-function factor, and the companion
module proves this proposition false. -/
def MontanaroChiSqScheduleOverlapSubgoal : Prop :=
  ∀ (Ω : Type) [Fintype Ω] (H : Ω → ℕ) (β₁ β₂ B : ℝ), β₁ ≤ β₂ →
    0 < partitionFn H β₁ → 0 < partitionFn H β₂ → 0 < B →
    partitionFn H β₁ * partitionFn H (2 * β₂ - β₁) ≤ B * partitionFn H β₂ ^ 2 →
    chiSqGibbsSum H β₁ β₂
      = partitionFn H β₁ * partitionFn H (2 * β₂ - β₁) / partitionFn H β₂ ^ 2 ∧
    1 / B ≤ gibbsOverlap H β₁ β₂ ^ 2

end Qatlib.Concepts.EstimatorLaws.TvStability

set_option autoImplicit false
namespace Qatlib.Concepts.EstimatorLaws.TvStability.Montanaro2015
noncomputable section

/-- The corrected Gibbs chi-squared sum, obtained by multiplying the raw sum by `Z(β₁)`. -/
def chiSqGibbsSumCorrected {Ω : Type} [Fintype Ω] (H : Ω→ℕ) (β₁ β₂ : ℝ) : ℝ :=
  partitionFn H β₁*chiSqGibbsSum H β₁ β₂
end
end Qatlib.Concepts.EstimatorLaws.TvStability.Montanaro2015
