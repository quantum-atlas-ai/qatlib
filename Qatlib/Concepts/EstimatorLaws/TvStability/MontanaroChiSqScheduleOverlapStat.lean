/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EstimatorLaws.TvStability.MontanaroGibbsOverlapContracts

/-!
# Corrected Gibbs schedule overlap contract

States the cooling-schedule overlap property using the corrected, normalized Gibbs chi-squared
sum. The proposition specifies the normalization and squared-overlap conclusion needed in the
partition-function algorithm of [Montanaro2015].

## Main statements

* `MontanaroChiSqScheduleOverlapCorrectedSubgoal` combines the corrected partition-function
  identity with `1 / B ≤ gibbsOverlap²` under the schedule inequality.

## References

* [Montanaro, 2015][Montanaro2015]
-/

open Qatlib.Concepts.EstimatorLaws.TvStability.Montanaro2015

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.EstimatorLaws.TvStability

/-- The proposition requiring the corrected Gibbs chi-squared identity and squared-overlap lower
bound `1 / B`, assuming ordered temperatures, positive partition functions, positive `B`,
and the Chebyshev schedule inequality. -/
def MontanaroChiSqScheduleOverlapCorrectedSubgoal : Prop :=
  ∀ (Ω : Type) [Fintype Ω] (H : Ω→ℕ) (β₁ β₂ B : ℝ),β₁≤β₂→
    0<partitionFn H β₁→0<partitionFn H β₂→0<B→
    partitionFn H β₁*partitionFn H (2*β₂-β₁)≤B*partitionFn H β₂^2→
    chiSqGibbsSumCorrected H β₁ β₂=partitionFn H β₁*partitionFn H (2*β₂-β₁)/partitionFn H β₂^2 ∧
      1/B≤gibbsOverlap H β₁ β₂^2
end Qatlib.Concepts.EstimatorLaws.TvStability
