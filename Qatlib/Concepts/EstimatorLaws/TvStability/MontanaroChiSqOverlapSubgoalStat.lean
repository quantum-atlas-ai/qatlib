/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.EstimatorLaws.TvStability.MontanaroScheduleDefs

/-!
# Chi-squared overlap contract

Records the chi-squared-to-overlap inequality for finite probability laws with strictly positive
probabilities. This is the distributional estimate used to obtain adjacent Gibbs-state overlap
bounds in [Montanaro2015].

## Main statements

* `MontanaroChiSqOverlapSubgoal` requires a lower bound on `∑ x, ν(x) * sqrt (π(x) / ν(x))`.

## References

* [Montanaro, 2015][Montanaro2015]
-/

open Qatlib.Concepts.EstimatorLaws.TvStability.Montanaro2015
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.EstimatorLaws.TvStability

/-- The proposition requiring overlap to be at least `1 / sqrt (chiSqDist ν π + 1)` for strictly
positive finite laws `ν` and `π`. -/
def MontanaroChiSqOverlapSubgoal : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (ν π : FinDist X),
    (∀ x, 0 < π.prob x) → (∀ x, 0 < ν.prob x) →
    1 / Real.sqrt (chiSqDist ν π + 1)
      ≤ ∑ x, ν.prob x * Real.sqrt (π.prob x / ν.prob x)

end Qatlib.Concepts.EstimatorLaws.TvStability
