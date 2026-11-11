/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

/-!
# Classical Chebyshev contract

Packages the finite-distribution Chebyshev bound for an independent sample average as a
proposition. The contract is a classical concentration input for the estimator framework
surrounding [Montanaro2015].

## Main statements

* `ClassicalChebyshevSubgoal` requires the probability of absolute sample-mean error greater
  than `ε` to be at most `variance / (L * ε²)`.

## References

* [Montanaro, 2015][Montanaro2015]
-/

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

namespace Qatlib.Concepts.EstimatorLaws.TvStability

/-- The proposition asserting Chebyshev's inequality for the mean of `L` independent samples
from a finite law, with `L > 0` and `ε > 0`. -/
def ClassicalChebyshevSubgoal : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (p : FinDist X) (f : X → ℝ)
    (L : ℕ) (hL : 0 < L) (ε : ℝ) (hε : 0 < ε),
    p.probEvent (fun ω : Fin L → X => ε < |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg f ω - p.expect f|)
      ≤ p.variance f / (L * ε ^ 2)

end Qatlib.Concepts.EstimatorLaws.TvStability
