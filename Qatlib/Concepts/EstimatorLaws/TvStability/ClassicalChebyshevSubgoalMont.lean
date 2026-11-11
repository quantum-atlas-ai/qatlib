/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EstimatorLaws.TvStability.ClassicalChebyshevSubgoalStat
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

/-!
# Classical sample-mean Chebyshev bound

Discharges the classical Chebyshev contract by applying the existing finite-distribution
sample-mean theorem. This provides the classical concentration ingredient used alongside the
quantum mean-estimation methods of [Montanaro2015].

## Main statements

* `classicalChebyshevSubgoal` proves the variance-over-`L * ε²` bound for the deviation of an
  average of `L` independent samples.

## References

* [Montanaro, 2015][Montanaro2015]
-/

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

namespace Qatlib.Concepts.EstimatorLaws.TvStability

open Qatlib

/-- Proves the classical Chebyshev contract for a finite probability law by applying
`FinDist.chebyshev_avg` to a positive sample count and positive deviation threshold. -/
theorem classicalChebyshevSubgoal : ClassicalChebyshevSubgoal :=
  fun X _ _ p f L hL ε hε => Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.chebyshev_avg p f hL ε hε

end Qatlib.Concepts.EstimatorLaws.TvStability
