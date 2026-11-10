/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EstimatorLaws.TvStability.ClassicalChebyshevSubgoalStat
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

namespace Qatlib.Concepts.EstimatorLaws.TvStability

open Qatlib

theorem classicalChebyshevSubgoal : ClassicalChebyshevSubgoal :=
  fun X _ _ p f L hL ε hε => Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.chebyshev_avg p f hL ε hε

end Qatlib.Concepts.EstimatorLaws.TvStability
