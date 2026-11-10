/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.EstimatorLaws.TvStability.MontanaroScheduleDefs
open Qatlib.Concepts.EstimatorLaws.TvStability.Montanaro2015
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.EstimatorLaws.TvStability

def MontanaroChiSqOverlapSubgoal : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (ν π : FinDist X),
    (∀ x, 0 < π.prob x) → (∀ x, 0 < ν.prob x) →
    1 / Real.sqrt (chiSqDist ν π + 1)
      ≤ ∑ x, ν.prob x * Real.sqrt (π.prob x / ν.prob x)

end Qatlib.Concepts.EstimatorLaws.TvStability
