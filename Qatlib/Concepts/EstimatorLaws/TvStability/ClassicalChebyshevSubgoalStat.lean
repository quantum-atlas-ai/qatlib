/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

namespace Qatlib.Concepts.EstimatorLaws.TvStability

def ClassicalChebyshevSubgoal : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (p : FinDist X) (f : X → ℝ)
    (L : ℕ) (hL : 0 < L) (ε : ℝ) (hε : 0 < ε),
    p.probEvent (fun ω : Fin L → X => ε < |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg f ω - p.expect f|)
      ≤ p.variance f / (L * ε ^ 2)

end Qatlib.Concepts.EstimatorLaws.TvStability
