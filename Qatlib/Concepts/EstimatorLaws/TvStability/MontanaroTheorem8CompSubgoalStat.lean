/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.IndependentWeightedEstimator
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.EstimatorLaws.TvStability

open Qatlib

def MontanaroTheorem8CompositionSubgoal : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (ℓ : ℕ) (ps : Fin ℓ → FinDist X)
    (obs : Fin ℓ → X → ℝ) (means : Fin ℓ → ℝ), 0 < ℓ → ∀ ε : ℝ, 0 < ε → ε < 1 →
    (∀ i, (ps i).expect (obs i) = means i) →
    (∀ i, 0 < means i) →
    (∀ i, (ps i).probEvent (fun ω : Fin 1 → X =>
        (ε / (2 * ℓ)) * means i < |obs i (ω 0) - means i|) ≤ 1 / (4 * ℓ)) →
    (independentSampleLaw ps).probEvent
        (fun ω : Fin 1 → Fin ℓ → X =>
          ε * ∏ i, means i < |∏ i, obs i (ω 0 i) - ∏ i, means i|)
      ≤ 1 / 4

end Qatlib.Concepts.EstimatorLaws.TvStability
