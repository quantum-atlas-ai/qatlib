/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.IndependentWeightedEstimator
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

/-!
# Relative factor composition contract

States the probability bound for multiplying independently sampled factor estimates. The
proposition isolates the composition step in Theorem 8 of [Montanaro2015], with per-factor
relative tolerance `ε / (2 * ℓ)` and a total failure budget of one quarter.

## Main statements

* `MontanaroTheorem8CompositionSubgoal` requires product relative error at most `ε` except with
  probability at most `1 / 4`, assuming positive target means and the specified factor failure
  bounds.

## References

* [Montanaro, 2015][Montanaro2015]
-/

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.EstimatorLaws.TvStability

open Qatlib

/-- The proposition specifying the relative product guarantee used in Theorem 8 of
[Montanaro2015]. It assumes positive target means, matching expectations, and per-factor
failure at most `1 / (4 * ℓ)` at relative tolerance `ε / (2 * ℓ)`. -/
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
