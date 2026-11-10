/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.EstimatorLaws.TvStability.MontanaroScheduleDefs

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.EstimatorLaws.TvStability

def MontanaroChebyshevProductIdentitySubgoal : Prop :=
  ∀ (Ω : Type) [Fintype Ω] (H : Ω → ℕ) (β₁ β₂ : ℝ), 0 ≤ β₁ → β₁ ≤ β₂ →
    0 < partitionFn H β₁ → 0 < partitionFn H β₂ →
    (∑ x : Ω, Real.exp (-(β₁ * (H x : ℝ))) *
          Real.exp (-((β₂ - β₁) * (H x : ℝ))))
      / partitionFn H β₁ = partitionFn H β₂ / partitionFn H β₁ ∧
    (∑ x : Ω, Real.exp (-(β₁ * (H x : ℝ))) *
          (Real.exp (-((β₂ - β₁) * (H x : ℝ)))) ^ 2)
      / partitionFn H β₁ = partitionFn H (2 * β₂ - β₁) / partitionFn H β₁

end Qatlib.Concepts.EstimatorLaws.TvStability
