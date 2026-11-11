/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.EstimatorLaws.TvStability.MontanaroScheduleDefs

/-!
# Gibbs ratio moment contract

States the moment identities for the exponential observable linking two Gibbs temperatures. This
proposition isolates the partition-function algebra used by the cooling-schedule estimator in
[Montanaro2015].

## Main statements

* `MontanaroChebyshevProductIdentitySubgoal` requires weighted first and second moments to equal
  the corresponding partition-function ratios.

## References

* [Montanaro, 2015][Montanaro2015]
-/

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.EstimatorLaws.TvStability

/-- The proposition specifying the Gibbs ratio observable's first moment `Z(β₂) / Z(β₁)` and
second moment `Z(2 * β₂ - β₁) / Z(β₁)`, under ordered nonnegative temperatures and positive
partition functions. -/
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
