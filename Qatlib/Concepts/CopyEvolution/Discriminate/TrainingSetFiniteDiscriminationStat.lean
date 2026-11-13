/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.Discriminate.FiniteCopyHelstromDiscriminationStat

/-!
# Specification of training-set discrimination

This module defines `TrainingSetFiniteDiscrimination`, a proposition for two nonempty normalized
training families and their uniform density mixtures. Given a unitary spectral decomposition of
the mixture difference with a positive gap away from zero, the proposition bounds timed
two-species discrimination success below by the Helstrom value minus the sign-error budget.

The specification includes the density properties of both mixtures and the four resource counts
of the QPE procedure. It isolates the finite-copy training-set guarantee motivated by
[LloydMohseniRebentrost2014].

## Main statements

* `TrainingSetFiniteDiscrimination`: the training-mixture density, success, and resource
  specification.

## References

* [Lloyd, Mohseni, and Rebentrost, 2014][LloydMohseniRebentrost2014]
-/

open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.FreshCopyExec.QpeConsumers

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.CopyEvolution.Discriminate
open Matrix
open scoped ComplexOrder BigOperators

/-- The proposition asserting that two nonempty normalized training sets define density mixtures
whose finite-copy discrimination success is within the sign-error budget of the Helstrom
value, under a spectral gap. It also fixes the QPE resource tuple. -/
def TrainingSetFiniteDiscrimination : Prop :=
  ∀ (d m₁ m₂ M n : ℕ) (γ : ℝ) (φ : Fin m₁ → QState (Fin d))
    (ψ : Fin m₂ → QState (Fin d)) (V : Operator d) (x : Fin d → ℝ),
    0 < m₁ → 0 < m₂ → 2 ≤ M → 0 < n → 0 < γ → γ ≤ 1 →
    (∀ i, Normalized (φ i)) → (∀ i, Normalized (ψ i)) →
    V ∈ Matrix.unitaryGroup (Fin d) ℂ →
    pureStateMixture d m₁ φ-pureStateMixture d m₂ ψ =
      V * Matrix.diagonal (fun j => (x j : ℂ)) * Vᴴ →
    (∀ j, x j ≠ 0 → γ ≤ |x j|) →
    let ρ := pureStateMixture d m₁ φ
    let σ := pureStateMixture d m₂ ψ
    IsDensityOperator ρ ∧ IsDensityOperator σ ∧
    ((1/2 + Matrix.traceNorm (ρ-σ)/4) - twoSpeciesSignErrorBudget M n γ ≤
      (twoSpeciesTimedPositiveMass d M n ρ σ ρ + twoSpeciesTimedNegativeMass d M n ρ σ σ)/2) ∧
    twoSpeciesQPEResources M n = (2*(M-1)*n,2*(M-1)*n,2*(M-1)*n,0)

end Qatlib.Concepts.CopyEvolution.Discriminate
