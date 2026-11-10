/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.Discriminate.FiniteCopyHelstromDiscriminationStat
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.FreshCopyExec.QpeConsumers

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.CopyEvolution.Discriminate
open Matrix
open scoped ComplexOrder BigOperators

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
