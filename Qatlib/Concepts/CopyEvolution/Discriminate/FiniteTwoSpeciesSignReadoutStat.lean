/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.Discriminate.TimedTwoSpeciesSpectralReadoutStat
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.CopyEvolution.Discriminate
open Matrix
open scoped ComplexOrder BigOperators

def FiniteTwoSpeciesSignReadout : Prop :=
  ∀ (d M n : ℕ) (γ : ℝ) (ρ σ V : Operator d) (x : Fin d → ℝ),
    2 ≤ M → 0 < n → 0 < γ → γ ≤ 1 → IsDensityOperator ρ → IsDensityOperator σ →
    V ∈ Matrix.unitaryGroup (Fin d) ℂ →
    ρ-σ = V * Matrix.diagonal (fun j => (x j : ℂ)) * Vᴴ →
    (∀ j, |x j| ≤ 1) → (∀ j, x j ≠ 0 → γ ≤ |x j|) →
    (∀ χ : Operator d, IsDensityOperator χ →
      |twoSpeciesTimedPositiveMass d M n ρ σ χ -
        (∑ j ∈ Finset.univ.filter (fun j => 0 < x j), ((Vᴴ*χ*V) j j).re)|
        ≤ twoSpeciesSignErrorBudget M n γ) ∧
    (∀ j : Fin d, x j ≠ 0 →
      let χ := outerProduct (fun a => V a j)
      1-twoSpeciesSignErrorBudget M n γ ≤
        if 0 < x j then twoSpeciesTimedPositiveMass d M n ρ σ χ
        else twoSpeciesTimedNegativeMass d M n ρ σ χ) ∧
    (twoSpeciesSignErrorBudget M n γ ≤ 1/3 → ∀ j : Fin d, x j ≠ 0 →
      let χ := outerProduct (fun a => V a j)
      2/3 ≤ if 0 < x j then twoSpeciesTimedPositiveMass d M n ρ σ χ
        else twoSpeciesTimedNegativeMass d M n ρ σ χ)

end Qatlib.Concepts.CopyEvolution.Discriminate
