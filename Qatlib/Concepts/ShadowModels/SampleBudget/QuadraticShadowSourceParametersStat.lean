/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ShadowVariance.PauliQuadraticVarianceSharpSubgoalStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.ShadowModels.ShadowVariance

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.ShadowModels.SampleBudget

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

def QuadraticShadowSourceParametersSubgoal : Prop :=
  ∀ (n D q : ℕ) (ww : Fin D → Fin q → pauliPairWord n) (c : Fin D → Fin q → ℚ)
    (S₁ S₂ : Fin D → Finset (Fin n)) (ρ : Operator (2^n)) (hρ : IsDensityOperator ρ)
    (ε δ : ℝ),
    (∀ z, pauliPairSupported (S₁ z) (S₂ z) (ww z) (c z)) →
    (∀ z, 1 ≤ ‖pauliPairObservable n q (ww z) (c z)‖) →
    0 < ε → ε ≤ 1 → 0 < δ → δ ≤ 1 → 0 < D →
    let B := (Finset.univ : Finset (Fin D)).fold max 0
      (fun z => (4 : ℝ)^(max (S₁ z).card (S₂ z).card) *
        ‖pauliPairObservable n q (ww z) (c z)‖^2)
    let m := Nat.ceil (140 * B / ε^2)
    let r := Nat.log 4 (8 * D * Nat.ceil (1 / δ)) + 1
    (∑ ω ∈ Finset.univ.filter (fun ω : Fin (2*r+1) → Fin m → Fin n → Fin 3 × Bool =>
      ∃ z, ε < |quadraticShadowMedian n m r (pauliPairObservable n q (ww z) (c z)) ω -
        (Matrix.trace (pauliPairObservable n q (ww z) (c z) * TensorGate ρ ρ)).re|),
      ∏ b, (tensorPauliLaw n ρ hρ).probOf (ω b)) ≤ δ

end Qatlib.Concepts.ShadowModels.SampleBudget
