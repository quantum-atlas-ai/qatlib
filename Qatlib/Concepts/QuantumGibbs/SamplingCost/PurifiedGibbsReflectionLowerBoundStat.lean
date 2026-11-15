/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QuantumGibbs.SamplingCost.TwoLevelGibbsInstance

@[expose] public section
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.HamiltonianQuery

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.QuantumGibbs.SamplingCost

open Matrix

open scoped Matrix.Norms.L2Operator

def PurifiedGibbsReflectionLowerBound : Prop :=
  ∀ (β ε δ : ℝ) (p : List (HamiltonianQueryStep (Fin 2 × Fin 2))),
    1 ≤ β → 0 < ε → ε ≤ 1 → 0 ≤ δ →
    HamiltonianQueryValid p →
    (∀ ψ : QState (Fin 2 × Fin 2),
      ‖toEuclidean_fromVec
          (HamiltonianQueryRun (twoLevelHamiltonianLift 2 (1 / β)) p ψ
            - ApplyGate (purifiedGibbsReflection 1) ψ)‖
        ≤ δ * ‖toEuclidean_fromVec ψ‖) →
    (∀ ψ : QState (Fin 2 × Fin 2),
      ‖toEuclidean_fromVec
          (HamiltonianQueryRun (twoLevelHamiltonianLift 2 ((1 + ε) / β)) p ψ
            - ApplyGate (purifiedGibbsReflection (1 + ε)) ψ)‖
        ≤ δ * ‖toEuclidean_fromVec ψ‖) →
    ε / 8 - 2 * δ ≤ HamiltonianEvolutionTime p * (ε / β)

end Qatlib.Concepts.QuantumGibbs.SamplingCost
