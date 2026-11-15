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

namespace Qatlib.Concepts.QuantumGibbs.SamplingCost

open Matrix

open scoped Matrix.Norms.L2Operator

def GibbsPreparationTimeLowerBound : Prop :=
  ∀ (A : ℕ) (β ε δ : ℝ) (p : List (HamiltonianQueryStep (Fin 2 × Fin A)))
      (ψ₀ : QState (Fin 2 × Fin A)),
    1 ≤ β → 0 < ε → ε ≤ 1 → 0 ≤ δ →
    HamiltonianQueryValid p → Normalized ψ₀ →
    Matrix.traceNorm
        (PartialTrace
            (pureDensity
              (HamiltonianQueryRun (twoLevelHamiltonianLift A (1 / β)) p ψ₀))
          - gibbsTwoLevel 1) ≤ δ →
    Matrix.traceNorm
        (PartialTrace
            (pureDensity
              (HamiltonianQueryRun (twoLevelHamiltonianLift A ((1 + ε) / β)) p ψ₀))
          - gibbsTwoLevel (1 + ε)) ≤ δ →
    Real.exp (-2) / 8 * ε - δ ≤ HamiltonianEvolutionTime p * (ε / β)

end Qatlib.Concepts.QuantumGibbs.SamplingCost
