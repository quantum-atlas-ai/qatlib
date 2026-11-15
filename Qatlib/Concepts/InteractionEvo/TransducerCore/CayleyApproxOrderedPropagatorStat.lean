/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.InteractionEvo.CayleyTransform
public import Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
public import Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding
public import Qatlib.Concepts.BlockEncoding.EncodingCore.CoordinateFiber
public import Qatlib.Concepts.InteractionEvo.TransducerCore.CayleyTransducerDefs

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.InteractionEvo.CayleyTransform Qatlib.Concepts.BlockEncoding.EncodingCore Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

set_option autoImplicit false

open Qatlib.Concepts.Execution.WorkspaceCP

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.InteractionEvo.TransducerCore

open Matrix
open scoped Matrix.Norms.L2Operator

variable {ιS ιA : Type} [Fintype ιS] [DecidableEq ιS] [Fintype ιA] [DecidableEq ιA]

def CayleyTransducerApproximatesOrderedPropagator : Prop :=
  ∀ (ιS ιA : Type) [Fintype ιS] [DecidableEq ιS] [Fintype ιA] [DecidableEq ιA]
    (a0 : ιA) (T α β : ℝ) (H : ℝ → Matrix ιS ιS ℂ) (J : ℕ),
    0 < T → 0 < α → 0 ≤ β → Continuous H →
    (∀ t ∈ Set.Icc 0 T, (H t).IsHermitian) →
    (∀ t ∈ Set.Icc 0 T, ‖H t‖ ≤ α) →
    (∀ s ∈ Set.Icc 0 T, ∀ t ∈ Set.Icc 0 T, ‖H t - H s‖ ≤ β * |t - s|) →
    0 < J → α * T / J ≤ 1 →
    ∃ (Sc : Matrix (ιS ⊕ ((ιA × ιS) × Fin J)) (ιS ⊕ ((ιA × ιS) × Fin J)) ℂ),
      Sc ∈ Matrix.unitaryGroup _ ℂ ∧
      (∀ oracle : HamTOracle a0 H T α J,
        ∃ Γ : Matrix ((ιA × ιS) × Fin J) ιS ℂ,
          ‖Γ‖ ^ 2 ≤ α * T ∧
          ∀ ψ0 : ιS → ℂ,
            (Sc * oracleDirectSum oracle.O) *ᵥ Sum.elim ψ0 (Γ *ᵥ ψ0) =
              Sum.elim (cayleyProduct H α T J *ᵥ ψ0) (Γ *ᵥ ψ0)) ∧
      ‖cayleyProduct H α T J - orderedEvolution (fun t => Complex.I • H t) 0 T‖ ≤
        β * T ^ 2 / (2 * (J : ℝ)) + (α * T) ^ 3 / (12 * (J : ℝ) ^ 2)

end Qatlib.Concepts.InteractionEvo.TransducerCore
