/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.OrderedOracle.TiSdpBridge.ControlledAccessSimulationKernelStat
public import Qatlib.Foundations.QueryWordCore.Circuit
public import Qatlib.Foundations.PureStateMath.Qubit

@[expose] public section
open Qatlib.Concepts.OrderedOracle.TiSdpBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Qatlib

def Proposition10UncontrolledAccess : Prop :=
  ∀ (n : ℕ) [NeZero n] (W : Type) [Fintype W] [DecidableEq W]
    (ε : ℝ) (C : Circuit ((Bool × Fin (2*n)) × W))
    (ψ : QState ((Bool × Fin (2*n)) × W))
    (E : Fin n → Finset ((Bool × Fin (2*n)) × W)),
    0 ≤ ε → ε ≤ 1 → IsUnitaryCircuit C → Normalized ψ →
    (∀ j : Fin (2*n),
      1-ε ≤ MeasureProb (Run (ospControlledPhaseOracle (ospBit n j)) C ψ) (E (ospFun n j))) →
    IsUnitaryCircuit (ospRemoveControlledCircuit C) ∧
    Normalized (TensorState (Ket (0 : Fin (2*n))) ψ) ∧
    QueryCount (ospRemoveControlledCircuit C) = QueryCount C ∧
    ∀ j : Fin (2*n),
      1-ε ≤ MeasureProb
        (Run (ospPlainBusOracle (ospBit n j)) (ospRemoveControlledCircuit C)
          (TensorState (Ket (0 : Fin (2*n))) ψ))
        ((Finset.univ : Finset (Fin (2*n))) ×ˢ E (ospFun n j))

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
