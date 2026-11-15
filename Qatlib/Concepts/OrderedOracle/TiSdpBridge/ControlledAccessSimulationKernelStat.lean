/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.OrderedOracle.TiSdpBridge.ControlledAccessRemoval
public import Qatlib.Foundations.QueryWordCore.Circuit
public import Qatlib.Foundations.PureStateMath.Qubit
public import Qatlib.Foundations.PureStateMath.Tensor

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.OrderedOracle.TiSdpBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Qatlib

def ControlledAccessSimulationKernel : Prop :=
  ∀ (I W : Type) [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    (i₀ : I) (f : I → Bool) (C : Circuit ((Bool × I) × W))
    (ψ : QState ((Bool × I) × W)),
    QueryCount (ospRemoveControlledCircuit C) = QueryCount C ∧
    (IsUnitaryCircuit C → IsUnitaryCircuit (ospRemoveControlledCircuit C)) ∧
    (Normalized ψ → Normalized (TensorState (Ket i₀) ψ)) ∧
    Run (ospPlainBusOracle f) (ospRemoveControlledCircuit C) (TensorState (Ket i₀) ψ)
      = ((if f i₀ then (-1 : ℂ) else 1) ^ QueryCount C) •
        TensorState (Ket i₀)
          (Run (ospControlledPhaseOracle (fun i => f i ^^ f i₀)) C ψ)

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
