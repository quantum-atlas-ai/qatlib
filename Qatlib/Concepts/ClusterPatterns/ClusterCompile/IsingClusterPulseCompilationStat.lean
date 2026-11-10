/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.IsingClusterResource
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.ClusterPatterns.ClusterCompile
open Qatlib

def IsingClusterPulseCompilation : Prop :=
  ∀ (n : ℕ) (edges : Finset (Fin n × Fin n)),
    (∀ e ∈ edges, e.1 < e.2) →
    sourcePulse edges = frameMatrix edges * czMatrix edges ∧
    sourcePulse edges ∈ Matrix.unitaryGroup (Reg n) ℂ ∧
    IsUnitaryCircuit (compiledPulseWord edges) ∧
    QueryCount (compiledPulseWord edges) = 0 ∧
    GateCount (compiledPulseWord edges) = edges.card + (frameVertices edges).card ∧
    ∀ ψ : QState (Reg n),
      Run (1 : Matrix (Reg n) (Reg n) ℂ) (compiledPulseWord edges) ψ
        = ApplyGate (sourcePulse edges) ψ

end Qatlib.Concepts.ClusterPatterns.ClusterCompile
