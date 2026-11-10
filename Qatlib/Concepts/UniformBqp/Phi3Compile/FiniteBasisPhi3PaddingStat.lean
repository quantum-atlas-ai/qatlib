/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.Phi3Compile.QtmPhi3Encoding
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CircuitImpl.Phi3Universal

open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.WalkFind.SearchAlgorithm

namespace Qatlib.Concepts.UniformBqp.Phi3Compile
open Matrix

def FiniteBasisPhi3Padding : Prop :=
  (∀ (I : Type) [Fintype I] (b : ℕ) (hb : Fintype.card I ≤ 2^b),
    Function.Injective (finiteBasisCode I b hb)) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I] (b : ℕ) (e : I → Reg b)
    (U : Matrix I I ℂ), Function.Injective e → U ∈ Matrix.unitaryGroup I ℂ →
    finiteBasisPadUnitary e U ∈ Matrix.unitaryGroup (Reg b) ℂ ∧
    (∀ ψ : QState I, Normalized ψ → Normalized (finiteBasisPadState e ψ)) ∧
    (∀ ψ : QState I,
      ApplyGate (finiteBasisPadUnitary e U) (finiteBasisPadState e ψ) =
        finiteBasisPadState e (ApplyGate U ψ)) ∧
    ∃ gs : List (Phi3Gate (b+3)),
      IsUnitaryCircuit (phi3Compile gs) ∧ QueryCount (phi3Compile gs) = 0 ∧
      GateCount (phi3Compile gs) = gs.length ∧ gs.length ≤ phi3PaddingBudget b ∧
      ∀ ψ : QState I,
        Run (1 : Matrix (Reg (b+3)) (Reg (b+3)) ℂ) (phi3Compile gs)
          (knownWireEmbed (knownPrefixWires b 3) (finiteBasisPadState e ψ)) =
          knownWireEmbed (knownPrefixWires b 3) (finiteBasisPadState e (ApplyGate U ψ)))

end Qatlib.Concepts.UniformBqp.Phi3Compile
