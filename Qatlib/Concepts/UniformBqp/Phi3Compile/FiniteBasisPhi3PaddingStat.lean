/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.Phi3Compile.QtmPhi3Encoding

/-!
# Finite-basis Phi3 padding specification

`FiniteBasisPhi3Padding` collects injective encoding, unitary extension, and exact circuit
synthesis for a finite basis embedded into `b` qubits. The implementation acts on three extra
wires, preserves embedded evolution exactly, and carries an explicit word-length budget. The
background is described in [Yao1993].

## Main statements

* `FiniteBasisPhi3Padding`: the combined finite encoding and exact synthesis specification.

## References

* [Yao, 1993][Yao1993]
-/

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

/-- The combined assertion that finite bases encode injectively into sufficiently large Boolean
registers, unitary padding preserves normalization and embedded evolution, and the padded
action has an exact zero-query Phi3 implementation on `b + 3` wires within
`phi3PaddingBudget b`. -/
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
