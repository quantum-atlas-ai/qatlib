/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.Phi3Universal.Phi3Defs
import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownFrameLocalSynthesis
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MatrixAccess.KnownFrameSynth

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.CircuitImpl.Phi3Universal

open Matrix

def Phi3UniversalityTheorem1 : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    ∀ (U : Matrix (Reg n) (Reg n) ℂ), U ∈ Matrix.unitaryGroup (Reg n) ℂ →
      ∃ gs : List (Phi3Gate (n + 3)),
        IsUnitaryCircuit (phi3Compile gs) ∧
        QueryCount (phi3Compile gs) = 0 ∧
        GateCount (phi3Compile gs) = gs.length ∧
        gs.length ≤ 768 * (n + 1) ^ 3 * 4 ^ n ∧
        ∀ ψ : QState (Reg n),
          Run (1 : Matrix (Reg (n + 3)) (Reg (n + 3)) ℂ) (phi3Compile gs)
            (knownWireEmbed (knownPrefixWires n 3) ψ) =
            knownWireEmbed (knownPrefixWires n 3) (U *ᵥ ψ)

end Qatlib.Concepts.CircuitImpl.Phi3Universal
