/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownFrameLocalSynthesis
import Qatlib.Concepts.CircuitImpl.MultiControl.NoWorkTwoLevelSynthesis

/-!
# Gray two-level synthesis specification

`Section8GrayTwoLevel` states a uniform exact synthesis bound for legal two-level instructions
on a nonempty qubit register. The specification records legality, zero query count, gate count
equal to word length, and agreement on every input state.

This packages a quantitative version of the two-level construction used in elementary quantum
gate synthesis [BarencoEtAl1995].

## Main statements

* `Section8GrayTwoLevel`: specifies the bound `(2 * n - 1) * (256 * n^2 + 2 * n - 2)` on the
  original register.

## References

* [Barenco et al., 1995][BarencoEtAl1995]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.CircuitImpl.MultiControl
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.GateTables.GrayUniversal

/-- The proposition that every legal two-level instruction on `n ≥ 1` qubits has a legal
reflection word of length at most `(2 * n - 1) * (256 * n^2 + 2 * n - 2)`, with zero queries
and gate count equal to word length. The compiled word must act as the instruction matrix on
every state. -/
def Section8GrayTwoLevel : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ g : TwoLevelInstruction (Reg n), twoLevelLegal g →
    ∃ gs : List (ReflectionGate n), reflectionLegal gs ∧
      gs.length ≤ (2 * n - 1) * (256 * n ^ 2 + 2 * n - 2) ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      ∀ ψ : QState (Reg n),
        Run (1 : Matrix (Reg n) (Reg n) ℂ) (reflectionCompile gs) ψ =
          Matrix.mulVec (twoLevelMatrix g) ψ

end Qatlib.Concepts.GateTables.GrayUniversal
