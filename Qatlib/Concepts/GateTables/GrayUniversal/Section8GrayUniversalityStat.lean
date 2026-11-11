/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownFrameLocalSynthesis
import Qatlib.Concepts.CircuitImpl.MultiControl.NoWorkTwoLevelSynthesis

/-!
# Gray-code universality specification

`Section8GrayUniversality` specifies exact implementation of every unitary on a nonempty qubit
register by a legal reflection-gate word on that register. Its quantitative bound multiplies the
two-level factor count by the uniform Gray two-level synthesis cost.

The specification records legality, zero queries, exact gate counts, and whole-state semantics,
following the unitary synthesis setting of [BarencoEtAl1995].

## Main statements

* `Section8GrayUniversality`: states the explicit bound `2^(n - 1) * (2^n + 1) * ((2 * n - 1) *
  (256 * n^2 + 2 * n - 2))`.

## References

* [Barenco et al., 1995][BarencoEtAl1995]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.GateTables.GrayUniversal

/-- The proposition that every unitary on `n ≥ 1` qubits has a legal reflection-word
implementation of length at most `2^(n - 1) * (2^n + 1) * ((2 * n - 1) * (256 * n^2 + 2 * n
- 2))`. The compiled circuit must have zero queries, one gate per word entry, and the
unitary's action on every state. -/
def Section8GrayUniversality : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ U : Matrix (Reg n) (Reg n) ℂ,
    U ∈ Matrix.unitaryGroup (Reg n) ℂ →
    ∃ gs : List (ReflectionGate n), reflectionLegal gs ∧
      gs.length ≤ 2 ^ (n - 1) * (2 ^ n + 1) * ((2 * n - 1) * (256 * n ^ 2 + 2 * n - 2)) ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      ∀ ψ : QState (Reg n),
        Run (1 : Matrix (Reg n) (Reg n) ℂ) (reflectionCompile gs) ψ =
          Matrix.mulVec U ψ

end Qatlib.Concepts.GateTables.GrayUniversal
