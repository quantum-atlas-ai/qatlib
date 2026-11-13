/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GateVocabulary.LocalReflectionGates

/-!
# A native three-bit controlled conjunction

`controlledCNOT` is a fifteen-step reflection-gate implementation of the three-bit Toffoli
operation. Its basis action toggles the third bit by the conjunction of the first two, with a
proof that every step is legal. The controlled-gate interpretation follows [NielsenChuang2010].

## Main statements

* `controlledCNOT_length`: the implementation has exactly fifteen steps.
* `controlledCNOT_basis`: the target bit is toggled by the conjunction of the two control bits.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.QueryWordCore.Circuit
open Matrix

namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.AndCoordinates

/-- Construct the three-bit register with entries `c`, `e`, and `d` in that order. -/
def bits (c e d : Bool) : Reg 3 := ![c,e,d]

end Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.AndCoordinates

namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.AndNetwork

/-- The local Toffoli reflection program with controls zero and one and target two. -/
def controlledCNOT : List (ReflectionGate 3) := toffoliLocalSteps 0 1 2

/-- The matrix represented by a three-bit reflection-gate program. -/
noncomputable def matrix (w : List (ReflectionGate 3)) : Matrix (Reg 3) (Reg 3) ℂ :=
  reflectionProgramMatrix w

/-- Every step of the controlled CNOT reflection program is legal. -/
theorem controlledCNOT_legal : reflectionLegal controlledCNOT :=
  (local_toffoli_fifteen_exact 3 0 1 2 (by decide) (by decide) (by decide)).2.1

/-- The controlled CNOT reflection program has exactly fifteen steps. -/
theorem controlledCNOT_length : controlledCNOT.length = 15 := rfl

/-- On a basis state, the compiled program replaces bit two by its XOR with the conjunction of
bits zero and one. -/
theorem controlledCNOT_basis (x : Reg 3) :
    Run 1 (reflectionCompile controlledCNOT) (Ket x) =
      Ket (Function.update x 2 (x 2 ^^ (x 0 && x 1))) :=
  (local_toffoli_fifteen_exact 3 0 1 2 (by decide) (by decide) (by decide)).2.2 x

end Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.AndNetwork

end
