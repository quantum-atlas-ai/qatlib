/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GateVocabulary.LocalReflectionGates
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.QueryWordCore.Circuit
open Matrix

namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.AndCoordinates

def bits (c e d : Bool) : Reg 3 := ![c,e,d]

end Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.AndCoordinates

namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.AndNetwork

def controlledCNOT : List (ReflectionGate 3) := toffoliLocalSteps 0 1 2

noncomputable def matrix (w : List (ReflectionGate 3)) : Matrix (Reg 3) (Reg 3) ℂ :=
  reflectionProgramMatrix w

theorem controlledCNOT_legal : reflectionLegal controlledCNOT :=
  (local_toffoli_fifteen_exact 3 0 1 2 (by decide) (by decide) (by decide)).2.1

theorem controlledCNOT_length : controlledCNOT.length = 15 := rfl

theorem controlledCNOT_basis (x : Reg 3) :
    Run 1 (reflectionCompile controlledCNOT) (Ket x) =
      Ket (Function.update x 2 (x 2 ^^ (x 0 && x 1))) :=
  (local_toffoli_fifteen_exact 3 0 1 2 (by decide) (by decide) (by decide)).2.2 x

end Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.AndNetwork

end
