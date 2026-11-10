/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.Achievability.CircuitWellFormed
import Mathlib.Analysis.CStarAlgebra.Matrix
set_option warningAsError false

open Qatlib.Concepts.CoherentSim.CoherentOAA

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline
open Matrix
open scoped Matrix.Norms.L2Operator

def replaceKnownInstruction {H : Type*}
    (f : Matrix H H ℂ → Matrix H H ℂ) : AdjointStep H → AdjointStep H
  | .gate A => .gate (f A)
  | .forward => .forward
  | .backward => .backward

def replaceKnownGates {H : Type*} (f : Matrix H H ℂ → Matrix H H ℂ)
    (cs : List (AdjointStep H)) : List (AdjointStep H) := cs.map (replaceKnownInstruction f)

def KnownGateApproximation {H : Type*} [Fintype H] [DecidableEq H]
    (cs : List (AdjointStep H)) (f : Matrix H H ℂ → Matrix H H ℂ) (η : ℝ) : Prop :=
  ∀ A, .gate A ∈ cs → f A ∈ Matrix.unitaryGroup H ℂ ∧ ‖f A - A‖ ≤ η

end Qatlib.Concepts.MatrixAccess.RitzPipeline
