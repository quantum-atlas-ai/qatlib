/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.Achievability.CircuitWellFormed
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Replacing known gates in adjoint circuits

`replaceKnownInstruction` and `replaceKnownGates` transform known gate matrices while preserving
forward and backward oracle instructions. `KnownGateApproximation` requires each replacement
used by the circuit to be unitary and within a prescribed operator-norm error. This is the local
error model for circuit approximation in [NielsenChuang2010].

## Main statements

* `replaceKnownGates`: apply a matrix replacement to all known gates.
* `KnownGateApproximation`: record unitarity and an error bound for each used replacement.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false

open Qatlib.Concepts.CoherentSim.CoherentOAA

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline
open Matrix
open scoped Matrix.Norms.L2Operator

/-- Apply a matrix transformation to a known gate instruction while leaving forward and backward
oracle instructions unchanged. -/
def replaceKnownInstruction {H : Type*}
    (f : Matrix H H ℂ → Matrix H H ℂ) : AdjointStep H → AdjointStep H
  | .gate A => .gate (f A)
  | .forward => .forward
  | .backward => .backward

/-- Replace each known gate in an adjoint circuit by applying the given matrix transformation. -/
def replaceKnownGates {H : Type*} (f : Matrix H H ℂ → Matrix H H ℂ)
    (cs : List (AdjointStep H)) : List (AdjointStep H) := cs.map (replaceKnownInstruction f)

/-- The predicate that each known gate occurring in the circuit is replaced by a unitary matrix
within operator-norm error `η`. -/
def KnownGateApproximation {H : Type*} [Fintype H] [DecidableEq H]
    (cs : List (AdjointStep H)) (f : Matrix H H ℂ → Matrix H H ℂ) (η : ℝ) : Prop :=
  ∀ A, .gate A ∈ cs → f A ∈ Matrix.unitaryGroup H ℂ ∧ ‖f A - A‖ ≤ η

end Qatlib.Concepts.MatrixAccess.RitzPipeline
