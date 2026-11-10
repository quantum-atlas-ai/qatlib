/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.List.Basic

namespace Qatlib.Papers.UniversalWalk08.MainResults.CircuitDefs

open Matrix

set_option autoImplicit false

variable {n : ℕ}

structure GateCircuit (n : ℕ) where

  gates : List (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)

  gates_unitary : ∀ g ∈ gates, g ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ

noncomputable def circuitEval (C : GateCircuit n) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  C.gates.prod

def circuitGateCount (C : GateCircuit n) : ℕ :=
  C.gates.length

@[simp]
theorem circuitEval_empty :
    circuitEval (⟨[], by simp⟩ : GateCircuit n) = 1 := by
  simp [circuitEval]

def circuitAppend (C D : GateCircuit n) : GateCircuit n where
  gates := C.gates ++ D.gates
  gates_unitary := by
    intro g hg
    rw [List.mem_append] at hg
    rcases hg with hg | hg
    · exact C.gates_unitary g hg
    · exact D.gates_unitary g hg

theorem circuitEval_append (C D : GateCircuit n) :
    circuitEval (circuitAppend C D) = circuitEval C * circuitEval D := by
  simp [circuitEval, circuitAppend, List.prod_append]

theorem circuitGateCount_append (C D : GateCircuit n) :
    circuitGateCount (circuitAppend C D) =
      circuitGateCount C + circuitGateCount D := by
  simp [circuitGateCount, circuitAppend, List.length_append]

def zeroBasis (n : ℕ) : Fin (2 ^ n) :=
  ⟨0, pow_pos (by norm_num : (0 : ℕ) < 2) n⟩

@[simp]
theorem zeroBasis_val (n : ℕ) : (zeroBasis n).val = 0 := rfl

end Qatlib.Papers.UniversalWalk08.MainResults.CircuitDefs
