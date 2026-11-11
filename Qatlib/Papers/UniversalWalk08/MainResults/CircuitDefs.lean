/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.List.Basic

/-!
# Finite unitary gate circuits

This module represents an `n`-qubit circuit as a list of unitary matrices, evaluated by their
ordered product. The definitions `GateCircuit`, `circuitEval`, and `zeroBasis` provide circuit
data for the quantum-walk simulation in [Childs2009].

## Main statements

* `circuitEval_append`: Evaluation turns list concatenation into matrix multiplication.
* `circuitGateCount_append`: Gate counts add under concatenation.

## References

* [Childs, 2009][Childs2009]
-/

namespace Qatlib.Papers.UniversalWalk08.MainResults.CircuitDefs

open Matrix

set_option autoImplicit false

variable {n : ℕ}

/-- A finite list of unitary matrices acting on the basis of `n` qubits. -/
structure GateCircuit (n : ℕ) where

  gates : List (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)

  gates_unitary : ∀ g ∈ gates, g ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ

/-- The ordered matrix product of the gates in `C`. -/
noncomputable def circuitEval (C : GateCircuit n) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  C.gates.prod

/-- The number of matrices in the gate list of `C`. -/
def circuitGateCount (C : GateCircuit n) : ℕ :=
  C.gates.length

/-- The circuit with an empty gate list evaluates to the identity matrix. -/
@[simp]
theorem circuitEval_empty :
    circuitEval (⟨[], by simp⟩ : GateCircuit n) = 1 := by
  simp [circuitEval]

/-- The circuit obtained by concatenating the gate lists of `C` and `D`. -/
def circuitAppend (C D : GateCircuit n) : GateCircuit n where
  gates := C.gates ++ D.gates
  gates_unitary := by
    intro g hg
    rw [List.mem_append] at hg
    rcases hg with hg | hg
    · exact C.gates_unitary g hg
    · exact D.gates_unitary g hg

/-- Evaluation of concatenated circuits is the product of their evaluations in list order. -/
theorem circuitEval_append (C D : GateCircuit n) :
    circuitEval (circuitAppend C D) = circuitEval C * circuitEval D := by
  simp [circuitEval, circuitAppend, List.prod_append]

/-- The gate count of concatenated circuits is the sum of their gate counts. -/
theorem circuitGateCount_append (C D : GateCircuit n) :
    circuitGateCount (circuitAppend C D) =
      circuitGateCount C + circuitGateCount D := by
  simp [circuitGateCount, circuitAppend, List.length_append]

/-- The basis index zero in the `n`-qubit computational basis. -/
def zeroBasis (n : ℕ) : Fin (2 ^ n) :=
  ⟨0, pow_pos (by norm_num : (0 : ℕ) < 2) n⟩

/-- The underlying natural-number value of `zeroBasis n` is zero. -/
@[simp]
theorem zeroBasis_val (n : ℕ) : (zeroBasis n).val = 0 := rfl

end Qatlib.Papers.UniversalWalk08.MainResults.CircuitDefs
