/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.List.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# The gate-circuit model of arXiv:0806.1972

Paper: A. M. Childs, *Universal computation by quantum walk*,
arXiv:0806.1972v1 (12 June 2008), Sec. VII:

> an arbitrary `m`-gate quantum circuit describing a unitary transformation `U`
> on `n` qubits can be implemented by quantum walk ...

The paper works with the universal gate set of Sec. III: controlled-NOT,
the phase gate `U_b` of Eq. (16), and the basis-changing gate `U_c` of
Eq. (20).  For the purpose of stating the paper's main theorem we only need
the *combinatorial* shape of a circuit: an ordered list of `m` unitary gates,
together with its product.  The concrete gate set is recorded in the module
documentation of the claim files, where the construction of the widgets is
discussed.
-/

namespace Qatlib.Papers.UniversalWalk08.MainResults.CircuitModel

open Matrix

set_option autoImplicit false

variable {n : ℕ}

/-- A finite gate circuit on `n` qubits: an ordered list of unitary gates.

Paper: arXiv:0806.1972v1, Sec. VII, where `U` is described by an `m`-gate
circuit and `m` is the number of gate widgets inserted in the walk graph. -/
structure GateCircuit (n : ℕ) where
  /-- The gates of the circuit, in temporal order. -/
  gates : List (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
  /-- Every gate is unitary. -/
  gates_unitary : ∀ g ∈ gates, g ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ

/-- The unitary implemented by the circuit: the ordered product of its gates.

Paper: arXiv:0806.1972v1, Sec. VII ("describing a unitary transformation `U`"). -/
noncomputable def circuitEval (C : GateCircuit n) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  C.gates.prod

/-- The number of gates, `m` in the paper.

Paper: arXiv:0806.1972v1, Sec. VII ("an arbitrary `m`-gate quantum circuit"). -/
def circuitGateCount (C : GateCircuit n) : ℕ :=
  C.gates.length

/-- The empty circuit implements the identity. -/
@[simp]
theorem circuitEval_empty :
    circuitEval (⟨[], by simp⟩ : GateCircuit n) = 1 := by
  simp [circuitEval]

/-- Concatenation of circuits multiplies the implemented unitaries. -/
def circuitAppend (C D : GateCircuit n) : GateCircuit n where
  gates := C.gates ++ D.gates
  gates_unitary := by
    intro g hg
    rw [List.mem_append] at hg
    rcases hg with hg | hg
    · exact C.gates_unitary g hg
    · exact D.gates_unitary g hg

/-- The evaluated product of a concatenation is the product of the factors. -/
theorem circuitEval_append (C D : GateCircuit n) :
    circuitEval (circuitAppend C D) = circuitEval C * circuitEval D := by
  simp [circuitEval, circuitAppend, List.prod_append]

/-- The gate count is additive under concatenation. -/
theorem circuitGateCount_append (C D : GateCircuit n) :
    circuitGateCount (circuitAppend C D) =
      circuitGateCount C + circuitGateCount D := by
  simp [circuitGateCount, circuitAppend, List.length_append]

/-- The canonical all-zero basis index `|0⋯0⟩ ∈ ℂ^{2^n}`. -/
def zeroBasis (n : ℕ) : Fin (2 ^ n) :=
  ⟨0, pow_pos (by norm_num : (0 : ℕ) < 2) n⟩

/-- The `zeroBasis_val` result for the UniversalWalk08 paper model. -/
@[simp]
theorem zeroBasis_val (n : ℕ) : (zeroBasis n).val = 0 := rfl

end Qatlib.Papers.UniversalWalk08.MainResults.CircuitModel
