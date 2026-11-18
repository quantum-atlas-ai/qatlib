/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CircuitLang.WordOps
public import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
public import Qatlib.Concepts.GateVocabulary.LocalReflectionGates
public import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
public import Qatlib.Concepts.GateKit.Cor74Net
public import Qatlib.Foundations.PureStateMath.Qubit

@[expose] public section

/-!
# Exact and approximate gate contracts over the audited public inventory

This module defines two contracts without inventing a compiler. The exact contract wraps a
unitary gate from the audited public inventory (Pauli family, Hadamard, phase S, the
new phase T, SWAP, CNOT) together with its unitarity proof and lifts it to a one-step
query word; the approximate contract records that some unitary approximates a target
entrywise within a positive ε — an existence statement only, never an executable
compilation procedure. The Cor74 network is already a query word via
`Qatlib.Concepts.GateKit.denoteRefl`; that bridge is re-exported here as the inventory's macro-gate
entry.

## Main statements

* `exWord_denote`: a wrapped exact gate denotes to its placed matrix in one step.
* `approxEntry`: entrywise distance bound of an approximate contract.
* `reflWordDenote`: Cor74 reflection words denote the program matrix (re-export).
-/

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CircuitLang.WireReg
open Qatlib.Concepts.CircuitLang.QueryWords
open Qatlib.Concepts.GateKit.Cor74Net

namespace Qatlib.Concepts.GateKit.GateContract

/-- The phase-T gate: diagonal with fourth-root phases; new in this inventory
(the public vocabulary ships I/X/Y/Z, S, and Hadamard only). -/
noncomputable def phaseT : Matrix Bool Bool ℂ :=
  Matrix.diagonal (fun b =>
    if b then (1 + Complex.I) / Complex.ofReal (Real.sqrt 2) else 1)

/-- The diagonal corner product: conjugate times entry of the T phase is one. -/
private theorem tcorner : (1 + -Complex.I) / (Complex.ofReal (Real.sqrt 2))
    * ((1 + Complex.I) / Complex.ofReal (Real.sqrt 2)) = 1 := by
  have hc : (Complex.ofReal (Real.sqrt 2) : ℂ) ≠ 0 := by
    intro h
    rw [Complex.ofReal_eq_zero, Real.sqrt_eq_zero (by norm_num : (0 : ℝ) ≤ 2)] at h
    norm_num at h
  field_simp [hc]
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  push_cast
  linear_combination -Complex.I_mul_I

/-- The phase-T gate is unitary: diagonal with unit-modulus entries. -/
theorem phaseT_unitary : phaseT ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext i j
  cases i <;> cases j <;>
    norm_num [phaseT, Matrix.mul_apply, Fintype.sum_bool, Matrix.diagonal_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply, tcorner]

/-- An exact gate contract: a unitary gate from the audited inventory. -/
structure ExGate where
  /-- The gate matrix over one Boolean qubit. -/
  mat : Matrix Bool Bool ℂ
  /-- Unitarity, carried from the inventory lemma. -/
  uni : mat ∈ Matrix.unitaryGroup Bool ℂ

/-- The Pauli family is in the exact inventory. -/
noncomputable def exPauli (a : Fin 4) : ExGate := ⟨pauliBool a, pauli_unitary a⟩

/-- The phase-S gate is in the exact inventory. -/
def exS : ExGate := ⟨phaseS, phaseS_unitary⟩

/-- The phase-T gate is in the exact inventory. -/
noncomputable def exT : ExGate := ⟨phaseT, phaseT_unitary⟩

/-- The Hadamard gate is in the exact inventory, transported through `toFinGate`. -/
noncomputable def exH : ExGate := ⟨Hadamard, hadamard_unitary⟩

/-- The one-step query word of an exact gate, placed on a one-wire register. -/
noncomputable def exWord (g : ExGate) : Circuit (Reg 1) := [Step.gate (relabelGate regOneBool.symm g.mat)]

/-- An exact gate's one-step word denotes to its placed matrix. -/
theorem exWord_denote (g : ExGate) :
    Denote (1 : Matrix (Reg 1) (Reg 1) ℂ) (exWord g)
      = relabelGate regOneBool.symm g.mat := by
  rw [exWord, denote_gate, denote_nil, Matrix.one_mul]

/-- The exact word is unitary and query-free. Its profile counts one matrix gate
instruction, with no claim of a one-gate realization in a finite elementary gate set. -/
theorem exWord_uni (g : ExGate) :
    Denote (1 : Matrix (Reg 1) (Reg 1) ℂ) (exWord g)
      ∈ Matrix.unitaryGroup (Reg 1) ℂ := by
  rw [exWord_denote]
  exact (relabelGate_mem_unitaryGroup regOneBool.symm g.mat).2 g.uni

/-- An ε-approximate compilation contract: a unitary `approx` entrywise within `eps`
of a `target`. This is an existence statement; no executable compiler, distance
optimum, ancilla cleanup, or phase convention is claimed or constructed here. -/
structure ApproxGate where
  /-- The target matrix being approximated. -/
  target : Matrix Bool Bool ℂ
  /-- The approximating unitary. -/
  approx : Matrix Bool Bool ℂ
  /-- Unitarity of the approximating gate. -/
  uni : approx ∈ Matrix.unitaryGroup Bool ℂ
  /-- The approximation tolerance. -/
  eps : ℝ
  /-- The tolerance is positive. -/
  eps_pos : 0 < eps
  /-- Entrywise distance bound. -/
  entry : ∀ b c, ‖approx b c - target b c‖ ≤ eps

/-- The entrywise bound of an approximate contract, as a standalone statement. -/
theorem approxEntry (A : ApproxGate) (b c : Bool) :
    ‖A.approx b c - A.target b c‖ ≤ A.eps :=
  A.entry b c

/-- The Cor74 reflection program is already a unified query word whose denotation is
the program matrix; re-exported from `Cor74Net` as the inventory's macro entry. -/
theorem reflWordDenote {n : ℕ} (gs : List (ReflectionGate n)) :
    Denote (1 : Matrix (Reg n) (Reg n) ℂ) (reflectionCompile gs)
      = reflectionProgramMatrix gs :=
  denoteRefl gs

end Qatlib.Concepts.GateKit.GateContract
