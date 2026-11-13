/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordStabilizerCoreDefs

/-!
# Matrix semantics for Pauli and Clifford words

This module defines the matrix interpretation `op` of Pauli elements and the predicate
`legalGate`, which requires distinct control and target sites for CNOT. The action
`verifiedCliffordAction` records the Pauli word and phase changes under H, S, and CNOT,
following the binary Clifford formalism of [DehaeneDeMoor2003].

The definitions `Uword` and `actionWord` accumulate gate matrices and Pauli actions in list
order. The correction `cnotPhaseCorrection` adds phase two for the local XZ and YY cases,
retaining the minus sign in those conjugations.

## Main statements

* `op`: Pauli word matrix scaled by its fourth-root-of-unity phase.
* `legalGate`: legality predicate for the supported Clifford gates.
* `verifiedCliffordAction`: gate action on Pauli elements including phase changes.
* `Uword`: matrix of a gate list, with the first gate applied first.
* `actionWord`: successive verified Pauli actions along a gate list.

## References

* [Dehaene and De Moor, 2003][DehaeneDeMoor2003]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.PauliClifford.PauliAlgebra

open Qatlib.Concepts.PauliClifford.PauliAlgebra

/-- Interpret a Pauli element as its Pauli word matrix multiplied by the scalar `Complex.I ^
p.phase.val`. -/
def op {n : ℕ} (p : PauliElem n) : Matrix (Reg n) (Reg n) ℂ :=
  (Complex.I ^ p.phase.val : ℂ) • pauliWordOp n p.word

/-- The legality predicate for Clifford gates: H and S are always legal, and CNOT requires
distinct control and target sites. -/
def legalGate {n : ℕ} : CliffordGate n → Prop
  | .H _ => True
  | .S _ => True
  | .CNOT i j => i ≠ j

/-- The CNOT phase increment is two for the local pairs XZ and YY, and zero for all other pairs. -/
def cnotPhaseCorrection (a b : Pauli1) : Phase4 :=
  if (a = .X ∧ b = .Z) ∨ (a = .Y ∧ b = .Y) then 2 else 0

/-- Update a Pauli element under H, S, or CNOT, including the gate's phase change. For CNOT, the
phase update uses `cnotPhaseCorrection`. -/
def verifiedCliffordAction {n : ℕ} (g : CliffordGate n) (p : PauliElem n) : PauliElem n :=
  match g with
  | .H i =>
    ⟨fun k => if k = i then conjHWord (p.word i) else p.word k,
      p.phase + ∑ k, if k = i then conjHPhase (p.word i) else 0⟩
  | .S i =>
    ⟨fun k => if k = i then conjSWord (p.word i) else p.word k,
      p.phase + ∑ k, if k = i then conjSPhase (p.word i) else 0⟩
  | .CNOT i j =>
    ⟨fun k =>
        if k = i then pauliMul1 (p.word i) (cnotTargetCross (p.word j))
        else if k = j then pauliMul1 (cnotControlCross (p.word i)) (p.word j)
        else p.word k,
      p.phase + cnotPhaseCorrection (p.word i) (p.word j)⟩

/-- Accumulate the matrices of a Clifford gate list by left multiplication, so the first listed
gate acts first. -/
def Uword {n : ℕ} (gs : List (CliffordGate n)) : Matrix (Reg n) (Reg n) ℂ :=
  gs.foldl (fun U g => cliffordGateOp n g * U) 1

/-- Apply `verifiedCliffordAction` successively to a Pauli element in the order of the gate
list. -/
def actionWord {n : ℕ} (gs : List (CliffordGate n)) (p : PauliElem n) : PauliElem n :=
  gs.foldl (fun q g => verifiedCliffordAction g q) p

end Qatlib.Concepts.PauliClifford.PauliAlgebra
