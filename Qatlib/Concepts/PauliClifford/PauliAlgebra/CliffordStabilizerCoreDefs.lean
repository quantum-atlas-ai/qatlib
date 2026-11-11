/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Dimension.Finrank
import Qatlib.Concepts.ChannelTheory.Stinespring.ShadowEstimator
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.PauliClifford.ExactRank.BooleanCharacters

/-!
# Pauli words and Clifford gate data

This module defines `Pauli1`, `PauliElem`, binary symplectic coordinates, and the matrix data
for H, S, and CNOT gates. Pauli multiplication records powers of i through `Phase4`; the binary
description is standard background in [DehaeneDeMoor2003].

It also defines subgroup predicates, phase-eigenvalue code spaces, and `StabilizerRank`. The
update `cliffordAction` includes H and S phase changes and leaves the phase unchanged in its
CNOT branch; later modules provide the verified Clifford action.

## Main statements

* `PauliElem.mul`: Pauli multiplication combines word products and local phase exponents.
* `symplecticForm`: The binary symplectic pairing of Pauli coordinate pairs.
* `StabilizerRank`: The binary dimension of the span of a set's symplectic image.

## References

* [Dehaene and De Moor, 2003][DehaeneDeMoor2003]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PauliClifford.ExactRank

set_option autoImplicit false

namespace Qatlib.Concepts.PauliClifford.PauliAlgebra

open Matrix

open Qatlib.Concepts.PauliClifford.ExactRank (BooleanVec booleanDot)

/-- The four single-qubit Pauli letters I, X, Y, and Z. -/
inductive Pauli1
  | I
  | X
  | Y
  | Z
  deriving DecidableEq, Fintype

/-- Exponents modulo four representing powers of the imaginary unit. -/
abbrev Phase4 := ZMod 4

/-- A Pauli letter assigned to each of n qubit positions. -/
abbrev PauliWord (n : ℕ) := Fin n → Pauli1

/-- An n-qubit Pauli word together with an exponent modulo four for its global phase. -/
structure PauliElem (n : ℕ) where

  word : PauliWord n

  phase : Phase4

instance pauliElemOne (n : ℕ) : One (PauliElem n) :=
  ⟨⟨fun _ => Pauli1.I, 0⟩⟩

/-- The complex two-by-two matrix associated with a single-qubit Pauli letter. -/
def pauli1Matrix : Pauli1 → Matrix (Fin 2) (Fin 2) ℂ
  | .I => 1
  | .X => pauliX
  | .Y => pauliY
  | .Z => pauliZ

/-- The register matrix of a Pauli word, with entries given by products of its single-qubit
matrix entries. -/
def pauliWordOp (n : ℕ) (w : PauliWord n) : Matrix (Reg n) (Reg n) ℂ :=
  fun x y => ∏ i, pauli1Matrix (w i) (boolEquivFin2 (x i)) (boolEquivFin2 (y i))

/-- The Pauli letter in a single-qubit product after discarding its scalar phase. -/
def pauliMul1 : Pauli1 → Pauli1 → Pauli1
  | .I, a => a
  | a, .I => a
  | .X, .X => .I
  | .Y, .Y => .I
  | .Z, .Z => .I
  | .X, .Y => .Z
  | .Y, .X => .Z
  | .Y, .Z => .X
  | .Z, .Y => .X
  | .Z, .X => .Y
  | .X, .Z => .Y

/-- The exponent modulo four of the scalar phase in a single-qubit Pauli product. -/
def pauliMulPhase : Pauli1 → Pauli1 → Phase4
  | .I, _ => 0
  | _, .I => 0
  | .X, .X => 0
  | .Y, .Y => 0
  | .Z, .Z => 0
  | .X, .Y => 1
  | .Y, .Z => 1
  | .Z, .X => 1
  | .Y, .X => 3
  | .Z, .Y => 3
  | .X, .Z => 3

/-- Multiplication of Pauli elements, combining their words and adding their global and local
phase contributions. -/
def PauliElem.mul {n : ℕ} (p q : PauliElem n) : PauliElem n :=
  ⟨fun i => pauliMul1 (p.word i) (q.word i),
    p.phase + q.phase + ∑ i, pauliMulPhase (p.word i) (q.word i)⟩

/-- The binary X coordinates of a Pauli word, equal to one at X and Y letters. -/
def symplecticX {n : ℕ} (w : PauliWord n) : BooleanVec n :=
  fun i => if w i = .X ∨ w i = .Y then 1 else 0

/-- The binary Z coordinates of a Pauli word, equal to one at Y and Z letters. -/
def symplecticZ {n : ℕ} (w : PauliWord n) : BooleanVec n :=
  fun i => if w i = .Y ∨ w i = .Z then 1 else 0

/-- The binary symplectic pairing of two pairs of Boolean vectors. -/
def symplecticForm {n : ℕ} (v w : BooleanVec n × BooleanVec n) : ZMod 2 :=
  booleanDot v.1 w.2 + booleanDot v.2 w.1

/-- Hadamard, phase, and controlled-NOT gates with register positions as parameters. -/
inductive CliffordGate (n : ℕ)
  | H (i : Fin n)
  | S (i : Fin n)
  | CNOT (i j : Fin n)

/-- The single-qubit phase gate with diagonal entries 1 and i. -/
def sGate : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun b => if b then Complex.I else 1

/-- The register matrix of a Hadamard, phase, or controlled-NOT gate acting at the specified
positions. -/
noncomputable def cliffordGateOp (n : ℕ) : CliffordGate n → Matrix (Reg n) (Reg n) ℂ
  | .H i =>
    fun x y => if ∀ j : Fin n, j ≠ i → x j = y j then Hadamard (x i) (y i) else 0
  | .S i =>
    fun x y => if ∀ j : Fin n, j ≠ i → x j = y j then sGate (x i) (y i) else 0
  | .CNOT i j =>
    fun x y =>
      if ∀ k : Fin n, k ≠ i ∧ k ≠ j → x k = y k then CNOT (x i, x j) (y i, y j) else 0

/-- The Pauli letter obtained by Hadamard conjugation, with its scalar phase omitted. -/
def conjHWord : Pauli1 → Pauli1
  | .I => .I
  | .X => .Z
  | .Y => .Y
  | .Z => .X

/-- The phase exponent contributed by Hadamard conjugation of a Pauli letter. -/
def conjHPhase : Pauli1 → Phase4
  | .I => 0
  | .X => 0
  | .Y => 2
  | .Z => 0

/-- The Pauli letter obtained by phase-gate conjugation, with its scalar phase omitted. -/
def conjSWord : Pauli1 → Pauli1
  | .I => .I
  | .X => .Y
  | .Y => .X
  | .Z => .Z

/-- The phase exponent contributed by phase-gate conjugation of a Pauli letter. -/
def conjSPhase : Pauli1 → Phase4
  | .I => 0
  | .X => 0
  | .Y => 2
  | .Z => 0

/-- The X contribution propagated from the control letter to the target under controlled-NOT
conjugation. -/
def cnotControlCross : Pauli1 → Pauli1
  | .I => .I
  | .X => .X
  | .Y => .X
  | .Z => .I

/-- The Z contribution propagated from the target letter to the control under controlled-NOT
conjugation. -/
def cnotTargetCross : Pauli1 → Pauli1
  | .I => .I
  | .X => .I
  | .Y => .Z
  | .Z => .Z

/-- The Pauli word update for a Clifford gate, with phase corrections for H and S and unchanged
phase for CNOT. -/
def cliffordAction {n : ℕ} (g : CliffordGate n) (p : PauliElem n) : PauliElem n :=
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
      p.phase⟩

/-- The condition that a set of Pauli elements contains the identity and is closed under
multiplication, with a right inverse in the set for every element. -/
def IsStabilizerSubgroup {n : ℕ} (S : Set (PauliElem n)) : Prop :=
  (1 : PauliElem n) ∈ S ∧
    ∀ p ∈ S, ∀ q ∈ S, p.mul q ∈ S ∧ ∃ r ∈ S, p.mul r = 1

/-- The condition that a set contains the identity Pauli word with phase exponent two. -/
def ContainsMinusI {n : ℕ} (S : Set (PauliElem n)) : Prop :=
  ⟨fun _ => Pauli1.I, 2⟩ ∈ S

/-- The functions whose Pauli-word action equals multiplication by the encoded phase for every
element of the given set. -/
def StabilizerCodespace {n : ℕ} (S : Set (PauliElem n)) : Set (Reg n → ℂ) :=
  {ψ | ∀ p ∈ S, pauliWordOp n p.word *ᵥ ψ = (Complex.I ^ p.phase.val : ℂ) • ψ}

/-- The set of binary X and Z coordinate pairs of the Pauli elements in a given set. -/
def symplecticImage {n : ℕ} (S : Set (PauliElem n)) : Set (BooleanVec n × BooleanVec n) :=
  (fun p => (symplecticX p.word, symplecticZ p.word)) '' S

/-- The dimension over the two-element field of the span of a set's symplectic image. -/
noncomputable def StabilizerRank {n : ℕ} (S : Set (PauliElem n)) : ℕ :=
  Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) (symplecticImage S))

end Qatlib.Concepts.PauliClifford.PauliAlgebra
