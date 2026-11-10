/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Dimension.Finrank
import Qatlib.Concepts.ChannelTheory.Stinespring.ShadowEstimator
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.PauliClifford.ExactRank.BooleanCharacters
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PauliClifford.ExactRank

set_option autoImplicit false

namespace Qatlib.Concepts.PauliClifford.PauliAlgebra

open Matrix

open Qatlib.Concepts.PauliClifford.ExactRank (BooleanVec booleanDot)

inductive Pauli1
  | I
  | X
  | Y
  | Z
  deriving DecidableEq, Fintype

abbrev Phase4 := ZMod 4

abbrev PauliWord (n : ℕ) := Fin n → Pauli1

structure PauliElem (n : ℕ) where

  word : PauliWord n

  phase : Phase4

instance pauliElemOne (n : ℕ) : One (PauliElem n) :=
  ⟨⟨fun _ => Pauli1.I, 0⟩⟩

def pauli1Matrix : Pauli1 → Matrix (Fin 2) (Fin 2) ℂ
  | .I => 1
  | .X => pauliX
  | .Y => pauliY
  | .Z => pauliZ

def pauliWordOp (n : ℕ) (w : PauliWord n) : Matrix (Reg n) (Reg n) ℂ :=
  fun x y => ∏ i, pauli1Matrix (w i) (boolEquivFin2 (x i)) (boolEquivFin2 (y i))

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

def PauliElem.mul {n : ℕ} (p q : PauliElem n) : PauliElem n :=
  ⟨fun i => pauliMul1 (p.word i) (q.word i),
    p.phase + q.phase + ∑ i, pauliMulPhase (p.word i) (q.word i)⟩

def symplecticX {n : ℕ} (w : PauliWord n) : BooleanVec n :=
  fun i => if w i = .X ∨ w i = .Y then 1 else 0

def symplecticZ {n : ℕ} (w : PauliWord n) : BooleanVec n :=
  fun i => if w i = .Y ∨ w i = .Z then 1 else 0

def symplecticForm {n : ℕ} (v w : BooleanVec n × BooleanVec n) : ZMod 2 :=
  booleanDot v.1 w.2 + booleanDot v.2 w.1

inductive CliffordGate (n : ℕ)
  | H (i : Fin n)
  | S (i : Fin n)
  | CNOT (i j : Fin n)

def sGate : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun b => if b then Complex.I else 1

noncomputable def cliffordGateOp (n : ℕ) : CliffordGate n → Matrix (Reg n) (Reg n) ℂ
  | .H i =>
    fun x y => if ∀ j : Fin n, j ≠ i → x j = y j then Hadamard (x i) (y i) else 0
  | .S i =>
    fun x y => if ∀ j : Fin n, j ≠ i → x j = y j then sGate (x i) (y i) else 0
  | .CNOT i j =>
    fun x y =>
      if ∀ k : Fin n, k ≠ i ∧ k ≠ j → x k = y k then CNOT (x i, x j) (y i, y j) else 0

def conjHWord : Pauli1 → Pauli1
  | .I => .I
  | .X => .Z
  | .Y => .Y
  | .Z => .X

def conjHPhase : Pauli1 → Phase4
  | .I => 0
  | .X => 0
  | .Y => 2
  | .Z => 0

def conjSWord : Pauli1 → Pauli1
  | .I => .I
  | .X => .Y
  | .Y => .X
  | .Z => .Z

def conjSPhase : Pauli1 → Phase4
  | .I => 0
  | .X => 0
  | .Y => 2
  | .Z => 0

def cnotControlCross : Pauli1 → Pauli1
  | .I => .I
  | .X => .X
  | .Y => .X
  | .Z => .I

def cnotTargetCross : Pauli1 → Pauli1
  | .I => .I
  | .X => .I
  | .Y => .Z
  | .Z => .Z

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

def IsStabilizerSubgroup {n : ℕ} (S : Set (PauliElem n)) : Prop :=
  (1 : PauliElem n) ∈ S ∧
    ∀ p ∈ S, ∀ q ∈ S, p.mul q ∈ S ∧ ∃ r ∈ S, p.mul r = 1

def ContainsMinusI {n : ℕ} (S : Set (PauliElem n)) : Prop :=
  ⟨fun _ => Pauli1.I, 2⟩ ∈ S

def StabilizerCodespace {n : ℕ} (S : Set (PauliElem n)) : Set (Reg n → ℂ) :=
  {ψ | ∀ p ∈ S, pauliWordOp n p.word *ᵥ ψ = (Complex.I ^ p.phase.val : ℂ) • ψ}

def symplecticImage {n : ℕ} (S : Set (PauliElem n)) : Set (BooleanVec n × BooleanVec n) :=
  (fun p => (symplecticX p.word, symplecticZ p.word)) '' S

noncomputable def StabilizerRank {n : ℕ} (S : Set (PauliElem n)) : ℕ :=
  Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) (symplecticImage S))

end Qatlib.Concepts.PauliClifford.PauliAlgebra
