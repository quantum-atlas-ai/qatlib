/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordStabilizerCoreDefs
import Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Concepts.PauliClifford.ExactRank (BooleanVec booleanDot)

namespace Qatlib.Papers.CliffordGroup03.MainResults

abbrev BV (n : ℕ) := BooleanVec n

def Umat (n : ℕ) : Matrix (Fin (2 * n)) (Fin (2 * n)) (ZMod 2) :=
  fun i j => if i.val < n ∧ j.val = i.val + n then 1 else 0

def Pmat (n : ℕ) : Matrix (Fin (2 * n)) (Fin (2 * n)) (ZMod 2) := Umat n + (Umat n)ᵀ

def Symplectic (n : ℕ) (C : Matrix (Fin (2 * n)) (Fin (2 * n)) (ZMod 2)) : Prop :=
  Cᵀ * Pmat n * C = Pmat n

def lows {m : ℕ} (M : Matrix (Fin m) (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2) :=
  fun i j => if j.val < i.val then M i j else 0

def diagVec {m : ℕ} (M : Matrix (Fin m) (Fin m) (ZMod 2)) : BV m := fun i => M i i

def Symm {m : ℕ} (M : Matrix (Fin m) (Fin m) (ZMod 2)) : Prop := Mᵀ = M

def quadForm {ι : Type*} [Fintype ι] (M : Matrix ι ι (ZMod 2)) (x : ι → ZMod 2) : ZMod 2 :=
  ∑ i, ∑ j, x i * M i j * x j

def stdBasis {m : ℕ} (k : Fin m) : BV m := fun i => if i = k then 1 else 0

def splitVec {n : ℕ} (a : BV (2 * n)) : BV n × BV n :=
  (fun j => a ⟨j.val, by have := j.isLt; omega⟩,
   fun j => a ⟨n + j.val, by have := j.isLt; omega⟩)

def colVec {m : ℕ} (C : Matrix (Fin m) (Fin m) (ZMod 2)) (k : Fin m) : BV m := fun i => C i k

def letter (v w : ZMod 2) : Pauli1 :=
  if v = 1 then (if w = 1 then .Y else .Z) else (if w = 1 then .X else .I)

def tau1 (v w : ZMod 2) : Matrix Bool Bool ℂ :=
  (Complex.I ^ (v * w).val : ℂ) • P1 (letter v w)

def tau {n : ℕ} (a : BV n × BV n) : Matrix (Reg n) (Reg n) ℂ :=
  productMatrix (fun k => tau1 (a.1 k) (a.2 k))

abbrev Ext (n : ℕ) := Option (Fin (2 * n))

def evec {n : ℕ} (b : BV (2 * n)) (δ : ZMod 2) : Ext n → ZMod 2
  | some i => b i
  | none => δ

def CbarMat {n : ℕ} (C : Matrix (Fin (2 * n)) (Fin (2 * n)) (ZMod 2)) (d : BV (2 * n)) :
    Matrix (Ext n) (Ext n) (ZMod 2)
  | some i, some j => C i j
  | some _, none => 0
  | none, some j => d j
  | none, none => 1

def Ubar (n : ℕ) : Matrix (Ext n) (Ext n) (ZMod 2)
  | some i, some j => Umat n i j
  | some _, none => 0
  | none, some _ => 0
  | none, none => 1

def hbar {n : ℕ} (h : BV (2 * n)) : Ext n → ZMod 2
  | some i => h i
  | none => 0

def lowsOpt {n : ℕ} (M : Matrix (Ext n) (Ext n) (ZMod 2)) : Matrix (Ext n) (Ext n) (ZMod 2) :=
  fun i j =>
    match i, j with
    | none, some _ => M i j
    | none, none => 0
    | some i', some j' => if j'.val < i'.val then M i j else 0
    | some _, none => 0

def extDot {n : ℕ} (x y : Ext n → ZMod 2) : ZMod 2 := ∑ o, x o * y o

def diagVecOpt {n : ℕ} (M : Matrix (Ext n) (Ext n) (ZMod 2)) : Ext n → ZMod 2 := fun i => M i i

def RepresentsClifford {n : ℕ} (Q : Matrix (Reg n) (Reg n) ℂ)
    (C : Matrix (Fin (2 * n)) (Fin (2 * n)) (ZMod 2)) (h : BV (2 * n)) : Prop :=
  ∀ k : Fin (2 * n),
    Q * tau (splitVec (stdBasis k)) * Qᴴ =
      ((Complex.I ^ ((diagVec (Cᵀ * Umat n * C)) k).val : ℂ) *
          ((-1 : ℂ) ^ (h k).val)) • tau (splitVec (colVec C k))

end Qatlib.Papers.CliffordGroup03.MainResults
