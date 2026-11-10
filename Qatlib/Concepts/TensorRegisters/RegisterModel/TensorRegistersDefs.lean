/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Algebra.BigOperators.Fin
import QuantumInfo.ForMathlib.Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib

set_option autoImplicit false

namespace Qatlib.Concepts.TensorRegisters.RegisterModel

open scoped BigOperators Kronecker

noncomputable def productMatrix {ι : Type*} [Fintype ι] {S : ι → Type*} {T : ι → Type*}
    (A : ∀ i, Matrix (S i) (T i) ℂ) : Matrix (∀ i, S i) (∀ i, T i) ℂ :=
  fun x y => ∏ i, A i (x i) (y i)

noncomputable def partitionReduce {S A B : Type*} [Fintype B] (e : S ≃ A × B)
    (X : Matrix S S ℂ) : Matrix A A ℂ := Matrix.traceRight (Matrix.reindex e e X)

noncomputable def partitionLift {S A B : Type*} [DecidableEq B] (e : S ≃ A × B)
    (U : Matrix A A ℂ) : Matrix S S ℂ :=
  Matrix.reindex e.symm e.symm (U ⊗ₖ (1 : Matrix B B ℂ))

abbrev Labels {m : ℕ} (d : Fin m → ℕ) := ∀ i, Fin (d i)

def flatten {m : ℕ} (d : Fin m → ℕ) : Labels d ≃ Fin (∏ i, d i) := finPiFinEquiv

def toReg {m : ℕ} (d : Fin m → ℕ) (q : ℕ) (h : (∏ i, d i) ≤ 2 ^ q)
    (x : Labels d) : Reg q :=
  (bitVecEquiv q).symm (Fin.castLE h (flatten d x))

def fromReg {m : ℕ} (d : Fin m → ℕ) (q : ℕ) (b : Reg q) : Option (Labels d) :=
  if h : (bitVecEquiv q b).val < ∏ i, d i then
    some ((flatten d).symm ⟨(bitVecEquiv q b).val, h⟩)
  else none

def exactRegEquiv {m : ℕ} (d : Fin m → ℕ) (q : ℕ) (h : (∏ i, d i) = 2 ^ q) :
    Labels d ≃ Reg q :=
  ((flatten d).trans (finCongr h)).trans (bitVecEquiv q).symm

noncomputable def paddingFrame {m : ℕ} (d : Fin m → ℕ) (q : ℕ)
    (h : (∏ i, d i) ≤ 2 ^ q) : Matrix (Reg q) (Labels d) ℂ :=
  fun b x => if b = toReg d q h x then 1 else 0

noncomputable def paddedGate {m : ℕ} (d : Fin m → ℕ) (q : ℕ)
    (h : (∏ i, d i) ≤ 2 ^ q) (U : Matrix (Labels d) (Labels d) ℂ) :
    Matrix (Reg q) (Reg q) ℂ :=
  paddingFrame d q h * U * (paddingFrame d q h).conjTranspose +
    (1 - paddingFrame d q h * (paddingFrame d q h).conjTranspose)

end Qatlib.Concepts.TensorRegisters.RegisterModel
