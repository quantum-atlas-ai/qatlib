/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PureStateMath.Qubit
public import Mathlib.LinearAlgebra.Matrix.Reindex

@[expose] public section

/-!
# Wire numbers versus register states, and the `Fin (2 ^ n)` reindex bridge

`Wire n` is the type of wire numbers of an `n`-wire register; an `n`-bit computational basis
vector is `Reg n = Fin n → Bool`, and `Fin n` itself is never treated as an `n`-qubit Hilbert
space. Conversion between the register basis and the `Fin (2 ^ n)` basis goes through the
explicit equivalence `bitVecEquiv` and square matrix reindexing, which preserves products,
identity, and unitarity.

## Main statements

* `reidxUnitary`: square reindexing along an equivalence preserves unitarity.
* `reidxReg_uni`: the `Fin (2 ^ n)` transport of a unitary matrix is unitary.
* `reidxReg_round`: reindexing to `Fin (2 ^ n)` and back is the identity.
-/

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.CircuitLang.WireReg

/-- The wire numbers of an `n`-wire register: indices only, not a Hilbert space. -/
abbrev Wire (n : ℕ) : Type := Fin n

/-- Reading the bit carried by one wire of a register is function application. -/
def readWire {n : ℕ} (w : Wire n) (x : Reg n) : Bool := x w

/-- An `n`-bit register is exactly an assignment of bits to wire numbers. -/
theorem reg_wire_eq (n : ℕ) : Reg n = (Wire n → Bool) := rfl

/-- Square matrix reindexing along an equivalence, evaluated entrywise. -/
theorem reidx_apply {I J : Type*} (e : J ≃ I) (M : Matrix J J ℂ) (x y : I) :
    Matrix.reindex e e M x y = M (e.symm x) (e.symm y) := rfl

/-- Square reindexing is multiplicative. -/
theorem reidxMul {I J : Type*} [Fintype I] [Fintype J]
    (e : J ≃ I) (A B : Matrix J J ℂ) :
    Matrix.reindex e e (A * B) = Matrix.reindex e e A * Matrix.reindex e e B := by
  ext x y
  simp only [Matrix.mul_apply, reidx_apply]
  exact Fintype.sum_equiv e
    (fun z : J => A (e.symm x) z * B z (e.symm y))
    (fun w : I => A (e.symm x) (e.symm w) * B (e.symm w) (e.symm y))
    (fun z => by simp)

/-- Square reindexing preserves the identity matrix. -/
theorem reidxOne {I J : Type*} [DecidableEq I] [DecidableEq J]
    (e : J ≃ I) : Matrix.reindex e e (1 : Matrix J J ℂ) = 1 := by
  ext x y
  simp only [reidx_apply, Matrix.one_apply, e.symm.injective.eq_iff]

/-- Square reindexing commutes with conjugate transposition. -/
theorem reidxConj {I J : Type*} (e : J ≃ I) (M : Matrix J J ℂ) :
    Matrix.conjTranspose (Matrix.reindex e e M) = Matrix.reindex e e (Matrix.conjTranspose M) :=
  rfl

/-- Square reindexing along an equivalence preserves unitarity. -/
theorem reidxUnitary {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : J ≃ I) {M : Matrix J J ℂ} (hM : M ∈ Matrix.unitaryGroup J ℂ) :
    Matrix.reindex e e M ∈ Matrix.unitaryGroup I ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hM
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, reidxConj, ← reidxMul, hM,
    reidxOne]

/-- Transport a `Fin (2 ^ n)`-indexed matrix to the register basis via `bitVecEquiv`. -/
def ReidxReg (n : ℕ) (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    Matrix (Reg n) (Reg n) ℂ :=
  Matrix.reindex (bitVecEquiv n).symm (bitVecEquiv n).symm M

/-- Entries of the transported matrix read the basis vector through the equivalence. -/
theorem reidxReg_apply (n : ℕ) (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (x y : Reg n) :
    ReidxReg n M x y = M (bitVecEquiv n x) (bitVecEquiv n y) := rfl

/-- The `Fin (2 ^ n)` transport preserves unitarity. -/
theorem reidxReg_uni (n : ℕ) {M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hM : M ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    ReidxReg n M ∈ Matrix.unitaryGroup (Reg n) ℂ :=
  reidxUnitary _ hM

/-- Reindexing a register matrix to `Fin (2 ^ n)` and back is the identity. -/
theorem reidxReg_round (n : ℕ) (M : Matrix (Reg n) (Reg n) ℂ) :
    ReidxReg n (Matrix.reindex (bitVecEquiv n) (bitVecEquiv n) M) = M := by
  have h : ReidxReg n (Matrix.reindex (bitVecEquiv n) (bitVecEquiv n) M)
      = (Matrix.reindex (bitVecEquiv n) (bitVecEquiv n)).symm
        (Matrix.reindex (bitVecEquiv n) (bitVecEquiv n) M) := by
    simp [ReidxReg, Matrix.reindex_symm, Equiv.symm_symm]
  rw [h]
  exact Equiv.symm_apply_apply _ M

end Qatlib.Concepts.CircuitLang.WireReg
