/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator Kronecker
namespace Qatlib.Concepts.TensorRegisters.RegisterModel.BinaryShift

def bitEncoding (n : ℕ) : BitVec n ≃+* ZMod (2 ^ n) :=
  BitVec.equivFin.trans (ZMod.finEquiv (2 ^ n))

def permU {I : Type*} [Fintype I] [DecidableEq I] (e : Equiv.Perm I) : Matrix I I ℂ :=
  Equiv.Perm.permMatrix ℂ e.symm

theorem permU_unitary {I : Type*} [Fintype I] [DecidableEq I] (e : Equiv.Perm I) :
    permU e ∈ Matrix.unitaryGroup I ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (Equiv.Perm.permMatrix ℂ e.symm)ᴴ * Equiv.Perm.permMatrix ℂ e.symm = 1
  rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
  simp

theorem permU_mulVec {I : Type*} [Fintype I] [DecidableEq I] (e : Equiv.Perm I) (v : I → ℂ) :
    permU e *ᵥ v = v ∘ e.symm := Matrix.permMatrix_mulVec (e.symm : Equiv.Perm I)

def shift {S G : Type*} [AddCommGroup G] (side : S → Bool) (l : G) : Equiv.Perm (S × G) where
  toFun x := (x.1, if side x.1 then x.2 + l else x.2 - l)
  invFun x := (x.1, if side x.1 then x.2 - l else x.2 + l)
  left_inv x := by cases x with | mk s g => cases h : side s <;> simp [h]
  right_inv x := by cases x with | mk s g => cases h : side s <;> simp [h]

def stream {S G : Type*} [Fintype S] [DecidableEq S] [Fintype G] [DecidableEq G]
    [AddCommGroup G] (side : S → Bool) (l : G) : Matrix (S × G) (S × G) ℂ := permU (shift side l)

theorem stream_unitary {S G : Type*} [Fintype S] [DecidableEq S] [Fintype G] [DecidableEq G]
    [AddCommGroup G] (side : S → Bool) (l : G) :
    stream side l ∈ Matrix.unitaryGroup (S × G) ℂ := permU_unitary _

theorem stream_apply {S G : Type*} [Fintype S] [DecidableEq S] [Fintype G] [DecidableEq G]
    [AddCommGroup G] (side : S → Bool) (l : G) (v : S × G → ℂ) (s : S) (g : G) :
    (stream side l *ᵥ v) (s,g) = v (s, if side s then g - l else g + l) := by
  rw [stream, permU_mulVec]
  rfl

def mode {S G : Type*} [AddMonoid G] (χ : AddChar G ℂ) (v : S → ℂ) : S × G → ℂ :=
  fun x => v x.1 * χ x.2

def bloch {S G : Type*} [DecidableEq S] [AddCommGroup G] (side : S → Bool)
    (χ : AddChar G ℂ) (l : G) : Matrix S S ℂ :=
  Matrix.diagonal (fun s => χ (if side s then -l else l))

theorem stream_mode {S G : Type*} [Fintype S] [DecidableEq S] [Fintype G] [DecidableEq G]
    [AddCommGroup G] (side : S → Bool) (χ : AddChar G ℂ) (l : G) (v : S → ℂ) :
    stream side l *ᵥ mode χ v = mode χ (bloch side χ l *ᵥ v) := by
  funext x
  obtain ⟨s,g⟩ := x
  rw [stream_apply]
  cases h : side s <;>
    simp [mode, bloch, Matrix.mulVec_diagonal, h, sub_eq_add_neg, AddChar.map_add_eq_mul] <;> ring

def spinLift {S G : Type*} [DecidableEq G] (P : Matrix S S ℂ) : Matrix (S × G) (S × G) ℂ :=
  P ⊗ₖ (1 : Matrix G G ℂ)

theorem spinLift_unitary {S G : Type*} [Fintype S] [DecidableEq S] [Fintype G] [DecidableEq G]
    (P : Matrix S S ℂ) (hP : P ∈ Matrix.unitaryGroup S ℂ) :
    spinLift (G := G) P ∈ Matrix.unitaryGroup (S × G) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (P ⊗ₖ (1 : Matrix G G ℂ))ᴴ * (P ⊗ₖ (1 : Matrix G G ℂ)) = 1
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
  simpa using! congrArg (fun M : Matrix S S ℂ => M ⊗ₖ (1 : Matrix G G ℂ))
    (Matrix.mem_unitaryGroup_iff'.mp hP)

theorem spinLift_mode {S G : Type*} [Fintype S] [DecidableEq S] [Fintype G] [DecidableEq G]
    [AddMonoid G] (P : Matrix S S ℂ) (χ : AddChar G ℂ) (v : S → ℂ) :
    spinLift P *ᵥ mode χ v = mode χ (P *ᵥ v) := by
  ext x
  rcases x with ⟨s,g⟩
  simp only [spinLift, mode, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.one_apply]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  ring

theorem mode_injective {S G : Type*} [AddMonoid G] (χ : AddChar G ℂ) :
    Function.Injective (mode (S := S) χ) := by
  intro v w he
  funext s
  have h := congrFun he (s,0)
  simpa only [mode, AddChar.map_zero_eq_one, mul_one] using h
