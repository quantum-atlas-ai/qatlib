/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Basic.Unique
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Qatlib.Papers.JonesPolyShor07.MainResults.Definitions.FibonacciRepresentation
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.JonesPolyShor07.MainResults.Definitions

open Matrix
open scoped BigOperators

def Mdiag (α : ℝ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j =>
    if i = j then
      (if i.val = 4 then Complex.exp (-(α / 2) * Complex.I)
       else Complex.exp ((α / 2) * Complex.I))
    else 0

def Mn : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => bFib
    | 1, 1 => aFib
    | 2, 2 => aFib
    | 3, 3 => eFib
    | 3, 4 => dFib
    | 4, 3 => dFib
    | 4, 4 => cFib
    | _, _ => 0

def blockDiag5 (φ1 φ2 : ℂ) (V : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => φ1
    | 1, 1 => φ2
    | 2, 2 => φ2
    | 3, 3 => V 0 0
    | 3, 4 => V 0 1
    | 4, 3 => V 1 0
    | 4, 4 => V 1 1
    | _, _ => 0

theorem Mdiag_eq_diagonal (α : ℝ) :
    Mdiag α = Matrix.diagonal
      (fun i : Fin 5 =>
        if i.val = 4 then Complex.exp (-(α / 2) * Complex.I)
        else Complex.exp ((α / 2) * Complex.I)) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [Mdiag, Matrix.diagonal]
  · simp [Mdiag, Matrix.diagonal, h]

theorem Mdiag_mul (α β : ℝ) : Mdiag α * Mdiag β = Mdiag (α + β) := by
  rw [Mdiag_eq_diagonal, Mdiag_eq_diagonal, Mdiag_eq_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases h : i.val = 4
  · simp only [h, if_true]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  · simp only [h, if_false]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring

theorem Mdiag_zero : Mdiag 0 = 1 := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [Mdiag]
  · simp [Mdiag, h]

theorem blockDiag5_mul (φ1 φ2 ψ1 ψ2 : ℂ) (V W : Matrix (Fin 2) (Fin 2) ℂ) :
    blockDiag5 φ1 φ2 V * blockDiag5 ψ1 ψ2 W = blockDiag5 (φ1 * ψ1) (φ2 * ψ2) (V * W) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockDiag5, Matrix.mul_apply, Fin.sum_univ_succ]

end Qatlib.Papers.JonesPolyShor07.MainResults.Definitions
