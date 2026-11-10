/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace Qatlib.Concepts.TensorRegisters.RegisterModel.RootChars

def plane (N : ℕ) [NeZero N] (k : ℤ) : AddChar (ZMod N) ℂ :=
  ZMod.stdAddChar.mulShift (-(k : ZMod N))

def angle (N : ℕ) (k : ℤ) : ℝ := 2 * Real.pi * k / N

theorem plane_one (N : ℕ) [NeZero N] (k : ℤ) :
    plane N k 1 = Complex.exp (-Complex.I * (angle N k : ℂ)) := by
  rw [plane, AddChar.mulShift_apply, mul_one, ← Int.cast_neg, ZMod.stdAddChar_coe]
  congr 1
  unfold angle
  push_cast
  ring

theorem plane_neg_one (N : ℕ) [NeZero N] (k : ℤ) :
    plane N k (-1) = Complex.exp (Complex.I * (angle N k : ℂ)) := by
  rw [plane, AddChar.mulShift_apply]
  simp only [mul_neg, mul_one, neg_neg]
  rw [ZMod.stdAddChar_coe]
  congr 1
  unfold angle
  push_cast
  ring

def prodChar {G H : Type*} [AddMonoid G] [AddMonoid H] (χ : AddChar G ℂ) (ψ : AddChar H ℂ) :
    AddChar (G × H) ℂ where
  toFun x := χ x.1 * ψ x.2
  map_zero_eq_one' := by simp only [Prod.fst_zero, Prod.snd_zero, AddChar.map_zero_eq_one, mul_one]
  map_add_eq_mul' x y := by
    simp only [Prod.fst_add, Prod.snd_add, AddChar.map_add_eq_mul]
    ring
