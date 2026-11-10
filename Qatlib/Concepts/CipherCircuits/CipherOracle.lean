/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Qatlib.Concepts.CipherCircuits.CipherOracle
set_option autoImplicit false
noncomputable section
open scoped Matrix
variable {I J : Type*}

abbrev Bank (J : Type*) := J → Bool

abbrev Whole (I J : Type*) := I × (Bank J × Bool)

def zeroBank : Bank J := fun _ => false

def bankXor (a b : Bank J) : Bank J := fun j => a j ^^ b j

theorem bankXor_twice (a b : Bank J) : bankXor (bankXor a b) b = a := by
  funext j
  simp [bankXor]

theorem bankXor_zero (b : Bank J) : bankXor zeroBank b = b := by
  funext j
  simp [bankXor, zeroBank]

def computeFn (values : I → Bank J) (x : Whole I J) : Whole I J :=
  (x.1, (bankXor x.2.1 (values x.1), x.2.2))

def computePerm (values : I → Bank J) : Equiv.Perm (Whole I J) where
  toFun := computeFn values
  invFun := computeFn values
  left_inv := by rintro ⟨k,w,b⟩; simp [computeFn, bankXor_twice]
  right_inv := by rintro ⟨k,w,b⟩; simp [computeFn, bankXor_twice]
variable [Fintype J]

def compareFn (target : Bank J) (x : Whole I J) : Whole I J :=
  (x.1, (x.2.1, x.2.2 ^^ decide (x.2.1 = target)))

def comparePerm (target : Bank J) : Equiv.Perm (Whole I J) where
  toFun := compareFn target
  invFun := compareFn target
  left_inv := by
    rintro ⟨k,w,b⟩
    cases b <;> by_cases h : w = target <;> simp [compareFn, h]
  right_inv := by
    rintro ⟨k,w,b⟩
    cases b <;> by_cases h : w = target <;> simp [compareFn, h]

def oraclePerm (values : I → Bank J) (target : Bank J) : Equiv.Perm (Whole I J) :=
  (computePerm values).trans ((comparePerm target).trans (computePerm values))

theorem oraclePerm_apply (values : I → Bank J) (target : Bank J) (k : I)
    (w : Bank J) (b : Bool) :
    oraclePerm values target (k,w,b) =
      (k,w,b ^^ decide (bankXor w (values k) = target)) := by
  simp [oraclePerm, computePerm, comparePerm, computeFn, compareFn, bankXor_twice]

theorem oraclePerm_clean (values : I → Bank J) (target : Bank J) (k : I) (b : Bool) :
    oraclePerm values target (k,zeroBank,b) =
      (k,zeroBank,b ^^ decide (values k = target)) := by
  rw [oraclePerm_apply, bankXor_zero]

theorem oraclePerm_involutive (values : I → Bank J) (target : Bank J) :
    Function.Involutive (oraclePerm values target) := by
  rintro ⟨k,w,b⟩
  simp only [oraclePerm_apply]
  cases b <;> by_cases h : bankXor w (values k) = target <;> simp [h]
variable [Fintype I] [DecidableEq I] [DecidableEq J]

def oracleMatrix (values : I → Bank J) (target : Bank J) :
    Matrix (Whole I J) (Whole I J) ℂ := (oraclePerm values target).permMatrix ℂ

theorem permutation_unitary {X : Type*} [Fintype X] [DecidableEq X] (e : Equiv.Perm X) :
    e.permMatrix ℂ ∈ Matrix.unitaryGroup X ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
  simp

theorem oracleMatrix_unitary (values : I → Bank J) (target : Bank J) :
    oracleMatrix values target ∈ Matrix.unitaryGroup (Whole I J) ℂ :=
  permutation_unitary _

def minus (b : Bool) : ℂ := if b then -((Real.sqrt 2 / 2 : ℝ) : ℂ) else ((Real.sqrt 2 / 2 : ℝ) : ℂ)

theorem minus_xor (b t : Bool) : minus (b ^^ t) = (if t then (-1 : ℂ) else 1) * minus b := by
  cases b <;> cases t <;> simp [minus]

def auxiliary (x : Bank J × Bool) : ℂ := if x.1 = zeroBank then minus x.2 else 0

def embed (ψ : I → ℂ) (x : Whole I J) : ℂ := ψ x.1 * auxiliary x.2

def phaseMatrix (values : I → Bank J) (target : Bank J) : Matrix I I ℂ :=
  Matrix.diagonal (fun k => if values k = target then -1 else 1)
omit [DecidableEq J] in

theorem phaseMatrix_mulVec (values : I → Bank J) (target : Bank J) (ψ : I → ℂ) (k : I) :
    (phaseMatrix values target *ᵥ ψ) k = (if values k = target then -1 else 1) * ψ k := by
  simp [phaseMatrix, Matrix.mulVec, dotProduct, Matrix.diagonal_apply]

theorem oracleMatrix_embed (values : I → Bank J) (target : Bank J) (ψ : I → ℂ) :
    oracleMatrix values target *ᵥ embed ψ = embed (phaseMatrix values target *ᵥ ψ) := by
  rw [oracleMatrix, Matrix.permMatrix_mulVec]
  funext x
  rcases x with ⟨k,w,b⟩
  rw [Function.comp_apply, oraclePerm_apply]
  by_cases hw : w = zeroBank
  · subst w
    by_cases h : values k = target
    · cases b <;> simp [embed, auxiliary, bankXor_zero, phaseMatrix_mulVec, h, minus]
    · cases b <;> simp [embed, auxiliary, bankXor_zero, phaseMatrix_mulVec, h, minus]
  · simp [embed, auxiliary, hw]

theorem minus_norm_sq (b : Bool) : ‖minus b‖ ^ 2 = (1 : ℝ) / 2 := by
  have h : ‖((Real.sqrt 2 / 2 : ℝ) : ℂ)‖ ^ 2 = (1 : ℝ) / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  cases b <;> simpa [minus] using h

theorem auxiliary_normalized : ∑ x : Bank J × Bool, ‖auxiliary x‖ ^ 2 = 1 := by
  rw [Fintype.sum_prod_type]
  have h (w : Bank J) : (∑ b : Bool, ‖auxiliary (w,b)‖ ^ 2) =
      if w = zeroBank then 1 else 0 := by
    by_cases hw : w = zeroBank
    · simp [auxiliary, hw, minus_norm_sq]
    · simp [auxiliary, hw]
  simp_rw [h]
  simp

end
end Qatlib.Concepts.CipherCircuits.CipherOracle
