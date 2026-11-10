/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Kronecker

namespace Qatlib.Papers.CommuteTest05.QueryDefs

def xGate : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

def hGate : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2 : ℂ)⁻¹) • !![1, 1; 1, -1]

theorem xGate_mul_self : xGate * xGate = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xGate, Matrix.mul_apply, Fin.sum_univ_two]

theorem sqrtTwo_sq_complex : ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)) = 2 := by
  rw [← Complex.ofReal_mul]
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    rw [← sq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h]
  norm_num

theorem hGate_mul_self : hGate * hGate = 1 := by
  have h2 : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
    rw [← mul_inv, sqrtTwo_sq_complex]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hGate, Matrix.mul_apply, Fin.sum_univ_two, h2] <;> norm_num

abbrev Q : Type := Fin 2 × Fin 2

def xBoth : Matrix Q Q ℂ := fun i j => xGate i.1 j.1 * xGate i.2 j.2

def hSecond : Matrix Q Q ℂ := fun i j =>
  (if i.1 = j.1 then 1 else 0) * hGate i.2 j.2

def czGate : Matrix Q Q ℂ := fun i j =>
  if i = j then (if i = (1, 1) then -1 else 1) else 0

def cnotGate : Matrix Q Q ℂ := fun i j =>
  if j = (i.1, if i.1 = 1 then (1 - i.2) else i.2) then 1 else 0

def rankOne (a b : Q) : Matrix Q Q ℂ := fun i j =>
  if i = a then (if j = b then 1 else 0) else 0

def phaseFlip : Matrix Q Q ℂ := fun i j =>
  if i = j then (if i = (0, 0) then -1 else 1) else 0

theorem phaseFlip_apply (i j : Q) :
    phaseFlip i j = if i = j then (if i = (0, 0) then -1 else 1) else 0 := rfl

theorem phaseFlip_mul_self : phaseFlip * phaseFlip = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  obtain ⟨i1, i2⟩ := i
  obtain ⟨j1, j2⟩ := j
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    simp [phaseFlip_apply]

theorem czGate_mul_self : czGate * czGate = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  obtain ⟨i1, i2⟩ := i
  obtain ⟨j1, j2⟩ := j
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    simp [czGate]

theorem cnotGate_mul_self : cnotGate * cnotGate = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  obtain ⟨i1, i2⟩ := i
  obtain ⟨j1, j2⟩ := j
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    simp [cnotGate, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem bool_xor_cancel (b c : Bool) : Bool.xor (Bool.xor b c) c = b := by
  cases b <;> cases c <;> rfl

def oracle {X : Type} [DecidableEq X] (f : X → Bool) : Matrix (X × Bool) (X × Bool) ℂ :=
  fun i j => if j = (i.1, Bool.xor i.2 (f i.1)) then 1 else 0

theorem oracle_apply {X : Type} [DecidableEq X] (f : X → Bool) (i j : X × Bool) :
    oracle f i j = if j = (i.1, Bool.xor i.2 (f i.1)) then 1 else 0 := rfl

theorem oracle_mul_self {X : Type} [Fintype X] [DecidableEq X] (f : X → Bool) :
    oracle f * oracle f = (1 : Matrix (X × Bool) (X × Bool) ℂ) := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  let a0 : X × Bool := (i.1, Bool.xor i.2 (f i.1))
  have hsingle : (∑ a : X × Bool, oracle f i a * oracle f a j) = oracle f a0 j := by
    rw [Fintype.sum_eq_single a0]
    · rw [oracle_apply, if_pos rfl, one_mul]
    · intro a ha
      rw [oracle_apply, if_neg ha, zero_mul]
  rw [hsingle, oracle_apply]
  have hkey : (a0.1, Bool.xor a0.2 (f a0.1)) = i := by
    obtain ⟨ix, ib⟩ := i
    simp [a0]
  rw [hkey]
  simp [eq_comm]

theorem oracle_symm {X : Type} [DecidableEq X] (f : X → Bool) (i j : X × Bool) :
    oracle f i j = oracle f j i := by
  rw [oracle_apply, oracle_apply]
  by_cases hij : j = (i.1, Bool.xor i.2 (f i.1))
  · rw [if_pos hij]
    rw [if_pos (by rw [hij]; simp)]
  · rw [if_neg hij, if_neg]
    intro hji
    apply hij
    rw [hji]
    simp

theorem oracle_star {X : Type} [Fintype X] [DecidableEq X] (f : X → Bool) :
    star (oracle f) = oracle f := by
  ext i j
  rw [Matrix.star_apply, oracle_symm, oracle_apply]
  split_ifs <;> simp

theorem oracle_unitary {X : Type} [Fintype X] [DecidableEq X] (f : X → Bool) :
    (oracle f)ᴴ * oracle f = 1 := by
  rw [← Matrix.star_eq_conjTranspose, oracle_star, oracle_mul_self]

theorem oracle_mem_unitary {X : Type} [Fintype X] [DecidableEq X] (f : X → Bool) :
    oracle f ∈ Matrix.unitaryGroup (X × Bool) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  exact oracle_unitary f

theorem query_word_mem_unitary {X : Type} [Fintype X] [DecidableEq X]
    (l : List (Matrix (X × Bool) (X × Bool) ℂ))
    (hl : ∀ A ∈ l, A ∈ Matrix.unitaryGroup (X × Bool) ℂ) :
    l.prod ∈ Matrix.unitaryGroup (X × Bool) ℂ :=
  Submonoid.list_prod_mem (s := Matrix.unitaryGroup (X × Bool) ℂ) hl

end Qatlib.Papers.CommuteTest05.QueryDefs
