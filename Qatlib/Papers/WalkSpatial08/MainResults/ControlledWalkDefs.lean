/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.WalkSpatial08.MainResults.SearchDefs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Reflection
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.WalkSpatial08.MainResults

open Matrix

def Xdelta (δ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j =>
    if i = 0 then (if j = 0 then Real.cos δ else Real.sin δ)
    else (if j = 0 then -Real.sin δ else Real.cos δ)

def Zbar : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j =>
    if i = 0 then (if j = 0 then -1 else 0) else (if j = 0 then 0 else 1)

def ket0 : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0

def ket1 : Fin 2 → ℝ := fun i => if i = 0 then 0 else 1

def delta0 (δ : ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then Real.cos δ else Real.sin δ

def delta1 (δ : ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then -Real.sin δ else Real.cos δ

def rankOne {ι : Type*} (v : ι → ℝ) : Matrix ι ι ℝ := fun i j => v i * v j

theorem Xdelta_transpose_mulVec_ket0 (δ : ℝ) :
    mulVec (transpose (Xdelta δ)) ket0 = delta0 δ := by
  funext i
  fin_cases i <;>
    simp [mulVec, dotProduct, transpose, Xdelta, ket0, delta0, Fin.sum_univ_two]

theorem Xdelta_transpose_mulVec_ket1 (δ : ℝ) :
    mulVec (transpose (Xdelta δ)) ket1 = delta1 δ := by
  funext i
  fin_cases i <;>
    simp [mulVec, dotProduct, transpose, Xdelta, ket1, delta1, Fin.sum_univ_two]

theorem delta0_orthogonal_delta1 (δ : ℝ) :
    (∑ i : Fin 2, delta0 δ i * delta1 δ i) = 0 := by
  simp [Fin.sum_univ_two, delta0, delta1]
  ring

theorem delta0_norm (δ : ℝ) :
    (∑ i : Fin 2, delta0 δ i * delta0 δ i) = 1 := by
  simp [Fin.sum_univ_two, delta0]
  nlinarith [Real.cos_sq_add_sin_sq δ]

theorem delta1_norm (δ : ℝ) :
    (∑ i : Fin 2, delta1 δ i * delta1 δ i) = 1 := by
  simp [Fin.sum_univ_two, delta1]
  nlinarith [Real.cos_sq_add_sin_sq δ]

theorem Xdelta_conj_rankOne_ket1 (δ : ℝ) :
    transpose (Xdelta δ) * rankOne ket1 * Xdelta δ = rankOne (delta1 δ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rankOne, Xdelta, ket1, delta1, Matrix.mul_apply, Fin.sum_univ_two,
      transpose] <;>
    ring

theorem Zbar_mulVec_ket0 : mulVec Zbar ket0 = fun i => -(ket0 i) := by
  funext i
  fin_cases i <;> simp [Zbar, ket0, mulVec, dotProduct, Fin.sum_univ_two]

theorem Zbar_mulVec_ket1 : mulVec Zbar ket1 = ket1 := by
  funext i
  fin_cases i <;> simp [Zbar, ket1, mulVec, dotProduct, Fin.sum_univ_two]

theorem delta1_inner_ket1 (δ : ℝ) :
    (∑ i : Fin 2, delta1 δ i * ket1 i) = Real.cos δ := by
  simp [Fin.sum_univ_two, delta1, ket1]

theorem delta1_inner_ket0 (δ : ℝ) :
    (∑ i : Fin 2, delta1 δ i * ket0 i) = -Real.sin δ := by
  simp [Fin.sum_univ_two, delta1, ket0]

def uniformCoin : Fin 4 → ℝ := fun _ => 1 / 2

abbrev JointIndex (n : ℕ) : Type := Fin 2 × (Fin 4 × Site n)

def targetState (n : ℕ) (δ : ℝ) (m : Site n) : JointIndex n → ℝ :=
  fun x => delta1 δ x.1 * uniformCoin x.2.1 * (if x.2.2 = m then 1 else 0)

theorem targetState_eq_zero_of_ne (n : ℕ) (δ : ℝ) (m s : Site n) (h : s ≠ m) :
    ∀ b c, targetState n δ m (b, c, s) = 0 := by
  intro b c
  simp only [targetState, if_neg h, mul_zero]

theorem targetState_apply (n : ℕ) (δ : ℝ) (m : Site n) (b : Fin 2) (c : Fin 4) (s : Site n) :
    targetState n δ m (b, c, s) = delta1 δ b * (1 / 2) * (if s = m then 1 else 0) := by
  rfl

end Qatlib.Papers.WalkSpatial08.MainResults
