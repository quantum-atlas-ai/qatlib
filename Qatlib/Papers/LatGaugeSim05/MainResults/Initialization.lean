/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open Matrix
open Real

namespace Qatlib.Papers.LatGaugeSim05.MainResults

def u5Rot (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos φ, -Real.sin φ; Real.sin φ, Real.cos φ]

theorem u5Rot_orthogonal (φ : ℝ) : (u5Rot φ)ᵀ * u5Rot φ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u5Rot, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
      Matrix.one_apply] <;>
    nlinarith [Real.cos_sq_add_sin_sq φ, Real.sin_sq_add_cos_sq φ]

theorem u5Rot_orthogonal' (φ : ℝ) : u5Rot φ * (u5Rot φ)ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u5Rot, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
      Matrix.one_apply] <;>
    nlinarith [Real.cos_sq_add_sin_sq φ, Real.sin_sq_add_cos_sq φ]

def u5ApplyCount (M d c : ℕ) : ℕ := c * (d * M)

def u5LocalOpCount (M d c : ℕ) : ℕ := c * (M * d)

def u5WorstOpCount (M d D : ℕ) : ℕ := D * d ^ 2 * M ^ 2

theorem u5_apply_count_eq (M d c : ℕ) : u5ApplyCount M d c = c * d * M := by
  simp only [u5ApplyCount]; ring

theorem u5_local_op_count_linear (d c : ℕ) (M : ℕ) :
    u5LocalOpCount (M + 1) d c = u5LocalOpCount M d c + c * d := by
  simp only [u5LocalOpCount]; ring

theorem u5_worst_is_plaquette_times_qubits (M d D : ℕ) :
    u5WorstOpCount M d D = (d * M) * (D * d * M) := by
  simp only [u5WorstOpCount]; ring

theorem u5_worst_op_count_quadratic (M d D : ℕ) :
    u5WorstOpCount M d D = D * d ^ 2 * M ^ 2 := by
  simp only [u5WorstOpCount]

end Qatlib.Papers.LatGaugeSim05.MainResults
