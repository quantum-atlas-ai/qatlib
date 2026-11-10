/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Real.Sqrt

set_option autoImplicit false
set_option linter.unusedSimpArgs false

noncomputable section

open Matrix
open scoped Matrix

namespace Qatlib.Papers.ContDiscWalk08.EdBridge

def effectiveMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 1 / 2]

def eigenvectorPlus : Fin 2 → ℝ := ![1, (1 + Real.sqrt 17) / 4]

def eigenvectorMinus : Fin 2 → ℝ := ![1, (1 - Real.sqrt 17) / 4]

theorem effectiveMatrix_mulVec_plus :
    effectiveMatrix *ᵥ eigenvectorPlus = ((1 + Real.sqrt 17) / 4) • eigenvectorPlus := by
  have hs : (Real.sqrt 17) ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  ext i
  fin_cases i
  · simp [effectiveMatrix, eigenvectorPlus, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
  · simp [effectiveMatrix, eigenvectorPlus, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
    nlinarith

theorem effectiveMatrix_mulVec_minus :
    effectiveMatrix *ᵥ eigenvectorMinus = ((1 - Real.sqrt 17) / 4) • eigenvectorMinus := by
  have hs : (Real.sqrt 17) ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  ext i
  fin_cases i
  · simp [effectiveMatrix, eigenvectorMinus, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
  · simp [effectiveMatrix, eigenvectorMinus, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
    nlinarith

theorem eigenvalue_quadratic_plus :
    2 * ((1 + Real.sqrt 17) / 4) ^ 2 - (1 + Real.sqrt 17) / 4 - 2 = 0 := by
  have hs : (Real.sqrt 17) ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  nlinarith

theorem eigenvalue_quadratic_minus :
    2 * ((1 - Real.sqrt 17) / 4) ^ 2 - (1 - Real.sqrt 17) / 4 - 2 = 0 := by
  have hs : (Real.sqrt 17) ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  nlinarith

theorem smul_mulVec_eigenvector {n : Type*} [Fintype n] (c lam : ℝ)
    (M : Matrix n n ℝ) (v : n → ℝ) (h : M *ᵥ v = lam • v) :
    (c • M) *ᵥ v = (c * lam) • v := by
  rw [Matrix.smul_mulVec, h, smul_smul]

end Qatlib.Papers.ContDiscWalk08.EdBridge
