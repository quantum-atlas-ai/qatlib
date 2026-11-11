/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Real.Sqrt

/-!
# Effective matrix for element distinctness

The matrix `effectiveMatrix` and two explicit vectors give the algebraic spectral calculation
for the two-dimensional effective model discussed in [Childs2010]. The module verifies the two
eigenvalues and records how eigenpairs behave under scalar multiplication.

## Main statements

* `effectiveMatrix_mulVec_plus` and `effectiveMatrix_mulVec_minus`: explicit eigenpair
  identities.
* `smul_mulVec_eigenvector`: rescaling a matrix rescales its eigenvalue.

## References

* [Childs, 2010][Childs2010]
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

noncomputable section

open Matrix
open scoped Matrix

namespace Qatlib.Papers.ContDiscWalk08.EdBridge

/-- Defines the real matrix with rows `(0, 1)` and `(1, 1 / 2)`. -/
def effectiveMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 1 / 2]

/-- Defines the vector `(1, (1 + √17) / 4)`. -/
def eigenvectorPlus : Fin 2 → ℝ := ![1, (1 + Real.sqrt 17) / 4]

/-- Defines the vector `(1, (1 - √17) / 4)`. -/
def eigenvectorMinus : Fin 2 → ℝ := ![1, (1 - Real.sqrt 17) / 4]

/-- The vector `eigenvectorPlus` satisfies the eigenvector equation for `effectiveMatrix` with
eigenvalue `(1 + √17) / 4`. See the effective spectral model in [Childs2010]. -/
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

/-- The vector `eigenvectorMinus` satisfies the eigenvector equation for `effectiveMatrix` with
eigenvalue `(1 - √17) / 4`. See the effective spectral model in [Childs2010]. -/
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

/-- The positive-branch value `(1 + √17) / 4` solves `2 * x ^ 2 - x - 2 = 0`. -/
theorem eigenvalue_quadratic_plus :
    2 * ((1 + Real.sqrt 17) / 4) ^ 2 - (1 + Real.sqrt 17) / 4 - 2 = 0 := by
  have hs : (Real.sqrt 17) ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  nlinarith

/-- The negative-branch value `(1 - √17) / 4` solves `2 * x ^ 2 - x - 2 = 0`. -/
theorem eigenvalue_quadratic_minus :
    2 * ((1 - Real.sqrt 17) / 4) ^ 2 - (1 - Real.sqrt 17) / 4 - 2 = 0 := by
  have hs : (Real.sqrt 17) ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  nlinarith

/-- If `M *ᵥ v = lam • v`, then scaling `M` by `c` gives the eigenvector equation with scalar `c
* lam`. This supplies a rescaling identity for the effective model in [Childs2010]. -/
theorem smul_mulVec_eigenvector {n : Type*} [Fintype n] (c lam : ℝ)
    (M : Matrix n n ℝ) (v : n → ℝ) (h : M *ᵥ v = lam • v) :
    (c • M) *ᵥ v = (c * lam) • v := by
  rw [Matrix.smul_mulVec, h, smul_smul]

end Qatlib.Papers.ContDiscWalk08.EdBridge
