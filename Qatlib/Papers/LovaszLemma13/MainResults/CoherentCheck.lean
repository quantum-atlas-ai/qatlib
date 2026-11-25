/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LovaszLemma13.MainResults.CommutingFixInvariant
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# Unitarity of one coherent projector check

The check in Eq. (2) flips the log qubit in one projector sector
and is the identity on the complementary sector.
-/

set_option autoImplicit false

namespace Qatlib.Papers.LovaszLemma13.MainResults

open Matrix Qatlib.Papers.LovaszLemma13.MainResults
open scoped Kronecker Matrix

/-- The matrix of the one-step coherent check is unitary for any Hermitian projector. -/
theorem check_unitary {ν : Type*} [Fintype ν] [DecidableEq ν]
    (P : Matrix ν ν ℂ) (hP : P.IsHermitian) (hPP : P * P = P) :
    let C := P ⊗ₖ (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) +
      (1 - P) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
    Cᴴ * C = 1 ∧ C * Cᴴ = 1 := by
  let X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
  let C := P ⊗ₖ X + (1 - P) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
  change Cᴴ * C = 1 ∧ C * Cᴴ = 1
  have hXadj : Xᴴ = X := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [X, conjTranspose_apply]
  have hXX : X * X = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [X, Matrix.mul_apply, Fin.sum_univ_two]
  have hPQ := projector_mul_compl P hPP
  have hQP : (1 - P) * P = 0 := (commute_compl (rfl : P * P = P * P)).symm.trans hPQ
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, hPQ, sub_zero]
  have hsum : P + (1 - P) = 1 := by abel
  have hC : Cᴴ = C := by
    simp only [C, conjTranspose_add, conjTranspose_kronecker, conjTranspose_sub, hP.eq,
      hXadj, conjTranspose_one]
  have hCC : C * C = 1 := by
    simp only [C, Matrix.add_mul, Matrix.mul_add, ← mul_kronecker_mul, hPP, hPQ, hQP, hQQ,
      hXX, Matrix.mul_one, Matrix.one_mul, zero_kronecker, add_zero, zero_add,
      ← add_kronecker, hsum, one_kronecker_one]
  simpa only [hC] using And.intro hCC hCC

end Qatlib.Papers.LovaszLemma13.MainResults
