module

import Qatlib.Papers.QSingValue19.QsVtStability.PolynomialEigenvalueRobustness

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Polynomial
open scoped Matrix.Norms.L2Operator

namespace QatlibTests.QSingValue19PolynomialRobustness

open Qatlib.Papers.QSingValue19.QsVtStability

/-- A concrete two-level diagonal register. -/
def plusMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal fun _ => 1

/-- The opposite diagonal perturbation has operator distance two. -/
def minusMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal fun _ => -1

/-- A concrete non-degenerate consumer for the restricted Theorem 20 bound. -/
example :
    ∃ C : ℝ, 0 < C ∧
      ‖Polynomial.aeval
          (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) plusMatrix)
          (Polynomial.X : ℂ[X])
        - Polynomial.aeval
          (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) minusMatrix)
          (Polynomial.X : ℂ[X])‖
        ≤ C * ‖plusMatrix - minusMatrix‖ ∧
      ‖plusMatrix - minusMatrix‖ = 2 := by
  obtain ⟨C, hC, hbound⟩ :=
    theorem20PolynomialEigenvalueRobustnessMatrix (Fin 2)
      (p := (Polynomial.X : ℂ[X])) (R := 1) le_rfl
  refine ⟨C, hC, hbound plusMatrix minusMatrix ?_ ?_, ?_⟩
  · simp [plusMatrix]
  · simp [minusMatrix]
  · have htwo : plusMatrix - minusMatrix = Matrix.diagonal fun _ => (2 : ℂ) := by
      ext i j
      by_cases h : i = j
      · subst h
        simp [plusMatrix, minusMatrix]
        norm_num
      · simp [h, plusMatrix, minusMatrix]
    rw [htwo, Matrix.l2_opNorm_diagonal]
    simp

end QatlibTests.QSingValue19PolynomialRobustness
