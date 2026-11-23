module

public import Qatlib.Papers.LowRankMatrix19.MatrixFunctions.PartitionFunction

/-!
# LowRankMatrix19 partition-function consumer

The consumer uses two concrete Hermitian `2 × 2` matrices.  The off-diagonal
Pauli matrix makes the example noncommuting with the diagonal matrix, while the
finite `Fin 2` domain keeps every norm and trace genuinely Euclidean and
computable.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace QatlibTests.LowRankMatrix19PartitionFunctionRegression

open Matrix
open Qatlib.Papers.LowRankMatrix19.MatrixFunctions
open scoped Matrix.Norms.L2Operator

private def h₂ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), 0; 0, 1]

private def k₂ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

private theorem h₂_hermitian : h₂.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h₂, Matrix.conjTranspose, starRingEnd_apply]

private theorem k₂_hermitian : k₂.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [k₂, Matrix.conjTranspose, starRingEnd_apply]

/-- The top-level paper theorem applies to a noncommuting concrete pair. -/
example :
    |(Matrix.trace (NormedSpace.exp k₂)).re -
        (Matrix.trace (NormedSpace.exp h₂)).re| ≤
      Matrix.traceNorm (NormedSpace.exp h₂ - NormedSpace.exp k₂) ∧
    Matrix.traceNorm (NormedSpace.exp h₂ - NormedSpace.exp k₂) ≤
      (Real.exp ‖h₂ - k₂‖ - 1) *
        (Matrix.trace (NormedSpace.exp h₂)).re := by
  exact partition_function_perturbation (Fin 2) h₂ k₂ h₂_hermitian k₂_hermitian

/-- The two input matrices do not commute, so this is not a scalar or diagonal
branch of the perturbation theorem. -/
example : h₂ * k₂ ≠ k₂ * h₂ := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  norm_num [h₂, k₂, Matrix.mul_apply, Fin.sum_univ_two] at h01

end QatlibTests.LowRankMatrix19PartitionFunctionRegression
