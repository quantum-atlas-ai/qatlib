module

public import Qatlib.Papers.QSingValue19.QsVtStability.Corollary21PolynomialResponse
public import Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
public import Qatlib.Concepts.CoherentSim.CoherentOAA.OddApproximation

@[expose] public section

/-!
# Consumer checks for the polynomial Corollary 21 increment

The tests instantiate the even, odd, and uniform-constant forms of the
polynomial Corollary 21 bound on a concrete non-degenerate two-level register.
The matrices are diagonal with singular values `1/2` and `1/4`; their operator
distance is `1/4`, so the uniform hypothesis is satisfied with `δ₀ = 1/4`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace QatlibTests.QSingValue19Corollary21

open Matrix Polynomial
open Qatlib.Concepts.QsvtCore.ApproxToolkit
open Qatlib.Concepts.QsvtCore.PhaseExistence
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Papers.QSingValue19.QsVtStability
open scoped Matrix.Norms.L2Operator

/-- The first concrete contraction. -/
def firstMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![(1 / 2 : ℂ), (1 / 4 : ℂ)]

/-- The second concrete contraction. -/
def secondMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![(1 / 2 : ℂ), (0 : ℂ)]

/-- The first matrix has operator norm at most one. -/
theorem firstMatrix_norm_le : ‖firstMatrix‖ ≤ 1 := by
  rw [firstMatrix, Matrix.l2_opNorm_diagonal]
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  fin_cases i <;> norm_num

/-- The second matrix has operator norm at most one. -/
theorem secondMatrix_norm_le : ‖secondMatrix‖ ≤ 1 := by
  rw [secondMatrix, Matrix.l2_opNorm_diagonal]
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  fin_cases i <;> norm_num

/-- The operator distance of the two concrete contractions is `1/4`. -/
theorem firstMatrix_sub_secondMatrix :
    ‖firstMatrix - secondMatrix‖ = 1 / 4 := by
  have hsub : firstMatrix - secondMatrix =
      Matrix.diagonal (fun i : Fin 2 => if i = 0 then (0 : ℂ) else (1 / 4 : ℂ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [firstMatrix, secondMatrix]
  rw [hsub, Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (by norm_num)).mpr ?_
    intro i
    fin_cases i <;> simp
  · have h := norm_le_pi_norm
      (f := fun i : Fin 2 => if i = 0 then (0 : ℂ) else (1 / 4 : ℂ)) (1 : Fin 2)
    simpa using h

/-- The even polynomial `X ^ 2` satisfies the even polynomial bound. -/
example :
    ‖rightSingularTransform firstMatrix (realPolynomialResponse ((X : Polynomial ℝ) ^ 2)) -
        rightSingularTransform secondMatrix (realPolynomialResponse ((X : Polynomial ℝ) ^ 2))‖ ≤
      modulusRobustnessFactor ‖firstMatrix - secondMatrix‖ *
        polynomialResponseModulus ((X : Polynomial ℝ) ^ 2) ‖firstMatrix - secondMatrix‖ := by
  refine corollary21_evenPolynomial firstMatrix secondMatrix ((X : Polynomial ℝ) ^ 2) ?_
    firstMatrix_norm_le secondMatrix_norm_le
  simp

/-- The odd polynomial `X ^ 3` satisfies the odd polynomial bound. -/
example :
    ‖oddSingularTransform firstMatrix (realPolynomialResponse ((X : Polynomial ℝ) ^ 3)) -
        oddSingularTransform secondMatrix (realPolynomialResponse ((X : Polynomial ℝ) ^ 3))‖ ≤
      modulusRobustnessFactor ‖firstMatrix - secondMatrix‖ *
        polynomialResponseModulus ((X : Polynomial ℝ) ^ 3) ‖firstMatrix - secondMatrix‖ := by
  refine corollary21_oddPolynomial firstMatrix secondMatrix ((X : Polynomial ℝ) ^ 3) ?_
    firstMatrix_norm_le secondMatrix_norm_le
  simp
  ring

/-- The uniform-constant form is applicable at distance `δ₀ = 1/4`. -/
example :
    ∃ C : ℝ, 0 < C ∧
      ‖rightSingularTransform firstMatrix (realPolynomialResponse ((X : Polynomial ℝ) ^ 2)) -
          rightSingularTransform secondMatrix (realPolynomialResponse ((X : Polynomial ℝ) ^ 2))‖ ≤
        C * ‖firstMatrix - secondMatrix‖ := by
  obtain ⟨C, hC, hbound⟩ :=
    corollary21_evenPolynomial_uniform ((X : Polynomial ℝ) ^ 2) (δ₀ := 1 / 4) (by norm_num)
  refine ⟨C, hC, hbound firstMatrix secondMatrix ?_ firstMatrix_norm_le
    secondMatrix_norm_le ?_⟩
  · simp
  · rw [firstMatrix_sub_secondMatrix]

/-- The packaged even/odd dichotomy exposes both bounds. -/
example :
    (((X : Polynomial ℝ) ^ 2).comp (-Polynomial.X) = (X : Polynomial ℝ) ^ 2 →
      ‖rightSingularTransform firstMatrix
          (realPolynomialResponse ((X : Polynomial ℝ) ^ 2)) -
          rightSingularTransform secondMatrix
            (realPolynomialResponse ((X : Polynomial ℝ) ^ 2))‖ ≤
        modulusRobustnessFactor ‖firstMatrix - secondMatrix‖ *
          polynomialResponseModulus ((X : Polynomial ℝ) ^ 2) ‖firstMatrix - secondMatrix‖) ∧
    (((X : Polynomial ℝ) ^ 2).comp (-Polynomial.X) = -((X : Polynomial ℝ) ^ 2) →
      ‖oddSingularTransform firstMatrix
          (realPolynomialResponse ((X : Polynomial ℝ) ^ 2)) -
          oddSingularTransform secondMatrix
            (realPolynomialResponse ((X : Polynomial ℝ) ^ 2))‖ ≤
        modulusRobustnessFactor ‖firstMatrix - secondMatrix‖ *
          polynomialResponseModulus ((X : Polynomial ℝ) ^ 2) ‖firstMatrix - secondMatrix‖) :=
  corollary21_polynomialResponse firstMatrix secondMatrix ((X : Polynomial ℝ) ^ 2)
    (Or.inl (by simp)) firstMatrix_norm_le secondMatrix_norm_le

end QatlibTests.QSingValue19Corollary21
