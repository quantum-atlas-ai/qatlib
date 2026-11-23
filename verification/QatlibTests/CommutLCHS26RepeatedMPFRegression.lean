module

import Qatlib.Papers.CommutLCHS26.MainResults.RepeatedMPF

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace QatlibTests.CommutLCHS26RepeatedMPFRegression

open Qatlib.Papers.CommutLCHS26.MainResults

/-- A two-dimensional diagonal example exercises the repeated operator bound
with a nonzero local error. -/
example :
    ‖(Matrix.diagonal (fun _ : Fin 2 => (1 : ℂ))) ^ 4 -
        (Matrix.diagonal (fun i : Fin 2 => if i = 0 then (1 : ℂ) else 7 / 8)) ^ 4‖
      ≤ Real.exp 1 * (1 / 2) := by
  have hU : ‖Matrix.diagonal (fun _ : Fin 2 => (1 : ℂ))‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_diagonal]
    norm_num
  have herr :
      ‖Matrix.diagonal (fun _ : Fin 2 => (1 : ℂ)) -
          Matrix.diagonal (fun i : Fin 2 => if i = 0 then (1 : ℂ) else 7 / 8)‖
        ≤ (1 : ℝ) / 2 / 4 := by
    rw [Matrix.diagonal_sub, Matrix.l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun i => ?_
    fin_cases i <;> simp <;> norm_num
  exact repeated_mpf_error_le_exp _ _ (by norm_num) (by norm_num) (by norm_num) hU herr

/-- The same non-degenerate instance acts on a concrete Euclidean state space. -/
example (x : EuclideanSpace ℂ (Fin 2)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2)
        ((Matrix.diagonal (fun _ : Fin 2 => (1 : ℂ))) ^ 4 -
          (Matrix.diagonal (fun i : Fin 2 => if i = 0 then (1 : ℂ) else 7 / 8)) ^ 4) x‖
      ≤ Real.exp 1 * (1 / 2) * ‖x‖ := by
  have hU : ‖Matrix.diagonal (fun _ : Fin 2 => (1 : ℂ))‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_diagonal]
    norm_num
  have herr :
      ‖Matrix.diagonal (fun _ : Fin 2 => (1 : ℂ)) -
          Matrix.diagonal (fun i : Fin 2 => if i = 0 then (1 : ℂ) else 7 / 8)‖
        ≤ (1 : ℝ) / 2 / 4 := by
    rw [Matrix.diagonal_sub, Matrix.l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun i => ?_
    fin_cases i <;> simp <;> norm_num
  exact repeated_mpf_vector_error_le_exp _ _ (by norm_num) (by norm_num) (by norm_num)
    hU herr x

end QatlibTests.CommutLCHS26RepeatedMPFRegression
