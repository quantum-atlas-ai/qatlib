module

public import Qatlib.Papers.HittingTimes08.MainResults.RotationEuclidean

@[expose] public section

/-!
# Concrete Euclidean consumer for the HittingTimes08 rotation bridge

The Pauli-X matrix acts on the first basis vector in a two-dimensional complex Euclidean space.
The residual vector is the first basis vector, and the ideal output is the second. The same two
repetitions are used in the rotation error bound and in the controlled-unitary cost model.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace QatlibTests.HittingTimes08RotationEuclidean

open Qatlib.Papers.HittingTimes08.MainResults
open Qatlib.Papers.HittingTimes08.MainResults
open scoped Matrix Matrix.Norms.L2Operator

private def flip : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli-X is unitary. -/
private theorem flip_unitary : flip ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [flip, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, Matrix.one_apply]

private def inputState : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 ![(1 : ℂ), 0]

/-- The first basis vector has Euclidean norm one. -/
private theorem inputState_norm : ‖inputState‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [inputState, Fin.sum_univ_two]

/-- Two repetitions meet the error tolerance `1/8` and incur the modeled budget at `T = 1`. -/
example : ∃ C > 0, ∃ K > 0,
    ‖flip‖ = 1 ∧
      ‖rotationMixtureModel ((Matrix.toEuclideanCLM (𝕜 := ℂ)) flip inputState) inputState
          ((1 / 3 : ℝ) ^ 2) - ((Matrix.toEuclideanCLM (𝕜 := ℂ)) flip inputState)‖ ≤
        C * Real.sqrt (1 / 8) ∧
      PhaseSpectrum.detectCostModel (1 / 1) 2 = K * ((2 : ℝ) * (1 + 1)) := by
  obtain ⟨C, hC, hdist⟩ := theorem_3_9_unitary_euclidean_uniform
  obtain ⟨K, hK, hcost⟩ := theorem_3_9_cost_uniform
  have hresult := hdist 2 (by norm_num) flip flip_unitary inputState inputState
    inputState_norm inputState_norm (1 / 8) (by norm_num) (by norm_num) 2 (by norm_num) (by norm_num)
  exact ⟨C, hC, K, hK, hresult.1, hresult.2, hcost 1 (by norm_num) 2 (by norm_num)⟩

end QatlibTests.HittingTimes08RotationEuclidean
