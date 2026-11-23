module

import Qatlib.Papers.QuantumSVM13.GramDensity.EuclideanBridge

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.QuantumSVM13.GramDensity

noncomputable section

def concreteTrainingRows : Fin 2 → Fin 2 → ℝ := fun i k =>
  if i = 0 ∧ k = 0 then 1 else if i = 1 ∧ k = 1 then 1 else 0

def firstAxis : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1

def secondAxis : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1

example : 0 < (2 : ℕ) := by norm_num

example (i : Fin 2) : 0 < ∑ k, (concreteTrainingRows i k) ^ 2 := by
  fin_cases i <;> norm_num [concreteTrainingRows, Fin.sum_univ_two]

example : ‖gramStateEuclidean concreteTrainingRows‖ = 1 := by
  apply gramState_euclidean_norm concreteTrainingRows (by norm_num)
  intro i
  fin_cases i <;> norm_num [concreteTrainingRows, Fin.sum_univ_two]

example :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2 × Fin 2))
        (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
        (gramStateEuclidean concreteTrainingRows) =
      gramStateEuclidean concreteTrainingRows ∧
      ‖(1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ = 1 := by
  apply gramState_identity_operator_certificate concreteTrainingRows (by norm_num)
  intro i
  fin_cases i <;> norm_num [concreteTrainingRows, Fin.sum_univ_two]

example : ‖firstAxis‖ = 1 := by
  simp [firstAxis]

example : ‖secondAxis‖ = 1 := by
  simp [secondAxis]

example : euclideanMinusBranchWeight firstAxis secondAxis = (1 : ℝ) / 2 := by
  have hinner : ⟪firstAxis, secondAxis⟫_ℝ = 0 := by
    simp [firstAxis, secondAxis, EuclideanSpace.single, PiLp.inner_apply]
  rw [euclidean_swap_test_branch_formula firstAxis secondAxis (by
    simp [firstAxis]) (by
    simp [secondAxis])]
  rw [hinner]
  norm_num
