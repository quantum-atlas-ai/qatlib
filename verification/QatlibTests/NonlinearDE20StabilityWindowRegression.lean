module

public import Qatlib.Papers.NonlinearDE20.ErrorAnalysis.StabilityWindow

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open scoped Matrix.Norms.L2Operator

namespace QatlibTests.NonlinearDE20StabilityWindowRegression

open Qatlib.Papers.NonlinearDE20.ErrorAnalysis.Stability

/-- A concrete two-dimensional forward-Euler propagator with diagonal entries `1/2` and `1/3`. -/
def stableEulerStepMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal ![1 / 2, 1 / 3]

/-- The true `L2` operator norm of the concrete stable propagator is at most `1/2`. -/
theorem stableEulerStepMatrix_opNorm_le_one_half :
    ‖(Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
        stableEulerStepMatrix)‖ ≤ 1 / 2 := by
  rw [stableEulerStepMatrix, Matrix.l2_opNorm_toEuclideanCLM,
    Matrix.l2_opNorm_diagonal]
  have hcoords : ∀ i, ‖(![1 / 2, 1 / 3] : Fin 2 → ℝ) i‖ ≤ 1 / 2 := by
    intro i
    fin_cases i <;> norm_num [Real.norm_eq_abs]
  exact (pi_norm_le_iff_of_nonneg (by norm_num)).mpr hcoords

/-- Two distinct concrete states on the nonzero Euclidean plane. -/
def stableInput : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, 0]

/-- Another distinct concrete state on the same plane. -/
def stableTarget : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![0, 1]

/-- The concrete stable input is nonzero. -/
theorem stableInput_ne_zero : stableInput ≠ 0 := by
  intro h
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => ‖v‖) h
  have hunit : ‖stableInput‖ = 1 := by
    simp [stableInput, EuclideanSpace.norm_eq, Real.norm_eq_abs]
  rw [hunit] at h0
  simp at h0

/-- The uniform stability theorem on the concrete two-dimensional plane, after five steps of the
diagonal propagator with entries `1/2` and `1/3`. -/
theorem concrete_stability_five_steps :
    ∃ C : ℝ, 0 < C ∧
      ‖stepOrbit
          (fun _ => (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
            stableEulerStepMatrix)) 5 stableInput -
        stepOrbit
          (fun _ => (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
            stableEulerStepMatrix)) 5 stableTarget‖ ≤
          C * (1 / 2) ^ 5 * ‖stableInput - stableTarget‖ := by
  obtain ⟨C, hC0, hstable⟩ := contractive_linear_euler_stability
  have h := hstable 2 (by norm_num) (1 / 2) (by norm_num) (by norm_num)
    (fun _ => (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
      stableEulerStepMatrix))
    (fun _ => stableEulerStepMatrix_opNorm_le_one_half) stableInput stableTarget 5
  exact ⟨C, hC0, h⟩

/-- The negative-trace generator has an expanding matrix action and a growing Euler orbit. -/
theorem concrete_negative_trace_expansion :
    negativeTraceExpandingMatrix.trace < 0 ∧ 2 < ‖negativeTraceExpandingMatrix‖ ∧
      ∃ v : EuclideanSpace ℝ (Fin 2), ‖v‖ = 1 ∧
        ‖stepOrbit
          (fun _ => Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
            (1 + negativeTraceExpandingMatrix)) 5 v‖ = 243 := by
  obtain ⟨htrace, v, hv, horbit⟩ := negative_trace_euler_orbit_expands
  refine ⟨htrace, negative_trace_expansion_counterexample.2.1, v, hv, ?_⟩
  rw [horbit]
  norm_num

end QatlibTests.NonlinearDE20StabilityWindowRegression
