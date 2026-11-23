/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HittingTimes08.MainResults.Rotate
public import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

/-!
# Euclidean and uniform-cost bridges for approximate rotations

The rotation estimate uses a complex Euclidean state space. Each finite unitary matrix acts as
a continuous linear map with L2 operator norm one. The distance bound uses a dimension-independent
constant, and the modeled budget has a single coefficient for all positive threshold parameters
and repetition counts.

These estimates support [MagniezEtAl2008], Theorem 3.9, at the level of an ideal vector mixture
and a per-repetition cost model. The circuit, its Born probabilities, and the choice of repetition
count from the desired precision are outside this model.

## Main statements

* `theorem_3_9_unitary_euclidean_uniform`: one constant controls every positive-dimensional
  unitary Euclidean rotation instance.
* `theorem_3_9_cost_uniform`: one coefficient gives the exact modeled controlled-unitary budget.

## References

* [Magniez et al., 2008][MagniezEtAl2008]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HittingTimes08.MainResults

open Qatlib.Papers.HittingTimes08.MainResults
open Qatlib.Foundations.PureStateMath.BornBridge
open scoped Matrix Matrix.Norms.L2Operator

/-- One absolute constant controls the Euclidean error of every positive-dimensional unitary
rotation instance with a positive repetition count. The unitary matrix acts by its L2 operator
action, and the error bound is for the ideal mixture. -/
theorem theorem_3_9_unitary_euclidean_uniform :
    ∃ C > 0, ∀ d : ℕ, ∀ _hd : 0 < d,
      ∀ U : Matrix (Fin d) (Fin d) ℂ, ∀ _hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ,
      ∀ ψ junk : EuclideanSpace ℂ (Fin d), ∀ _hψ : ‖ψ‖ = 1, ∀ _hjunk : ‖junk‖ = 1,
      ∀ ε : ℝ, ∀ _hε0 : 0 < ε, ∀ _hε1 : ε ≤ 1 / 2, ∀ k : ℕ,
      ∀ _hkpos : 0 < k, ∀ _hk : (1 / 3 : ℝ) ^ k ≤ 2 * ε,
      ‖U‖ = 1 ∧
        ‖rotationMixtureModel ((Matrix.toEuclideanCLM (𝕜 := ℂ)) U ψ) junk
            ((1 / 3 : ℝ) ^ k) -
          ((Matrix.toEuclideanCLM (𝕜 := ℂ)) U ψ)‖ ≤ C * Real.sqrt ε := by
  refine ⟨Real.sqrt 8, by positivity, ?_⟩
  intro d _hd U _hU ψ junk _hψ _hjunk ε _hε0 _hε1 k _hkpos _hk
  let : Nonempty (Fin d) := ⟨⟨0, _hd⟩⟩
  have hnorm : ‖U‖ = 1 := CStarRing.norm_of_mem_unitary _hU
  have hrot : ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)) U ψ‖ = 1 := by
    rw [norm_toEuclideanCLM_of_mem_unitaryGroup _hU, _hψ]
  have hdist := theorem_3_9 _ _ ε k _hε0 _hε1 _hk hrot _hjunk
  refine ⟨hnorm, ?_⟩
  rw [Real.sqrt_mul (x := (8 : ℝ)) (by norm_num : (0 : ℝ) ≤ 8) ε] at hdist
  exact hdist

/-- One coefficient, equal to one, gives the exact modeled controlled-unitary budget for
every positive reciprocal threshold `T` and positive repetition count `k`. -/
theorem theorem_3_9_cost_uniform :
    ∃ C > 0, ∀ T : ℝ, ∀ _hT : 0 < T, ∀ k : ℕ, ∀ _hk : 0 < k,
      PhaseSpectrum.detectCostModel (1 / T) k = C * ((k : ℝ) * (T + 1)) := by
  refine ⟨1, by norm_num, ?_⟩
  intro T _ k _
  simp [PhaseSpectrum.detectCostModel, one_div]

end Qatlib.Papers.HittingTimes08.MainResults
