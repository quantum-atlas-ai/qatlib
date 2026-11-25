/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.PhaseEst07.MainResults.FidelityAppendix
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-!
# Inverse-square rate for the sine-state fidelity cost

Appendix B gives the attained fidelity cost in Eq. (B10). Its inverse-square
bound follows uniformly for positive chain lengths.
-/

set_option autoImplicit false

namespace Qatlib.Papers.PhaseEst07.MainResults

open Qatlib.Papers.PhaseEst07.MainResults.FidelityAppendix
open Qatlib.Papers.PhaseEst07.MainResults.VarianceState
open scoped Asymptotics

/-- The squared sine in Eq. (B10) is bounded by `(π/2)² / N²` for positive `N`. -/
theorem fidelity_le (N : ℕ) (hN : 1 ≤ N) :
    Real.sin (Real.pi / (2 * ((N + 2 : ℕ) : ℝ))) ^ 2 ≤
      (Real.pi / 2) ^ 2 / (N : ℝ) ^ 2 := by
  have hpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hden : (N : ℝ) ≤ ((N + 2 : ℕ) : ℝ) := by exact_mod_cast (show N ≤ N + 2 by omega)
  have hangle : Real.pi / (2 * ((N + 2 : ℕ) : ℝ)) ≤ Real.pi / (2 * (N : ℝ)) :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) (by linarith)
  have hsquare :
      (Real.pi / (2 * ((N + 2 : ℕ) : ℝ))) ^ 2 ≤ (Real.pi / (2 * (N : ℝ))) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hangle
  calc
    _ ≤ (Real.pi / (2 * ((N + 2 : ℕ) : ℝ))) ^ 2 := Real.sin_sq_le_sq
    _ ≤ (Real.pi / (2 * (N : ℝ))) ^ 2 := hsquare
    _ = (Real.pi / 2) ^ 2 / (N : ℝ) ^ 2 := by rw [← div_pow, div_div]

/-- The closed form of the sine-state cost is big-O of the inverse square. -/
theorem fidelity_bigO :
    (fun N : ℕ => Real.sin (Real.pi / (2 * ((N + 2 : ℕ) : ℝ))) ^ 2)
      =O[Filter.atTop] (fun N : ℕ => 1 / (N : ℝ) ^ 2) := by
  refine Asymptotics.isBigO_iff.mpr ⟨(Real.pi / 2) ^ 2, Filter.eventually_atTop.2 ⟨1, ?_⟩⟩
  intro N hN
  rw [Real.norm_of_nonneg (sq_nonneg _),
    Real.norm_of_nonneg (by positivity : 0 ≤ 1 / (N : ℝ) ^ 2)]
  simpa only [div_eq_mul_inv, one_mul] using fidelity_le N hN

/-- The attained fidelity objective in the path model obeys the same inverse-square bound. -/
theorem attained_le (N : ℕ) (hN : 1 ≤ N) :
    (1 - sourceFidelityObjective N (sourceVarianceVector (N + 1)) (fun _ => 0)) / 2
      ≤ (Real.pi / 2) ^ 2 / (N : ℝ) ^ 2 := by
  rw [source_fidelity_cost_attained N hN]
  exact fidelity_le N hN

end Qatlib.Papers.PhaseEst07.MainResults
