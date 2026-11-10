/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.CosineParameters
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
noncomputable section
namespace CBMD
open Complex
open scoped BigOperators

theorem cosineFiniteWeightMass_pos {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ) (N : ℕ) :
    0 < cosineFiniteWeightMass γ τ N := by
  unfold cosineFiniteWeightMass
  apply mul_pos (norm_pos_iff.mpr (cosineRegulator_one_ne_zero hγ hτ))
  have h : 0 ≤ ∑ k ∈ Finset.range N, ‖cosineSampleCoefficient γ τ k‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  linarith

section Banach
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem cosineApproximation_norm_le_mass (γ τ : ℝ) (N : ℕ) (U : ℂ → E)
    (hUzero : ‖U 0‖ ≤ 1) (hUsample : ∀ k, ‖U (cosineSamplePole γ τ k)‖ ≤ 1) :
    ‖cosineApproximation γ τ N U‖ ≤ cosineFiniteWeightMass γ τ N := by
  have hsum : ‖cosineLCUSum γ τ N U‖ ≤ ∑ k ∈ Finset.range N, ‖cosineSampleCoefficient γ τ k‖ := by
    apply (norm_sum_le (Finset.range N) _).trans
    apply Finset.sum_le_sum
    intro k _
    rw [cosineSample, norm_smul]
    simpa only [mul_one] using! mul_le_mul_of_nonneg_left (hUsample k) (norm_nonneg _)
  unfold cosineApproximation
  apply (norm_sub_le _ _).trans
  rw [norm_smul, norm_smul]
  have h0 := mul_le_mul_of_nonneg_left hUzero (norm_nonneg (cosineRegulator γ τ 1))
  have h1 := mul_le_mul_of_nonneg_left hsum (norm_nonneg (cosineRegulator γ τ 1))
  unfold cosineFiniteWeightMass
  nlinarith

theorem cosineFiniteWeightMass_ge_half_of_error {γ τ ε η : ℝ}
    (hε : ε ≤ 1) (hη : 0 < η) (N : ℕ) (U : ℂ → E)
    (hUzero : ‖U 0‖ ≤ 1) (hUsample : ∀ k, ‖U (cosineSamplePole γ τ k)‖ ≤ 1)
    (hηU : η ≤ ‖U 1‖)
    (herr : ‖U 1 - cosineApproximation γ τ N U‖ ≤ ε * η / 8) :
    η ≤ 2 * cosineFiniteWeightMass γ τ N := by
  have hm := cosineApproximation_norm_le_mass γ τ N U hUzero hUsample
  have hh : ‖U 1‖ ≤ ‖U 1 - cosineApproximation γ τ N U‖ + ‖cosineApproximation γ τ N U‖ := by
    calc
      _ = ‖(U 1 - cosineApproximation γ τ N U) + cosineApproximation γ τ N U‖ := by simp
      _ ≤ _ := norm_add_le _ _
  nlinarith

end Banach
end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
