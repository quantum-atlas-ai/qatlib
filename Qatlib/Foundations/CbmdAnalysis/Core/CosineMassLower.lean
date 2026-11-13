/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.CosineParameters

/-!
# Lower bounds for finite cosine weight mass

This module relates `cosineFiniteWeightMass` to the norm of the finite cosine approximation.
Bounded baseline and sample values give an upper bound on the approximation norm, while an
approximation to a target of norm at least `η` forces the weight mass to be at least `η / 2`.
These estimates support normalization analysis for [WangEtAl2026].

## Main statements

* `cosineFiniteWeightMass_pos`: positive parameters give strictly positive finite weight mass.
* `cosineApproximation_norm_le_mass`: bounds the approximation norm by the weight mass.
* `cosineFiniteWeightMass_ge_half_of_error`: a sufficiently accurate approximation forces a
  lower bound on the mass.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
noncomputable section
namespace CBMD
open Complex
open scoped BigOperators

/-- For positive `γ` and `τ`, the finite cosine weight mass is strictly positive for every
retained count. -/
theorem cosineFiniteWeightMass_pos {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ) (N : ℕ) :
    0 < cosineFiniteWeightMass γ τ N := by
  unfold cosineFiniteWeightMass
  apply mul_pos (norm_pos_iff.mpr (cosineRegulator_one_ne_zero hγ hτ))
  have h : 0 ≤ ∑ k ∈ Finset.range N, ‖cosineSampleCoefficient γ τ k‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  linarith

section Banach
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- If the baseline and all sample values have norm at most one, the finite cosine approximation
has norm at most its finite weight mass. -/
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

/-- If the baseline and samples have norm at most one, the target norm is at least `η > 0`, and
the approximation error is at most `ε * η / 8` with `ε ≤ 1`, then `η ≤ 2 *
cosineFiniteWeightMass γ τ N`. -/
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
