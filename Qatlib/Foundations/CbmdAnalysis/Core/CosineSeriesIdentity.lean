/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.CosineCircleLimit
import Qatlib.Foundations.CbmdAnalysis.Core.CosineWeightBounds

/-!
# Infinite cosine sampling identities

This module derives an infinite cosine sampling formula from the finite circle identities and
vanishing contour integrals. Complex differentiability, bounded sample values, and an eventual
numerator-to-regulator comparison yield reconstruction of `U 1` and a quantitative finite-sum
error. This is the analytic sampling step underlying [WangEtAl2026].

## Main statements

* `cosine_kernel_series_identity`: reconstructs `U 1` from the baseline and infinite weighted
  sample series.
* `cosineLCU_target_error_le`: bounds the error after retaining samples through index `K`.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace CBMD
open Complex Metric Set Filter
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- For positive parameters, a complex differentiable numerator with sample norms at most one
and an eventual fixed nonnegative circle comparison satisfies `U 1 = cosineRegulator γ τ 1 •
U 0 - cosineRegulator γ τ 1 • ∑' k, cosineSample γ τ U k` [WangEtAl2026]. -/
theorem cosine_kernel_series_identity {γ τ C : ℝ} (hγ : 0 < γ) (hτ : 0 < τ)
    (hC : 0 ≤ C) (U : ℂ → E) (hUanalytic : Differentiable ℂ U)
    (hUsample : ∀ k, ‖U (cosineSamplePole γ τ k)‖ ≤ 1)
    (hUcircle : ∀ᶠ n : ℕ in atTop, ∀ z ∈ sphere 0 (cosineCircleRadius γ τ n),
      ‖U z‖ ≤ C * ‖cosineRegulator γ τ z‖) :
    U 1 = cosineRegulator γ τ 1 • U 0 -
      cosineRegulator γ τ 1 • (∑' k : ℕ, cosineSample γ τ U k) := by
  have hsn := cosineSample_norm_summable hγ hτ U hUsample
  have hsum : Tendsto (fun n => cosineLCUSum γ τ n U) atTop
      (𝓝 (∑' k : ℕ, cosineSample γ τ U k)) := hsn.of_norm.hasSum.tendsto_sum_nat
  have hc := cosineContour_circle_tendsto_zero hγ hτ hC U hUcircle
  have he : (fun n : ℕ => (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      ∮ z in C(0, cosineCircleRadius γ τ n), cosineContourIntegrand γ τ U z) =ᶠ[atTop]
      (fun n => U 1 - cosineRegulator γ τ 1 • U 0 +
        cosineRegulator γ τ 1 • cosineLCUSum γ τ n U) := by
    filter_upwards [(cosineCircleRadius_tendsto hγ hτ).eventually_gt_atTop 1] with n hn
    exact cosineContour_circle_identity_normalized hγ hτ n hn U hUanalytic
  have hr := (tendsto_const_nhds (x := U 1 - cosineRegulator γ τ 1 • U 0)).add
    (hsum.const_smul (cosineRegulator γ τ 1))
  have hz : U 1 - cosineRegulator γ τ 1 • U 0 +
      cosineRegulator γ τ 1 • (∑' k : ℕ, cosineSample γ τ U k) = 0 :=
    tendsto_nhds_unique hr (hc.congr' he)
  calc
    U 1 = (U 1 - cosineRegulator γ τ 1 • U 0 +
        cosineRegulator γ τ 1 • (∑' k : ℕ, cosineSample γ τ U k)) +
        cosineRegulator γ τ 1 • U 0 -
        cosineRegulator γ τ 1 • (∑' k : ℕ, cosineSample γ τ U k) := by abel
    _ = _ := by rw [hz, zero_add]

/-- Under the analytic sampling and circle comparison hypotheses with positive parameters,
retaining samples through index `K` gives target error at most `‖cosineRegulator γ τ 1‖ * γ
* τ ^ 2 / (π ^ 3 * (K + 1 / 2) ^ 2)`. -/
theorem cosineLCU_target_error_le {γ τ C : ℝ} (hγ : 0 < γ) (hτ : 0 < τ)
    (hC : 0 ≤ C) (U : ℂ → E) (hUanalytic : Differentiable ℂ U)
    (hUsample : ∀ k, ‖U (cosineSamplePole γ τ k)‖ ≤ 1)
    (hUcircle : ∀ᶠ n : ℕ in atTop, ∀ z ∈ sphere 0 (cosineCircleRadius γ τ n),
      ‖U z‖ ≤ C * ‖cosineRegulator γ τ z‖) (K : ℕ) :
    ‖U 1 - (cosineRegulator γ τ 1 • U 0 -
      cosineRegulator γ τ 1 • cosineLCUSum γ τ (K + 1) U)‖ ≤
      ‖cosineRegulator γ τ 1‖ * γ * τ ^ 2 /
        (Real.pi ^ 3 * ((K : ℝ) + 1 / 2) ^ 2) := by
  have hid := cosine_kernel_series_identity hγ hτ hC U hUanalytic hUsample hUcircle
  have hsum := (cosineSample_summable hγ hτ U hUsample).sum_add_tsum_nat_add (K + 1)
  have htail : U 1 - (cosineRegulator γ τ 1 • U 0 -
      cosineRegulator γ τ 1 • cosineLCUSum γ τ (K + 1) U) =
      -(cosineRegulator γ τ 1 • ∑' j : ℕ, cosineSample γ τ U (K + 1 + j)) := by
    rw [hid, ← hsum, smul_add]
    simp only [cosineLCUSum, Nat.add_comm _ (K + 1)]
    abel
  rw [htail, norm_neg]
  exact cosineSample_weighted_tail_norm_le hγ hτ U hUsample K

end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
