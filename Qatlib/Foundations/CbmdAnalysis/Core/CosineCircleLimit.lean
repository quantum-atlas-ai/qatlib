/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.CosineFiniteCircle
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.AtTopBot.Ring

/-!
# Vanishing cosine contour integrals

This module proves that the cosine contour radii diverge and that the regulator is nonzero on
each corresponding sphere. If a numerator is eventually bounded there by a fixed multiple of the
regulator norm, the normalized contour integrals tend to zero. This supplies the limiting step
for the cosine sampling representation in [WangEtAl2026].

## Main statements

* `cosineCircleRadius_tendsto`: the radii tend to infinity for positive parameters.
* `cosineContourIntegrand_circle_le`: a rational bound for the integrand on a circle of radius
  greater than one.
* `cosineContour_circle_tendsto_zero`: the normalized integrals vanish under the eventual
  comparison hypothesis.

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

/-- For positive `γ` and `τ`, the cosine contour radii tend to infinity. -/
theorem cosineCircleRadius_tendsto {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ) :
    Tendsto (cosineCircleRadius γ τ) atTop atTop := by
  exact ((tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const Real.pi_pos)).atTop_div_const
      (mul_pos hγ (sq_pos_of_pos hτ))

/-- For positive `γ` and `τ`, the cosine regulator is nonzero on every sphere with radius
`cosineCircleRadius γ τ n`. -/
theorem cosineRegulator_sphere_ne_zero {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ)
    (n : ℕ) (z : ℂ) (hz : z ∈ sphere 0 (cosineCircleRadius γ τ n)) :
    cosineRegulator γ τ z ≠ 0 := by
  intro hzero
  obtain ⟨k, rfl⟩ := (cosineRegulator_eq_zero_iff hγ hτ z).mp hzero
  have hk := (cosineSamplePole_mem_closedBall hγ hτ k n).mp (sphere_subset_closedBall hz)
  have hb := (cosineSamplePole_mem_ball hγ hτ k n).mpr hk
  have he : ‖cosineSamplePole γ τ k‖ = cosineCircleRadius γ τ n := by
    simpa only [mem_sphere_iff_norm, sub_zero] using hz
  have hl : ‖cosineSamplePole γ τ k‖ < cosineCircleRadius γ τ n := by
    simpa only [mem_ball_zero_iff] using hb
  linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- If `‖U z‖ ≤ C * ‖cosineRegulator γ τ z‖` on a cosine circle of radius greater than one with
positive parameters and `C ≥ 0`, the integrand norm is at most `‖cosineRegulator γ τ 1‖ * C
/ (R * (R - 1))` there. -/
theorem cosineContourIntegrand_circle_le {γ τ C : ℝ} (hγ : 0 < γ) (hτ : 0 < τ)
    (hC : 0 ≤ C) (U : ℂ → E) (n : ℕ) (hR : 1 < cosineCircleRadius γ τ n)
    (hU : ∀ z ∈ sphere 0 (cosineCircleRadius γ τ n),
      ‖U z‖ ≤ C * ‖cosineRegulator γ τ z‖)
    (z : ℂ) (hz : z ∈ sphere 0 (cosineCircleRadius γ τ n)) :
    ‖cosineContourIntegrand γ τ U z‖ ≤
      ‖cosineRegulator γ τ 1‖ * C /
        (cosineCircleRadius γ τ n * (cosineCircleRadius γ τ n - 1)) := by
  have hzn : ‖z‖ = cosineCircleRadius γ τ n := by
    simpa only [mem_sphere_iff_norm, sub_zero] using hz
  have hd : cosineCircleRadius γ τ n - 1 ≤ ‖z - 1‖ := by
    simpa only [hzn, norm_one] using norm_sub_norm_le z (1 : ℂ)
  have hreg : 0 < ‖cosineRegulator γ τ z‖ :=
    norm_pos_iff.mpr (cosineRegulator_sphere_ne_zero hγ hτ n z hz)
  have hratio : ‖U z‖ / ‖cosineRegulator γ τ z‖ ≤ C :=
    (div_le_iff₀ hreg).mpr (hU z hz)
  rw [cosineContourIntegrand, norm_smul, norm_div, cosineContourDenominator,
    norm_mul, norm_mul, hzn]
  calc
    _ = (‖cosineRegulator γ τ 1‖ / (cosineCircleRadius γ τ n * ‖z - 1‖)) *
        (‖U z‖ / ‖cosineRegulator γ τ z‖) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ (‖cosineRegulator γ τ 1‖ / (cosineCircleRadius γ τ n * ‖z - 1‖)) * C :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ ≤ (‖cosineRegulator γ τ 1‖ /
        (cosineCircleRadius γ τ n * (cosineCircleRadius γ τ n - 1))) * C := by
      apply mul_le_mul_of_nonneg_right _ hC
      apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left hd (by linarith)
    _ = _ := by ring

/-- For positive parameters, an eventual bound of the numerator norm by a fixed nonnegative
multiple of the regulator norm on cosine circles implies that the normalized contour
integrals tend to zero. -/
theorem cosineContour_circle_tendsto_zero {γ τ C : ℝ} (hγ : 0 < γ) (hτ : 0 < τ)
    (hC : 0 ≤ C) (U : ℂ → E)
    (hU : ∀ᶠ n : ℕ in atTop, ∀ z ∈ sphere 0 (cosineCircleRadius γ τ n),
      ‖U z‖ ≤ C * ‖cosineRegulator γ τ z‖) :
    Tendsto (fun n : ℕ => (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      ∮ z in C(0, cosineCircleRadius γ τ n), cosineContourIntegrand γ τ U z) atTop (𝓝 0) := by
  have hR := cosineCircleRadius_tendsto hγ hτ
  have hd : Tendsto (fun n => cosineCircleRadius γ τ n - 1) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ) hR
  have hlim : Tendsto (fun n => ‖cosineRegulator γ τ 1‖ * C /
      (cosineCircleRadius γ τ n - 1)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hd
  apply squeeze_zero_norm' _ hlim
  filter_upwards [hU, hR.eventually_gt_atTop 1] with n hn hRn
  have hb := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (show 0 ≤ cosineCircleRadius γ τ n by linarith)
    (cosineContourIntegrand_circle_le hγ hτ hC U n hRn hn)
  apply hb.trans_eq
  have hRn0 : cosineCircleRadius γ τ n ≠ 0 := ne_of_gt (by linarith)
  field_simp

end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
