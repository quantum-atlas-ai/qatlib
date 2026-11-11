/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.CosineCoefficients
import Qatlib.Foundations.CbmdAnalysis.Core.AnalyticRegulator

/-!
# Finite cosine-regulator circle identities

This module defines cosine contour radii, finite pole sets, weighted samples, and their partial
sums. It locates the denominator zeros inside each disk and applies the simple-zero circle
formula to obtain a finite sampling identity. These identities provide the finite contour step
in [WangEtAl2026].

## Main statements

* `cosineContourPoleSet_zeros`: the closed-disk zeros are exactly the finite pole set.
* `cosineContourPoleSet_simple`: every listed zero has nonzero denominator derivative.
* `cosineContour_circle_identity_normalized`: the normalized integral equals the target minus
  the weighted baseline plus the weighted finite sample sum.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
noncomputable section
namespace CBMD
open Complex Metric Set
open scoped BigOperators

/-- The cosine contour radius `(n * π) ^ 2 / (γ * τ ^ 2)`. -/
def cosineCircleRadius (γ τ : ℝ) (n : ℕ) : ℝ := ((n : ℝ) * Real.pi) ^ 2 / (γ * τ ^ 2)

/-- For positive `γ` and `τ`, the sample pole norm equals `cosineSampleScale γ τ k`. -/
theorem cosineSamplePole_norm {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ) (k : ℕ) :
    ‖cosineSamplePole γ τ k‖ = cosineSampleScale γ τ k := by
  simp only [cosineSamplePole, norm_mul, norm_neg, norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (cosineSampleScale_pos hγ hτ k)]

/-- For positive `γ` and `τ`, distinct natural indices give distinct cosine sample poles. -/
theorem cosineSamplePole_injective {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ) :
    Function.Injective (cosineSamplePole γ τ) := by
  intro j k hjk
  have hn := congrArg norm hjk
  rw [cosineSamplePole_norm hγ hτ, cosineSamplePole_norm hγ hτ] at hn
  unfold cosineSampleScale at hn
  have he := (div_left_inj' (ne_of_gt (mul_pos hγ (sq_pos_of_pos hτ)))).mp hn
  have hx := (sq_eq_sq₀ (cosineSampleAngle_pos j).le (cosineSampleAngle_pos k).le).mp he
  unfold cosineSampleAngle at hx
  have := (mul_right_cancel₀ Real.pi_ne_zero hx)
  exact_mod_cast (add_right_cancel this : (j : ℝ) = (k : ℝ))

/-- For positive parameters, the `k`th sample pole lies in the open `n`th cosine disk exactly
when `k < n`. -/
theorem cosineSamplePole_mem_ball {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ) (k n : ℕ) :
    cosineSamplePole γ τ k ∈ ball (0 : ℂ) (cosineCircleRadius γ τ n) ↔ k < n := by
  rw [mem_ball_zero_iff, cosineSamplePole_norm hγ hτ]
  unfold cosineSampleScale cosineCircleRadius
  rw [div_lt_div_iff_of_pos_right (mul_pos hγ (sq_pos_of_pos hτ)),
    sq_lt_sq₀ (cosineSampleAngle_pos k).le (by positivity)]
  unfold cosineSampleAngle
  rw [mul_lt_mul_iff_left₀ Real.pi_pos]
  constructor
  · intro h
    have hh : (k : ℝ) < n := by linarith
    exact_mod_cast hh
  · intro h
    have hh : (k : ℝ) + 1 ≤ n := by exact_mod_cast h
    linarith

/-- For positive parameters, the `k`th sample pole lies in the closed `n`th cosine disk exactly
when `k < n`. -/
theorem cosineSamplePole_mem_closedBall {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ) (k n : ℕ) :
    cosineSamplePole γ τ k ∈ closedBall (0 : ℂ) (cosineCircleRadius γ τ n) ↔ k < n := by
  rw [mem_closedBall_zero_iff, cosineSamplePole_norm hγ hτ]
  unfold cosineSampleScale cosineCircleRadius
  rw [div_le_div_iff_of_pos_right (mul_pos hγ (sq_pos_of_pos hτ)),
    sq_le_sq₀ (cosineSampleAngle_pos k).le (by positivity)]
  unfold cosineSampleAngle
  rw [mul_le_mul_iff_left₀ Real.pi_pos]
  constructor
  · intro h
    have hh : (k : ℝ) < n := by linarith
    exact_mod_cast hh
  · intro h
    have hh : (k : ℝ) + 1 ≤ n := by exact_mod_cast h
    linarith

/-- The finite set containing zero, one, and the first `n` cosine sample poles. -/
def cosineContourPoleSet (γ τ : ℝ) (n : ℕ) : Finset ℂ :=
  insert 0 (insert 1 ((Finset.range n).image (cosineSamplePole γ τ)))

/-- For positive parameters, the contour denominator vanishes exactly at zero, one, and the
cosine sample poles. -/
theorem cosineContourDenominator_eq_zero_iff {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ) (z : ℂ) :
    cosineContourDenominator γ τ z = 0 ↔ z = 0 ∨ z = 1 ∨ ∃ k, z = cosineSamplePole γ τ k := by
  simp only [cosineContourDenominator, mul_eq_zero, sub_eq_zero,
    cosineRegulator_eq_zero_iff hγ hτ, or_assoc]

/-- For positive parameters and cosine radius greater than one, every point of the finite
contour pole set lies strictly inside the disk. -/
theorem cosineContourPoleSet_inside {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ) (n : ℕ)
    (hR : 1 < cosineCircleRadius γ τ n) :
    ∀ z ∈ cosineContourPoleSet γ τ n, z ∈ ball (0 : ℂ) (cosineCircleRadius γ τ n) := by
  intro z hz
  simp only [cosineContourPoleSet, Finset.mem_insert, Finset.mem_image, Finset.mem_range] at hz
  rcases hz with rfl | rfl | ⟨k, hk, rfl⟩
  · simp only [mem_ball_zero_iff, norm_zero]
    linarith
  · simpa only [mem_ball_zero_iff, norm_one] using hR
  · exact (cosineSamplePole_mem_ball hγ hτ k n).mpr hk

/-- For positive parameters, the zeros of the contour denominator in the closed `n`th cosine
disk are exactly the finite contour pole set. -/
theorem cosineContourPoleSet_zeros {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ) (n : ℕ)
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) (cosineCircleRadius γ τ n)) :
    cosineContourDenominator γ τ z = 0 ↔ z ∈ cosineContourPoleSet γ τ n := by
  rw [cosineContourDenominator_eq_zero_iff hγ hτ]
  simp only [cosineContourPoleSet, Finset.mem_insert, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro (rfl | rfl | ⟨k, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨k, (cosineSamplePole_mem_closedBall hγ hτ k n).mp hz, rfl⟩)
  · rintro (rfl | rfl | ⟨k, _, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨k, rfl⟩)

/-- For positive parameters, the contour denominator has nonzero derivative at every point of
the finite contour pole set. -/
theorem cosineContourPoleSet_simple {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ) (n : ℕ) :
    ∀ z ∈ cosineContourPoleSet γ τ n, deriv (cosineContourDenominator γ τ) z ≠ 0 := by
  intro z hz
  simp only [cosineContourPoleSet, Finset.mem_insert, Finset.mem_image] at hz
  rcases hz with rfl | rfl | ⟨k, _, rfl⟩
  · rw [cosineContourDenominator_deriv_zero]
    norm_num
  · rw [cosineContourDenominator_deriv_one]
    exact cosineRegulator_one_ne_zero hγ hτ
  · exact cosineContourDenominator_deriv_sample_ne_zero hγ hτ k

/-- For positive parameters, a sum over the finite contour pole set splits into the values at
zero and one and the sum over the first `n` sample poles. -/
theorem cosineContourPoleSet_sum {M : Type*} [AddCommMonoid M]
    {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ) (n : ℕ) (f : ℂ → M) :
    ∑ z ∈ cosineContourPoleSet γ τ n, f z =
      f 0 + f 1 + ∑ k ∈ Finset.range n, f (cosineSamplePole γ τ k) := by
  classical
  have h0 : (0 : ℂ) ∉ (Finset.range n).image (cosineSamplePole γ τ) := by
    simp only [Finset.mem_image, not_exists, not_and]
    intro k _ hk
    exact cosineSamplePole_ne_zero hγ hτ k hk
  have h1 : (1 : ℂ) ∉ (Finset.range n).image (cosineSamplePole γ τ) := by
    simp only [Finset.mem_image, not_exists, not_and]
    intro k _ hk
    exact cosineSamplePole_ne_one γ τ k hk
  unfold cosineContourPoleSet
  rw [Finset.sum_insert (by simp [h0]), Finset.sum_insert h1,
    Finset.sum_image (fun j _ k _ hjk => cosineSamplePole_injective hγ hτ hjk)]
  exact (add_assoc _ _ _).symm

section Numerator
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The numerator `U z` multiplied by the ratio of the regulator at one to the contour
denominator at `z`. -/
def cosineContourIntegrand (γ τ : ℝ) (U : ℂ → E) (z : ℂ) : E :=
  (cosineRegulator γ τ 1 / cosineContourDenominator γ τ z) • U z

/-- The numerator value at the `k`th cosine sample pole weighted by its sample coefficient. -/
def cosineSample (γ τ : ℝ) (U : ℂ → E) (k : ℕ) : E :=
  cosineSampleCoefficient γ τ k • U (cosineSamplePole γ τ k)

/-- The sum of the first `n` weighted cosine samples. -/
def cosineLCUSum (γ τ : ℝ) (n : ℕ) (U : ℂ → E) : E :=
  ∑ k ∈ Finset.range n, cosineSample γ τ U k

variable [CompleteSpace E]

/-- For positive parameters, radius greater than one, and complex differentiable `U`, the
contour integral equals `2πI` times `U 1 - cosineRegulator γ τ 1 • U 0 + cosineRegulator γ τ
1 • cosineLCUSum γ τ n U`. -/
theorem cosineContour_circle_identity {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ)
    (n : ℕ) (hR : 1 < cosineCircleRadius γ τ n)
    (U : ℂ → E) (hU : Differentiable ℂ U) :
    (∮ z in C(0, cosineCircleRadius γ τ n), cosineContourIntegrand γ τ U z) =
      (2 * (Real.pi : ℂ) * Complex.I) •
        (U 1 - cosineRegulator γ τ 1 • U 0 +
          cosineRegulator γ τ 1 • cosineLCUSum γ τ n U) := by
  classical
  let c : ℂ := cosineRegulator γ τ 1
  have hR0 : 0 ≤ cosineCircleRadius γ τ n := by linarith
  have hF : Differentiable ℂ (fun z => c • U z) := (differentiable_const c).smul hU
  have hD : Differentiable ℂ (cosineContourDenominator γ τ) :=
    fun z => (cosineContourDenominator_analytic γ τ z).differentiableAt
  have hC := circleIntegral_analytic_regulator (cosineContourPoleSet γ τ n) hR0
    (fun z => c • U z) (cosineContourDenominator γ τ) hF.diffContOnCl hD.diffContOnCl
    (cosineContourPoleSet_inside hγ hτ n hR)
    (cosineContourPoleSet_zeros hγ hτ n) (cosineContourPoleSet_simple hγ hτ n)
  have heq : (fun z => cosineContourIntegrand γ τ U z) =
      (fun z => (cosineContourDenominator γ τ z)⁻¹ • (c • U z)) := by
    funext z
    unfold cosineContourIntegrand
    rw [smul_smul]
    congr 1
    dsimp [c]
    ring
  rw [heq, hC]
  congr 1
  rw [cosineContourPoleSet_sum hγ hτ n]
  rw [cosineContourDenominator_deriv_zero, cosineContourDenominator_deriv_one]
  have hc : c ≠ 0 := cosineRegulator_one_ne_zero hγ hτ
  have htarget : (cosineRegulator γ τ 1)⁻¹ • (c • U 1) = U 1 := by
    rw [smul_smul, show (cosineRegulator γ τ 1)⁻¹ * c = 1 from inv_mul_cancel₀ hc,
      one_smul]
  rw [htarget]
  have hsample (k : ℕ) :
      (deriv (cosineContourDenominator γ τ) (cosineSamplePole γ τ k))⁻¹ •
        (c • U (cosineSamplePole γ τ k)) = c • cosineSample γ τ U k := by
    rw [← cosineSampleCoefficient_eq_deriv_inv hγ hτ k]
    unfold cosineSample
    rw [smul_smul, smul_smul, mul_comm]
  simp_rw [hsample]
  rw [← Finset.smul_sum]
  simp only [inv_neg, inv_one, neg_smul, one_smul]
  change -(c • U 0) + U 1 + c • cosineLCUSum γ τ n U = _
  dsimp [c]
  abel

/-- For positive parameters, radius greater than one, and complex differentiable `U`, dividing
the cosine contour integral by `2πI` yields the target minus the regulator-weighted baseline
plus the regulator-weighted finite sample sum. -/
theorem cosineContour_circle_identity_normalized {γ τ : ℝ}
    (hγ : 0 < γ) (hτ : 0 < τ) (n : ℕ) (hR : 1 < cosineCircleRadius γ τ n)
    (U : ℂ → E) (hU : Differentiable ℂ U) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
      (∮ z in C(0, cosineCircleRadius γ τ n), cosineContourIntegrand γ τ U z) =
        U 1 - cosineRegulator γ τ 1 • U 0 +
          cosineRegulator γ τ 1 • cosineLCUSum γ τ n U := by
  rw [cosineContour_circle_identity hγ hτ n hR U hU,
    smul_smul, inv_mul_cancel₀, one_smul]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
    Complex.I_ne_zero

end Numerator
end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
