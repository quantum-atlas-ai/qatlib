/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.KernelContourLimit
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Decay of integer kernels on expanding circles

This module bounds the lattice factor on circles with half-grid radii, including the portion
near the real axis where its phase requires separate control. A radial lower bound for the
pole-distance denominator yields quadratic decay of `integerContourIntegrand` on sufficiently
large circles.

The normalized circle integrals consequently tend to zero under the prescribed half-plane growth
estimate. This is the vanishing boundary term in the sampling argument of [WangEtAl2026].

## Main statements

* `integerContourIntegrand_circle_le`: gives a uniform quadratic circle bound.
* `integerContour_circle_tendsto_zero`: proves vanishing normalized circle integrals.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace CBMD
open Complex Metric Set Filter MeasureTheory
open scoped Topology BigOperators

/-- On a half-grid circle of radius at least `4a`, points with imaginary part of absolute value
at most one satisfy `cos (2πa * z.re) ≤ 0`. -/
private theorem halfGrid_circle_phase {a : ℝ} (ha : 0 < a) (n : ℕ)
    (hR : 4 * a ≤ halfGridRadius a n) (z : ℂ)
    (hz : ‖z‖ = halfGridRadius a n) (hy : |z.im| ≤ 1) :
    Real.cos (2 * Real.pi * a * z.re) ≤ 0 := by
  let R := halfGridRadius a n
  have hR0 : 0 < R := by dsimp [R, halfGridRadius]; positivity
  have hx : |z.re| ≤ R := (Complex.abs_re_le_norm z).trans_eq hz
  have hn : z.re ^ 2 + z.im ^ 2 = R ^ 2 := by
    simpa only [Complex.normSq_apply, hz, pow_two, R] using Complex.normSq_eq_norm_sq z
  have hy2 : z.im ^ 2 ≤ 1 := by nlinarith [sq_abs z.im, abs_nonneg z.im]
  have hdiff : 0 ≤ R - |z.re| := sub_nonneg.mpr hx
  have hd : 4 * a * (R - |z.re|) ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_right hR hdiff
    have hnon := mul_nonneg hdiff (abs_nonneg z.re)
    nlinarith [sq_abs z.re]
  let d := 2 * Real.pi * a * (|z.re| - R)
  have hd0 : d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hx)
  have hdl : -(Real.pi / 2) ≤ d := by
    have h := mul_le_mul_of_nonneg_left hd Real.pi_pos.le
    dsimp [d]
    nlinarith
  have hphase : 2 * Real.pi * a * |z.re| = d + Real.pi + (n : ℝ) * (2 * Real.pi) := by
    dsimp [d, R, halfGridRadius]
    field_simp
    ring
  have habs : Real.cos (2 * Real.pi * a * z.re) = Real.cos (2 * Real.pi * a * |z.re|) := by
    rcases le_total 0 z.re with hp | hm
    · rw [abs_of_nonneg hp]
    · rw [abs_of_nonpos hm, mul_neg, Real.cos_neg]
  rw [habs, hphase, Real.cos_add_nat_mul_two_pi, Real.cos_add_pi]
  exact neg_nonpos.mpr (Real.cos_nonneg_of_mem_Icc ⟨hdl, hd0.trans (by positivity)⟩)

/-- For positive spacing, the lattice factor norm is at most one on the strip `|z.im| ≤ 1` of a
half-grid circle with radius at least `4a`. -/
private theorem lattice_factor_circle_middle {a : ℝ} (ha : 0 < a) (n : ℕ)
    (hR : 4 * a ≤ halfGridRadius a n) (z : ℂ)
    (hz : ‖z‖ = halfGridRadius a n) (hy : |z.im| ≤ 1) :
    ‖latticePoleFactor a z‖ ≤ 1 := by
  have hc := halfGrid_circle_phase ha n hR z hz hy
  let w := Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * z)
  have hw : w.re ≤ 0 := by
    have he : (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * z).im =
        -(2 * Real.pi * a * z.re) := by simp [Complex.mul_im, Complex.mul_re]
    dsimp [w]
    rw [Complex.exp_re, he, Real.cos_neg]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hc
  have hden : 1 ≤ ‖w - 1‖ := by
    have h := Complex.abs_re_le_norm (w - 1)
    rw [Complex.sub_re, Complex.one_re, abs_of_nonpos (by linarith : w.re - 1 ≤ 0)] at h
    linarith
  have hn : ‖(-(Real.exp (-2 * Real.pi * a) - 1 : ℝ) : ℂ)‖ ≤ 1 := by
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]
    have he := Real.exp_le_one_iff.mpr (show -2 * Real.pi * a ≤ 0 by nlinarith [Real.pi_pos])
    rw [abs_of_nonpos (by linarith)]
    linarith [Real.exp_pos (-2 * Real.pi * a)]
  rw [latticePoleFactor, norm_div]
  exact (div_le_one (lt_of_lt_of_le (by norm_num) hden)).mpr (hn.trans hden)

/-- On a half-grid circle of radius at least `4a`, positive spacing and `ρ ≤ 2πa` bound the
lattice factor times `exp (max z.im 0 * ρ)` by `exp |ρ|`. -/
theorem lattice_circle_growth_le {a ρ : ℝ} (ha : 0 < a)
    (hρ : ρ ≤ 2 * Real.pi * a) (n : ℕ) (hR : 4 * a ≤ halfGridRadius a n)
    (z : ℂ) (hz : ‖z‖ = halfGridRadius a n) :
    ‖latticePoleFactor a z‖ * Real.exp (max z.im 0 * ρ) ≤ Real.exp |ρ| := by
  by_cases hy : |z.im| ≤ 1
  · have hb := lattice_factor_circle_middle ha n hR z hz hy
    have hm : max z.im 0 ≤ 1 := max_le (le_trans (le_abs_self _) hy) (by norm_num)
    have he : max z.im 0 * ρ ≤ |ρ| := by
      exact (mul_le_mul_of_nonneg_left (le_abs_self ρ) (le_max_right _ _)).trans
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hm (abs_nonneg ρ))
    calc
      _ ≤ 1 * Real.exp (max z.im 0 * ρ) := mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
      _ ≤ Real.exp |ρ| := by simpa only [one_mul] using Real.exp_le_exp.mpr he
  · have hone : ‖latticePoleFactor a z‖ * Real.exp (max z.im 0 * ρ) ≤ 1 := by
      by_cases hy0 : 0 ≤ z.im
      · have hy1 : 1 ≤ z.im := by rw [abs_of_nonneg hy0] at hy; linarith
        calc
          _ ≤ Real.exp (-2 * Real.pi * a * z.im) * Real.exp (z.im * ρ) := by
            rw [max_eq_left hy0]
            exact mul_le_mul_of_nonneg_right (latticePoleFactor_norm_le ha z hy1)
                (Real.exp_pos _).le
          _ = Real.exp (-2 * Real.pi * a * z.im + z.im * ρ) := (Real.exp_add _ _).symm
          _ ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      · have hy1 : z.im ≤ -1 := by rw [abs_of_neg (lt_of_not_ge hy0)] at hy; linarith
        have hy0' : z.im ≤ 0 := by linarith
        simpa only [max_eq_right hy0', zero_mul, Real.exp_zero, mul_one]
          using latticePoleFactor_norm_le_lower ha z hy1
    exact hone.trans (Real.one_le_exp (abs_nonneg _))

/-- Outside radius `m + 2`, the full pole-distance denominator is at least `(‖z‖ - (m + 2)) ^ (2
* m + 3)`. -/
theorem contour_denominator_radial_lower (m : ℕ) (z : ℂ) (hz : m + 2 < ‖z‖) :
    (‖z‖ - (m + 2)) ^ (2 * m + 3) ≤
      ‖z + Complex.I‖ * ‖z - 2 * Complex.I‖ *
        ∏ r ∈ Finset.Icc (-(m : ℤ)) m, ‖z - (r : ℂ) - Complex.I‖ := by
  have hd : 0 < ‖z‖ - (m + 2) := sub_pos.mpr hz
  have hc : (Finset.Icc (-(m : ℤ)) m).card = 2 * m + 1 := by rw [Int.card_Icc]; omega
  have hp : (‖z‖ - (m + 2)) ^ (2 * m + 1) ≤
      ∏ r ∈ Finset.Icc (-(m : ℤ)) m, ‖z - (r : ℂ) - Complex.I‖ := by
    calc
      _ = ∏ _r ∈ Finset.Icc (-(m : ℤ)) m, (‖z‖ - (m + 2)) := by simp only [Finset.prod_const, hc]
      _ ≤ _ := by
        apply Finset.prod_le_prod₀ (fun _ _ => hd.le)
        intro r hr
        have hr' := Finset.mem_Icc.mp hr
        have hrabs : |(r : ℝ)| ≤ m := by
          apply abs_le.mpr
          constructor
          · exact_mod_cast hr'.1
          · exact_mod_cast hr'.2
        have hpole : ‖(r : ℂ) + Complex.I‖ ≤ m + 2 := by
          calc
            _ ≤ ‖(r : ℂ)‖ + ‖Complex.I‖ := norm_add_le _ _
            _ ≤ m + 2 := by simpa only [Complex.norm_intCast, Complex.norm_I] using (show |(r : ℝ)| + 1 ≤ m + 2 by linarith)
        have ht := norm_sub_norm_le z ((r : ℂ) + Complex.I)
        rw [← sub_sub] at ht
        linarith
  have h₁ : ‖z‖ - (m + 2) ≤ ‖z + Complex.I‖ := by
    have h := norm_sub_norm_le z (-Complex.I)
    simp only [norm_neg, Complex.norm_I, sub_neg_eq_add] at h
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have h₂ : ‖z‖ - (m + 2) ≤ ‖z - 2 * Complex.I‖ := by
    have h := norm_sub_norm_le z (2 * Complex.I)
    norm_num at h
    linarith [Nat.cast_nonneg (α := ℝ) m]
  calc
    _ = ((‖z‖ - (m + 2)) * (‖z‖ - (m + 2))) * (‖z‖ - (m + 2)) ^ (2 * m + 1) := by
      rw [show 2 * m + 3 = (2 * m + 1) + 2 by omega, pow_add, pow_two]; ring
    _ ≤ _ := mul_le_mul (mul_le_mul h₁ h₂ hd.le (norm_nonneg _)) hp (by positivity) (by positivity)

section Integrand
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Under the stated growth and spacing hypotheses, the integrand norm on a sufficiently large
half-grid circle is at most `kernelNormalization m * exp |ρ| / (halfGridRadius a n - (m +
2))²`. -/
theorem integerContourIntegrand_circle_le (m : ℕ) {a ρ : ℝ} (ha : 0 < a)
    (hρ : ρ ≤ 2 * Real.pi * a) (U : ℂ → E)
    (hU : ∀ z, ‖U z‖ ≤ Real.exp (max z.im 0 * ρ))
    (n : ℕ) (hRa : 4 * a ≤ halfGridRadius a n) (hRm : m + 3 ≤ halfGridRadius a n)
    (z : ℂ) (hz : z ∈ sphere 0 (halfGridRadius a n)) :
    ‖integerContourIntegrand m a U z‖ ≤
      kernelNormalization m * Real.exp |ρ| / (halfGridRadius a n - (m + 2)) ^ 2 := by
  have hzn : ‖z‖ = halfGridRadius a n := by simpa only [mem_sphere_iff_norm, sub_zero] using hz
  have hd1 : 1 ≤ halfGridRadius a n - (m + 2) := by linarith
  have hd0 : 0 < halfGridRadius a n - (m + 2) := by linarith
  have hden : (halfGridRadius a n - (m + 2)) ^ 2 ≤
      ‖z + Complex.I‖ * ‖z - 2 * Complex.I‖ *
        ∏ r ∈ Finset.Icc (-(m : ℤ)) m, ‖z - (r : ℂ) - Complex.I‖ := by
    apply (pow_le_pow_right₀ hd1 (show 2 ≤ 2 * m + 3 by omega)).trans
    simpa only [hzn] using contour_denominator_radial_lower m z (by rw [hzn]; linarith)
  have hLU : ‖latticePoleFactor a z‖ * ‖U z‖ ≤ Real.exp |ρ| :=
    (mul_le_mul_of_nonneg_left (hU z) (norm_nonneg _)).trans
      (lattice_circle_growth_le ha hρ n hRa z hzn)
  rw [integerContourIntegrand, norm_smul, integerContourKernel_norm]
  calc
    _ = kernelNormalization m * (‖latticePoleFactor a z‖ * ‖U z‖) /
        (‖z + Complex.I‖ * ‖z - 2 * Complex.I‖ *
          ∏ r ∈ Finset.Icc (-(m : ℤ)) m, ‖z - (r : ℂ) - Complex.I‖) := by ring
    _ ≤ kernelNormalization m * Real.exp |ρ| /
        (‖z + Complex.I‖ * ‖z - 2 * Complex.I‖ *
          ∏ r ∈ Finset.Icc (-(m : ℤ)) m, ‖z - (r : ℂ) - Complex.I‖) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hLU (kernelNormalization_pos m).le
    _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg (kernelNormalization_pos m).le (Real.exp_pos _).le)
      (sq_pos_of_pos hd0) hden

/-- With positive spacing, `ρ ≤ 2πa`, and the stated global growth bound on `U`, the normalized
integrals over expanding half-grid circles tend to zero. -/
theorem integerContour_circle_tendsto_zero (m : ℕ) {a ρ : ℝ} (ha : 0 < a)
    (hρ : ρ ≤ 2 * Real.pi * a) (U : ℂ → E)
    (hU : ∀ z, ‖U z‖ ≤ Real.exp (max z.im 0 * ρ)) :
    Tendsto (fun n : ℕ => (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      ∮ z in C(0, halfGridRadius a n), integerContourIntegrand m a U z) atTop (𝓝 0) := by
  have hR := halfGridRadius_tendsto ha
  have hd : Tendsto (fun n => halfGridRadius a n - (m + 2)) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-((m : ℝ) + 2)) hR
  have hlim : Tendsto (fun n => 2 * (kernelNormalization m * Real.exp |ρ|) /
      (halfGridRadius a n - (m + 2))) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hd
  apply squeeze_zero_norm' _ hlim
  filter_upwards [hR.eventually_ge_atTop (4 * a), hR.eventually_ge_atTop (2 * ((m : ℝ) + 3))]
    with n hRa hRm
  have hRm' : (m : ℝ) + 3 ≤ halfGridRadius a n := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hd0 : 0 < halfGridRadius a n - (m + 2) := by linarith
  have hN := (kernelNormalization_pos m).le
  have hb := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (show 0 ≤ halfGridRadius a n by dsimp [halfGridRadius]; positivity)
    (integerContourIntegrand_circle_le m ha hρ U hU n hRa hRm')
  apply hb.trans
  calc
    _ ≤ (2 * (halfGridRadius a n - (m + 2))) *
        (kernelNormalization m * Real.exp |ρ| / (halfGridRadius a n - (m + 2)) ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by field_simp

end Integrand
end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
