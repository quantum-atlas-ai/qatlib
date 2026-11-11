/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.QuadratureCmp.TruncationGap
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# A gap in a finite-grid error estimate

This module examines a one-dimensional oscillatory instance of the quadrature setting in
[AftabAnTrivisa2026]. It compares the full integral, a short continuous truncation, and a
resonant three-point grid sum.

The construction `exists_final_bound_failure` gives positive scales for which the displayed mesh
estimate plus the continuous operator truncation error is strictly smaller than the actual
finite-grid error.

## Main statements

* `three_point`: the resonant three-point expression.
* `exists_final_bound_failure`: existence of a strict gap in the proposed combined bound.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.CommutLCHS26.QuadratureCmp.FinalBoundGap
open Complex Set Filter MeasureTheory
open scoped Topology BigOperators Matrix.Norms.L2Operator ComplexOrder
open Qatlib.Papers.CommutLCHS26.MainResults
open KernelStrip
open Qatlib.Papers.CommutLCHS26.QuadratureCmp
open Trapezoid TruncationGap

/-- For the one-dimensional choice `H = 0` and `L = 1`, the full integral norm is bounded by
`exp (-Tρ)` times the zero-growth strip mass under the stated strip conditions. -/
theorem full_decay (n : ℕ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c)
    {ρ T : ℝ} (hρ₀ : 0 < ρ) (hρ : ρ < 1) (hbn : n = 0 ∨ ρ < b) (hT : 0 ≤ T) :
    ‖∫ x : ℝ, integrand n b c d T (0 : Matrix (Fin 1) (Fin 1) ℂ) 1 (x : ℂ)‖ ≤
      Real.exp (-T * ρ) * mass n b c d ρ 0 := by
  let f := integrand n b c d 0 (0 : Matrix (Fin 1) (Fin 1) ℂ) 1
  have hs := integrand_strip_estimates n b c d hb hc
    (0 : Matrix (Fin 1) (Fin 1) ℂ) 1 Matrix.isHermitian_zero Matrix.PosSemidef.one
    (T := 0) (ρ := ρ) (by norm_num) hρ hbn
  have hd : DifferentiableOn ℂ f {z : ℂ | -ρ ≤ z.im ∧ z.im ≤ ρ} := by
    apply hs.1.differentiableOn.mono
    intro z hz
    exact abs_le.mpr hz
  have he := StripContour.fourier_decay_of_interior_mass f ρ (mass n b c d ρ 0) T
    hρ₀ hd hs.2.1
    (fun y hy => (hs.2.2 y (abs_le.mpr ⟨hy.1.le, hy.2.le⟩)).1)
    (fun y hy => by simpa using! (hs.2.2 y (abs_le.mpr ⟨hy.1.le, hy.2.le⟩)).2)
  have hi (x : ℝ) : StripContour.phase T (x : ℂ) • f (x : ℂ) =
      integrand n b c d T (0 : Matrix (Fin 1) (Fin 1) ℂ) 1 (x : ℂ) := by
    simp only [f, integrand, propagator_identity, StripContour.phase, neg_zero,
      ofReal_zero, zero_mul, Complex.exp_zero, one_smul, smul_smul]
    rw [mul_comm]
    simp only [neg_mul]
  simpa only [hi, abs_of_nonneg hT] using! he

/-- For nonnegative `T`, the strip mass with growth parameter `T` is at most its zero-growth
value times `exp (ρT)` under the stated conditions. -/
theorem mass_growth (n : ℕ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c)
    {ρ T : ℝ} (hρ₀ : 0 ≤ ρ) (hρ : ρ < 1) (hbn : n = 0 ∨ ρ < b) (hT : 0 ≤ T) :
    mass n b c d ρ T ≤ mass n b c d ρ 0 * Real.exp (ρ * T) := by
  have hden : 0 < (b - ρ) ^ n := by
    rcases hbn with rfl | hbn
    · simp
    · positivity
  have hm : max (-d) (d + T) ≤ max (-d) d + T := by
    apply max_le
    · linarith [le_max_left (-d) d]
    · linarith [le_max_right (-d) d]
  unfold mass
  rw [mul_assoc (c / Real.sqrt Real.pi * _) _ _, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left
  · apply Real.exp_le_exp.mpr
    simp only [add_zero]
    nlinarith [mul_le_mul_of_nonneg_left hm hρ₀]
  · exact mul_nonneg (div_nonneg hc.le (Real.sqrt_nonneg _))
      (div_nonneg (pow_nonneg (by linarith) _) (mul_nonneg (by linarith) hden.le))

/-- For positive `b`, the real-axis coefficient norm is at most its value at zero. -/
theorem coefficient_le_zero (n : ℕ) (b c d x : ℝ) (hb : 0 < b) :
    ‖coefficient n b c d (x : ℂ)‖ ≤ ‖coefficient n b c d 0‖ := by
  have he : ‖coefficient n b c d (x : ℂ)‖ = ‖coefficient n b c d ((|x| : ℝ) : ℂ)‖ := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, real_norm_even n b c d x hb]
  rw [he]
  exact real_norm_antitone n b c d hb (by simp) (abs_nonneg x) (abs_nonneg x)

/-- For the one-dimensional choice `H = 0` and `L = 1`, the integral over `[-R, R]` has norm at
most `2R` times the coefficient norm at zero when `T` and `R` are nonnegative. -/
theorem small_interval (n : ℕ) (b c d : ℝ) (hb : 0 < b)
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    ‖∫ x in Icc (-R) R,
      integrand n b c d T (0 : Matrix (Fin 1) (Fin 1) ℂ) 1 (x : ℂ)‖ ≤
      2 * R * ‖coefficient n b c d 0‖ := by
  have he := norm_setIntegral_le_of_norm_le_const
    (μ := volume) (s := Icc (-R) R) (f := fun x : ℝ =>
      integrand n b c d T (0 : Matrix (Fin 1) (Fin 1) ℂ) 1 (x : ℂ))
    isCompact_Icc.measure_lt_top (fun x _ =>
      (norm_real_integrand_le n b c d _ _ Matrix.isHermitian_zero Matrix.PosSemidef.one hT x).trans
        (coefficient_le_zero n b c d x hb))
  have hv : volume.real (Icc (-R) R) = 2 * R := by
    rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : 0 ≤ R - -R)]
    ring
  rw [hv] at he
  simpa only [mul_comm] using! he

/-- When `T h = π`, the three-point ideal grid sum is `h` times the central coefficient minus
its two neighboring coefficients, multiplied by the identity. -/
theorem three_point (n : ℕ) (b c d T h : ℝ) (hphase : T * h = Real.pi) :
    finiteIdeal n b c d T h (0 : Matrix (Fin 1) (Fin 1) ℂ) 1 1 =
      h • ((coefficient n b c d 0 - coefficient n b c d (h : ℂ) -
        coefficient n b c d ((-h : ℝ) : ℂ)) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) := by
  have hp : (T : ℂ) * (h : ℂ) = (Real.pi : ℂ) := by exact_mod_cast hphase
  have ep : Complex.exp ((-T : ℂ) * I * (h : ℂ)) = -1 := by
    rw [show (-T : ℂ) * I * (h : ℂ) = -((T : ℂ) * (h : ℂ) * I) by ring,
      hp, Complex.exp_neg_pi_mul_I]
  have en : Complex.exp ((-T : ℂ) * I * ((-h : ℝ) : ℂ)) = -1 := by
    rw [show (-T : ℂ) * I * ((-h : ℝ) : ℂ) = (T : ℂ) * (h : ℂ) * I by push_cast; ring,
      hp, Complex.exp_pi_mul_I]
  have hs : Finset.Icc (-1 : ℤ) 1 = {-1, 0, 1} := by decide
  simp only [ofReal_neg, mul_neg, neg_mul, neg_neg] at ep en
  unfold finiteIdeal
  norm_num only [Nat.cast_one]
  rw [hs]
  simp [integrand, propagator_identity, ep, en]
  module

/-- The norm of the central coefficient minus its two samples at `±1 / t` tends to the
coefficient norm at zero as `t` tends to positive infinity. -/
theorem resonant_norm_limit (n : ℕ) (b c d : ℝ) (hb : 0 < b) :
    Tendsto (fun t : ℝ => ‖coefficient n b c d 0 -
      coefficient n b c d ((1 / t : ℝ) : ℂ) -
      coefficient n b c d ((-(1 / t) : ℝ) : ℂ)‖) atTop
      (𝓝 ‖coefficient n b c d 0‖) := by
  have hf : ContinuousAt (coefficient n b c d) 0 :=
    (coefficient_analytic n b c d (ρ := 0) (by norm_num) (Or.inr hb) 0 (by simp)).continuousAt
  have ht : Tendsto (fun t : ℝ => ((1 / t : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa only [one_div, ofReal_zero] using!
      Complex.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0))
  have htn : Tendsto (fun t : ℝ => ((-(1 / t) : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa only [ofReal_neg, neg_zero] using! ht.neg
  have hp := hf.tendsto.comp ht
  have hn := hf.tendsto.comp htn
  simpa only [Function.comp_apply, sub_self, zero_sub, norm_neg] using!
    (((tendsto_const_nhds (x := coefficient n b c d 0)).sub hp).sub hn).norm

/-- Under the stated exponential lower bound, the mesh estimate at `T = πt` and `h = 1 / t`,
multiplied by `t`, is at most `4 * mass n b c d ρ 0 * t * exp (-πρt)`. -/
theorem mesh_scaled_bound (n : ℕ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c)
    {ρ t : ℝ} (hρ₀ : 0 < ρ) (hρ : ρ < 1) (hbn : n = 0 ∨ ρ < b)
    (ht : 0 < t) (hexp : 2 ≤ Real.exp (2 * Real.pi * ρ * t)) :
    t * (2 * mass n b c d ρ (Real.pi * t) /
      (Real.exp (2 * Real.pi * ρ / (1 / t)) - 1)) ≤
        4 * (mass n b c d ρ 0 * t * Real.exp (-(Real.pi * ρ) * t)) := by
  have he : 2 * Real.pi * ρ / (1 / t) = 2 * Real.pi * ρ * t := by field_simp
  rw [he]
  have hden : 0 < Real.exp (2 * Real.pi * ρ * t) - 1 := by linarith
  have hg := mass_growth n b c d hb hc hρ₀.le hρ hbn (mul_nonneg Real.pi_pos.le ht.le)
  have hM : 0 ≤ mass n b c d ρ 0 := by
    have hden : 0 < (b - ρ) ^ n := by rcases hbn with rfl | hbn <;> positivity
    unfold mass
    positivity
  apply (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hg (by norm_num)) hden.le) ht.le).trans
  have hhalf : Real.exp (2 * Real.pi * ρ * t) ≤
      2 * (Real.exp (2 * Real.pi * ρ * t) - 1) := by linarith
  have hsquare : Real.exp (2 * Real.pi * ρ * t) = Real.exp (ρ * (Real.pi * t)) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hr : 2 * Real.exp (ρ * (Real.pi * t)) / (Real.exp (2 * Real.pi * ρ * t) - 1) ≤
      4 / Real.exp (ρ * (Real.pi * t)) := by
    apply (div_le_div_iff₀ hden (Real.exp_pos _)).mpr
    nlinarith only [hsquare, hhalf]
  calc
    _ = (mass n b c d ρ 0 * t) *
        (2 * Real.exp (ρ * (Real.pi * t)) / (Real.exp (2 * Real.pi * ρ * t) - 1)) := by ring
    _ ≤ (mass n b c d ρ 0 * t) * (4 / Real.exp (ρ * (Real.pi * t))) :=
      mul_le_mul_of_nonneg_left hr (mul_nonneg hM ht.le)
    _ = _ := by
      rw [show -(Real.pi * ρ) * t = -(ρ * (Real.pi * t)) by ring, Real.exp_neg]
      ring

/-- There exist positive `T`, `R`, and `h` with `R = h²`, `T h = π`, and cutoff one for which
the mesh estimate plus the operator truncation error is strictly smaller than the actual
finite-grid error. -/
theorem exists_final_bound_failure (n : ℕ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c)
    {ρ : ℝ} (hρ₀ : 0 < ρ) (hρ : ρ < 1) (hbn : n = 0 ∨ ρ < b) :
    ∃ T R h : ℝ, 0 < T ∧ 0 < R ∧ 0 < h ∧ h < 1 ∧ R = h ^ 2 ∧
      T * h = Real.pi ∧ cutoff R h = 1 ∧
      2 * mass n b c d ρ T / (Real.exp (2 * Real.pi * ρ / h) - 1) +
        operatorTruncationError n b c d T (0 : Matrix (Fin 1) (Fin 1) ℂ) 1 R <
        ‖(∫ x : ℝ, integrand n b c d T (0 : Matrix (Fin 1) (Fin 1) ℂ) 1 (x : ℂ)) -
          finiteIdeal n b c d T h (0 : Matrix (Fin 1) (Fin 1) ℂ) 1 (cutoff R h)‖ := by
  let a := ‖coefficient n b c d 0‖
  let M := mass n b c d ρ 0
  have ha : 0 < a := norm_pos_iff.mpr (by simpa using! coefficient_ne_zero n b c d 0 hb)
  have hD : 0 < Real.pi * ρ := mul_pos Real.pi_pos hρ₀
  have hu : Tendsto (fun t : ℝ => M * t * Real.exp (-(Real.pi * ρ) * t)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one, mul_assoc, mul_zero] using!
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (Real.pi * ρ) hD).const_mul M
  have hv : Tendsto (fun t : ℝ => 2 * a / t) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using!
      (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0)).const_mul (2 * a)
  have he : Tendsto (fun t : ℝ => Real.exp (2 * Real.pi * ρ * t)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by positivity : 0 < 2 * Real.pi * ρ))
  have hs : ∀ᶠ t : ℝ in atTop, a / 2 < ‖coefficient n b c d 0 -
      coefficient n b c d ((1 / t : ℝ) : ℂ) - coefficient n b c d ((-(1 / t) : ℝ) : ℂ)‖ :=
    (resonant_norm_limit n b c d hb) (Ioi_mem_nhds (show a / 2 < a by linarith))
  have hu' : ∀ᶠ t : ℝ in atTop, M * t * Real.exp (-(Real.pi * ρ) * t) < a / 32 :=
    hu (Iio_mem_nhds (show 0 < a / 32 by positivity))
  have hv' : ∀ᶠ t : ℝ in atTop, 2 * a / t < a / 32 :=
    hv (Iio_mem_nhds (show 0 < a / 32 by positivity))
  obtain ⟨t, ht, hs, hu', hv', he⟩ :=
    ((eventually_gt_atTop (1 : ℝ)).and (hs.and (hu'.and (hv'.and (he.eventually_ge_atTop 2))))).exists
  have ht₀ : 0 < t := by linarith
  let h := 1 / t
  let R := h ^ 2
  let T := Real.pi * t
  have hh : 0 < h := by dsimp [h]; positivity
  have hh1 : h < 1 := (div_lt_one ht₀).mpr ht
  have hR : 0 < R := sq_pos_of_pos hh
  have hT : 0 < T := mul_pos Real.pi_pos ht₀
  have hcut : cutoff R h = 1 := by
    unfold cutoff
    have hr : R / h = h := by dsimp [R]; field_simp
    rw [hr]
    exact (Nat.ceil_eq_iff (by norm_num : (1 : ℕ) ≠ 0)).mpr (by simpa using! And.intro hh hh1.le)
  have hphase : T * h = Real.pi := by dsimp [T, h]; field_simp
  let A := ∫ x : ℝ, integrand n b c d T (0 : Matrix (Fin 1) (Fin 1) ℂ) 1 (x : ℂ)
  let J := ∫ x in Icc (-R) R, integrand n b c d T (0 : Matrix (Fin 1) (Fin 1) ℂ) 1 (x : ℂ)
  let W := finiteIdeal n b c d T h (0 : Matrix (Fin 1) (Fin 1) ℂ) 1 (cutoff R h)
  let B := 2 * mass n b c d ρ T / (Real.exp (2 * Real.pi * ρ / h) - 1)
  have hi : t * ‖A‖ < a / 32 := by
    have hf := mul_le_mul_of_nonneg_left (full_decay n b c d hb hc hρ₀ hρ hbn hT.le) ht₀.le
    have hf' : t * ‖A‖ ≤ M * t * Real.exp (-(Real.pi * ρ) * t) := by
      calc
        _ ≤ t * (Real.exp (-T * ρ) * mass n b c d ρ 0) := hf
        _ = _ := by
          dsimp [T, M]
          rw [show -(Real.pi * t) * ρ = -(Real.pi * ρ) * t by ring]
          ring
    exact hf'.trans_lt hu'
  have hj : t * ‖J‖ < a / 32 := by
    have hf := mul_le_mul_of_nonneg_left (small_interval n b c d hb hT.le hR.le) ht₀.le
    have hf' : t * ‖J‖ ≤ 2 * a / t := by
      convert! hf using 1
      dsimp [R, h, a]
      field_simp
    exact hf'.trans_lt hv'
  have hm : t * B < 4 * (a / 32) :=
    (mesh_scaled_bound n b c d hb hc hρ₀ hρ hbn ht₀ he).trans_lt
      (mul_lt_mul_of_pos_left hu' (by norm_num))
  have hw : a / 2 < t * ‖W‖ := by
    dsimp [W]
    rw [hcut, three_point n b c d T h hphase, norm_smul, Real.norm_of_nonneg hh.le,
      norm_smul, norm_one, mul_one, ← mul_assoc]
    have hinv : t * h = 1 := by dsimp [h]; field_simp
    rw [hinv, one_mul]
    exact hs
  refine ⟨T, R, h, hT, hR, hh, hh1, rfl, hphase, hcut, ?_⟩
  change B + ‖A - J‖ < ‖A - W‖
  by_contra! hbad
  have hn : ‖W‖ ≤ ‖A‖ + ‖A - W‖ := norm_le_norm_add_norm_sub A W
  have hjn := norm_sub_le A J
  have hineq : ‖W‖ ≤ B + 2 * ‖A‖ + ‖J‖ := by linarith
  have hf := mul_le_mul_of_nonneg_left hineq ht₀.le
  nlinarith only [hf, hw, hm, hi, hj, ha]

end Qatlib.Papers.CommutLCHS26.QuadratureCmp.FinalBoundGap
