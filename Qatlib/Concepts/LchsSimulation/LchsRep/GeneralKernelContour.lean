/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.Kernel.NearExponentialLchsKernel
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Normed.Module.Dual

/-!
# Cauchy contour formulas for power-decaying kernels

The regularization `powerCauchyRegular` removes the contribution of the pole at `-Complex.I`.
Power-decay estimates control its boundary integrals and yield
`power_kernel_lower_cauchy_integral`, together with continuity and integrability of the
Cauchy-weighted boundary kernel. See [AnChildsLin2026] for the mathematical setting.

## Main statements

* `power_kernel_weight_integrable`: A complex differentiable lower-half-plane kernel with
  positive-order power decay has an integrable Cauchy-weighted real boundary value.
* `power_kernel_lower_cauchy_integral`: For a complex differentiable kernel with the stated
  positive-order power decay and boundary integrability, the Cauchy-weighted real-line integral
  equals `2 * Real.pi * H (-Complex.I)`.

## References

* [An, Childs, and Lin, 2026][AnChildsLin2026]
-/

open Qatlib.Concepts.LchsSimulation.Kernel
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
namespace Qatlib.Concepts.LchsSimulation.LchsRep
open MeasureTheory Set Filter
open scoped Classical BigOperators Topology
/-- The regularized Cauchy expression formed from the divided slope of `H` at `-Complex.I` and
its explicit pole-value correction. -/
private noncomputable def powerCauchyRegular (H : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.I * dslope H (-Complex.I) z - H (-Complex.I) / (1 + Complex.I * z)

/-- Complex differentiability of `H` on the closed lower half-plane implies differentiability of
`powerCauchyRegular H` there. -/
private theorem powerCauchyRegular_differentiableOn (H : ℂ → ℂ)
    (hd : DifferentiableOn ℂ H {z : ℂ | z.im ≤ 0}) :
    DifferentiableOn ℂ (powerCauchyRegular H) {z : ℂ | z.im ≤ 0} := by
  have hn : {z : ℂ | z.im ≤ 0} ∈ 𝓝 (-Complex.I) :=
    Complex.continuous_im.continuousAt.preimage_mem_nhds (Iic_mem_nhds (by norm_num))
  have hs := (Complex.differentiableOn_dslope hn).mpr hd
  intro z hz
  have ha : DifferentiableWithinAt ℂ (fun w : ℂ => 1 + Complex.I * w)
      {z : ℂ | z.im ≤ 0} z :=
    ((differentiableAt_const (1 : ℂ)).add
      ((differentiableAt_const Complex.I).mul differentiableAt_id)).differentiableWithinAt
  have hne : (1 : ℂ) + Complex.I * z ≠ 0 :=
    Complex.slitPlane_ne_zero (highKernel_slitPlane z hz)
  exact ((differentiableAt_const Complex.I).differentiableWithinAt.mul (hs z hz)).sub
    ((differentiableAt_const (H (-Complex.I))).differentiableWithinAt.div ha hne)

/-- Away from the stated denominator zeros, the regularized expression equals the
Cauchy-weighted value minus `2 * H (-Complex.I) / ((1 - Complex.I * z) * (1 + Complex.I *
z))`. -/
private theorem powerCauchyRegular_eq (H : ℂ → ℂ) (z : ℂ)
    (hz : z ≠ -Complex.I) (hm : (1 : ℂ) - Complex.I * z ≠ 0)
    (hp : (1 : ℂ) + Complex.I * z ≠ 0) :
    powerCauchyRegular H z = H z / (1 - Complex.I * z) -
      2 * H (-Complex.I) / ((1 - Complex.I * z) * (1 + Complex.I * z)) := by
  rw [powerCauchyRegular, dslope_of_ne H hz]
  simp only [slope, smul_eq_mul, vsub_eq_sub]
  have hz' : z - -Complex.I ≠ 0 := sub_ne_zero.mpr hz
  field_simp
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three]
  ring

/-- On the real axis, the regularized expression equals the Cauchy-weighted boundary value minus
`(1 + k^2)⁻¹` times `2 * H (-Complex.I)`. -/
private theorem powerCauchyRegular_real_eq (H : ℂ → ℂ) (k : ℝ) :
    powerCauchyRegular H (k : ℂ) = H (k : ℂ) / (1 - Complex.I * (k : ℂ)) -
      ((1 + k ^ 2)⁻¹ : ℝ) • (2 * H (-Complex.I)) := by
  have hm : (1 : ℂ) - Complex.I * (k : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hp : (1 : ℂ) + Complex.I * (k : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hz : (k : ℂ) ≠ -Complex.I := by
    intro h
    have := congrArg Complex.im h
    norm_num at this
  rw [powerCauchyRegular_eq H _ hz hm hp]
  have he : ((1 : ℂ) - Complex.I * (k : ℂ)) * (1 + Complex.I * (k : ℂ)) =
      ((1 + k ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    simp [Complex.I_sq]
  rw [he]
  simp [div_eq_mul_inv, mul_comm, Complex.real_smul]

/-- If `‖z‖^α * ‖H z‖ ≤ C` on the closed lower half-plane, the regularized expression outside
radius `R ≥ 2` has norm at most `2 * C / (R^α * R) + 8 * ‖H (-Complex.I)‖ / R^2`. -/
private theorem powerCauchyRegular_norm_le (H : ℂ → ℂ) (α C R : ℝ)
    (hα : 0<α) (hC : 0≤C) (hR : 2≤R)
    (hH : ∀ z : ℂ,z.im≤0→‖z‖^α*‖H z‖≤C)
    (z : ℂ) (hz : z.im≤0) (hn : R≤‖z‖) :
    ‖powerCauchyRegular H z‖≤2*C/(R^α*R)+8*‖H (-Complex.I)‖/R^2 := by
  have hR0 : 0<R := by linarith
  have hm : R/2≤‖(1:ℂ)-Complex.I*z‖ := by
    have hh := norm_sub_norm_le (Complex.I*z) (1:ℂ)
    rw [norm_sub_rev] at hh
    simp only [norm_mul,Complex.norm_I,one_mul,norm_one] at hh
    linarith
  have hp : R/2≤‖(1:ℂ)+Complex.I*z‖ := by
    have hh := norm_sub_norm_le (Complex.I*z) (-1:ℂ)
    simp only [norm_mul,Complex.norm_I,one_mul,norm_neg,norm_one,sub_neg_eq_add] at hh
    rw [add_comm] at hh
    linarith
  have hm0 : (1:ℂ)-Complex.I*z≠0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hm)
  have hp0 : (1:ℂ)+Complex.I*z≠0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hp)
  have hz0 : z≠-Complex.I := by intro he;rw [he] at hn;norm_num at hn;linarith
  have hpR : 0<R^α := Real.rpow_pos_of_pos hR0 α
  have hbound : ‖H z‖≤C/R^α := by
    apply (le_div_iff₀ hpR).mpr
    calc _≤‖z‖^α*‖H z‖ := by
           rw [mul_comm]
           exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hR0.le hn hα.le) (norm_nonneg _)
         _≤C := hH z hz
  rw [powerCauchyRegular_eq H z hz0 hm0 hp0]
  apply (norm_sub_le _ _).trans
  simp only [norm_div,norm_mul]
  rw [show ‖(2:ℂ)‖=2 by norm_num]
  have h1 : ‖H z‖ / ‖(1:ℂ)-Complex.I*z‖ ≤ (C/R^α)/(R/2) :=
    div_le_div₀ (by positivity) hbound (by positivity : 0<R/2) hm
  have h2 : 2*‖H (-Complex.I)‖/(‖(1:ℂ)-Complex.I*z‖*‖(1:ℂ)+Complex.I*z‖)≤
      (2*‖H (-Complex.I)‖)/((R/2)*(R/2)) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul hm hp (by positivity) (norm_nonneg _))
  apply (add_le_add h1 h2).trans_eq
  field_simp
  ring

/-- For differentiable `H` with the stated power decay, the real-segment integral of its
regularization has norm at most `8 * C / R^α + 32 * ‖H (-Complex.I)‖ / R` when `R ≥ 2`. -/
private theorem powerCauchyRegular_rectangle_norm_le (H : ℂ → ℂ) (α C R : ℝ)
    (hα : 0<α) (hC : 0≤C) (hR : 2 ≤ R)
    (hd : DifferentiableOn ℂ H {z : ℂ | z.im ≤ 0})
    (hH : ∀ z : ℂ, z.im ≤ 0 →
      ‖z‖^α*‖H z‖≤C) :
    ‖∫ k in -R..R, powerCauchyRegular H (k : ℂ)‖ ≤
      8*C/R^α+32*‖H (-Complex.I)‖/R := by
  let g := powerCauchyRegular H
  let B := 2*C/(R^α*R)+8*‖H (-Complex.I)‖/R^2
  have hR0 : 0 < R := by linarith
  have hg := powerCauchyRegular_differentiableOn H hd
  have hh := Complex.integral_boundary_rect_eq_zero_of_differentiableOn g
    ((-R : ℂ) - (R : ℂ) * Complex.I) (R : ℂ) (hg.mono (by
      intro z hz
      have hy : z.im ∈ uIcc (-R) 0 := by simpa using! hz.2
      rw [uIcc_of_le (by linarith)] at hy
      exact hy.2))
  simp at hh
  have heq : (∫ k in -R..R, g (k : ℂ)) =
      (∫ k in -R..R, g ((k : ℂ) + (-R : ℂ) * Complex.I)) +
      Complex.I • (∫ y in -R..0, g ((R : ℂ) + (y : ℂ) * Complex.I)) -
      Complex.I • (∫ y in -R..0, g ((-R : ℂ) + (y : ℂ) * Complex.I)) := by
    simp only [neg_mul, smul_eq_mul, sub_eq_add_neg] at hh ⊢
    linear_combination -hh
  have hb : ‖∫ k in -R..R, g ((k : ℂ) + (-R : ℂ) * Complex.I)‖ ≤ B * (2 * R) := by
    have hbound (k : ℝ) : ‖g ((k : ℂ) + (-R : ℂ) * Complex.I)‖ ≤ B := by
      apply powerCauchyRegular_norm_le H α C R hα hC hR hH
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.neg_re, Complex.ofReal_re,
          Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
        linarith
      · have hh := Complex.abs_im_le_norm ((k : ℂ) + (-R : ℂ) * Complex.I)
        simpa [abs_of_pos hR0] using! hh
    have hn := intervalIntegral.norm_integral_le_of_norm_le_const
      (fun k (_ : k ∈ uIoc (-R) R) => hbound k)
    simpa only [show R - -R = 2 * R by ring, abs_of_pos (by positivity : 0 < 2 * R)] using! hn
  have hv (x : ℝ) (hx : |x| = R) :
      ‖∫ y in -R..0, g ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ B * R := by
    have hbound (y : ℝ) (hy : y ∈ uIoc (-R) 0) :
        ‖g ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ B := by
      rw [uIoc_of_le (by linarith)] at hy
      apply powerCauchyRegular_norm_le H α C R hα hC hR hH
      · simpa using! hy.2
      · have hh := Complex.abs_re_le_norm ((x : ℂ) + (y : ℂ) * Complex.I)
        simpa [hx] using! hh
    have hn := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    simpa only [zero_sub, neg_neg, abs_of_pos hR0] using! hn
  have hr := hv R (abs_of_pos hR0)
  have hl : ‖∫ y in -R..0, g ((-R : ℂ) + (y : ℂ) * Complex.I)‖ ≤ B * R := by
    simpa only [Complex.ofReal_neg] using! hv (-R) (by simp [abs_of_pos hR0])
  rw [heq]
  calc
    _ ≤ ‖(∫ k in -R..R, g ((k : ℂ) + (-R : ℂ) * Complex.I)) +
        Complex.I • (∫ y in -R..0, g ((R : ℂ) + (y : ℂ) * Complex.I))‖ +
        ‖Complex.I • (∫ y in -R..0, g ((-R : ℂ) + (y : ℂ) * Complex.I))‖ := norm_sub_le _ _
    _ ≤ (‖∫ k in -R..R, g ((k : ℂ) + (-R : ℂ) * Complex.I)‖ +
        ‖Complex.I • (∫ y in -R..0, g ((R : ℂ) + (y : ℂ) * Complex.I))‖) +
        ‖Complex.I • (∫ y in -R..0, g ((-R : ℂ) + (y : ℂ) * Complex.I))‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ = (‖∫ k in -R..R, g ((k : ℂ) + (-R : ℂ) * Complex.I)‖ +
        ‖∫ y in -R..0, g ((R : ℂ) + (y : ℂ) * Complex.I)‖) +
        ‖∫ y in -R..0, g ((-R : ℂ) + (y : ℂ) * Complex.I)‖ := by
      simp only [norm_smul, Complex.norm_I, one_mul]
    _ ≤ (B * (2 * R) + B * R) + B * R := add_le_add (add_le_add hb hr) hl
    _ = _ := by dsimp [B]; field_simp; ring

/-- A function complex differentiable on the closed lower half-plane has a continuous
Cauchy-weighted restriction to the real axis. -/
theorem power_kernel_weight_continuous (f : ℂ→ℂ)
    (hf : DifferentiableOn ℂ f {z : ℂ|z.im≤0}) :
    Continuous (fun k : ℝ=>f (k:ℂ)/(1-Complex.I*(k:ℂ))) := by
  have hc : Continuous (fun k : ℝ=>f (k:ℂ)) :=
    hf.continuousOn.comp_continuous Complex.continuous_ofReal (by intro k;simp)
  apply hc.div (continuous_const.sub (continuous_const.mul Complex.continuous_ofReal))
  intro k h
  have hh := congrArg Complex.re h
  norm_num at hh

/-- A power bound `‖z‖^α * ‖f z‖ ≤ C` on the lower half-plane gives the stated integrable power
envelope for the Cauchy-weighted boundary value when `‖k‖ ≥ 1`. -/
private theorem power_kernel_weight_tail (f : ℂ→ℂ) (α C : ℝ)
    (hα : 0<α) (hC : 0≤C)
    (hdecay : ∀ z : ℂ,z.im≤0→‖z‖^α*‖f z‖≤C) (k : ℝ) (hk : 1≤‖k‖) :
    ‖f (k:ℂ)/(1-Complex.I*(k:ℂ))‖≤
      C*2^(α+1)*(1+‖k‖)^(-(α+1)) := by
  have hk0 : 0<‖k‖ := lt_of_lt_of_le zero_lt_one hk
  have hka : 0<‖k‖^α := Real.rpow_pos_of_pos hk0 α
  have hd := hdecay (k:ℂ) (by simp)
  rw [Complex.norm_real] at hd
  have hf : ‖f (k:ℂ)‖≤C/‖k‖^α := (le_div_iff₀ hka).mpr (by nlinarith [hd])
  have hden : ‖k‖≤‖(1:ℂ)-Complex.I*(k:ℂ)‖ := by
    have hh := Complex.abs_im_le_norm ((1:ℂ)-Complex.I*(k:ℂ))
    simpa [Real.norm_eq_abs] using! hh
  have hstep : ‖f (k:ℂ)/(1-Complex.I*(k:ℂ))‖≤C/‖k‖^(α+1) := by
    rw [norm_div]
    apply (div_le_div₀ (by positivity) hf hk0 hden).trans_eq
    rw [Real.rpow_add hk0,Real.rpow_one,div_div]
  have hmodel0 : 0<(1+‖k‖)^(α+1) := Real.rpow_pos_of_pos (by positivity) _
  have hbase0 : 0<‖k‖^(α+1) := Real.rpow_pos_of_pos hk0 _
  have hmodel : (1+‖k‖)^(α+1)≤2^(α+1)*‖k‖^(α+1) := by
    calc _≤(2*‖k‖)^(α+1) := Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
         _=_ := Real.mul_rpow (by norm_num) hk0.le
  have hratio : (1+‖k‖)^(α+1)/‖k‖^(α+1)≤2^(α+1) := (div_le_iff₀ hbase0).mpr hmodel
  apply hstep.trans
  rw [Real.rpow_neg (by positivity),← div_eq_mul_inv]
  apply (le_div_iff₀ hmodel0).mpr
  calc _=C*((1+‖k‖)^(α+1)/‖k‖^(α+1)) := by ring
       _≤C*2^(α+1) := mul_le_mul_of_nonneg_left hratio hC

/-- A complex differentiable lower-half-plane kernel with positive-order power decay has an
integrable Cauchy-weighted real boundary value. -/
theorem power_kernel_weight_integrable (f : ℂ→ℂ) (α C : ℝ)
    (hα : 0<α) (hC : 0≤C) (hf : DifferentiableOn ℂ f {z : ℂ|z.im≤0})
    (hdecay : ∀ z : ℂ,z.im≤0→‖z‖^α*‖f z‖≤C) :
    Integrable (fun k : ℝ=>f (k:ℂ)/(1-Complex.I*(k:ℂ))) := by
  have hi : Integrable (fun k : ℝ=>(1+‖k‖)^(-(α+1))) :=
    integrable_one_add_norm (by simpa using! hα)
  apply (power_kernel_weight_continuous f hf).locallyIntegrable.integrable_of_isBigO_cocompact _
      (hi.integrableAtFilter (cocompact ℝ))
  apply Asymptotics.IsBigO.of_bound (C*2^(α+1))
  filter_upwards [(tendsto_norm_cocompact_atTop : Tendsto (fun k : ℝ=>‖k‖) (cocompact ℝ) atTop).eventually (eventually_ge_atTop (1:ℝ))] with k hk
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact power_kernel_weight_tail f α C hα hC hdecay k hk

/-- For a complex differentiable kernel with the stated positive-order power decay and boundary
integrability, the Cauchy-weighted real-line integral equals `2 * Real.pi * H (-Complex.I)`. -/
theorem power_kernel_lower_cauchy_integral (H : ℂ→ℂ) (α C : ℝ)
    (hα : 0<α) (hC : 0≤C) (hd : DifferentiableOn ℂ H {z : ℂ|z.im≤0})
    (hH : ∀ z : ℂ,z.im≤0→‖z‖^α*‖H z‖≤C)
    (hi : Integrable (fun k : ℝ=>H (k:ℂ)/(1-Complex.I*(k:ℂ)))) :
    (∫ k : ℝ,H (k:ℂ)/(1-Complex.I*(k:ℂ)))=(2*Real.pi:ℂ)*H (-Complex.I) := by
  have hr : Integrable (fun k : ℝ=>((1+k^2)⁻¹:ℝ) • (2*H (-Complex.I))) :=
    integrable_inv_one_add_sq.smul_const _
  have hg : Integrable (fun k : ℝ=>powerCauchyRegular H (k:ℂ)) := by
    apply (hi.sub hr).congr
    exact Eventually.of_forall (fun k=>(powerCauchyRegular_real_eq H k).symm)
  have ht := intervalIntegral_tendsto_integral hg
    (tendsto_neg_atTop_atBot : Tendsto (fun R : ℝ=>-R) atTop atBot)
    (tendsto_id : Tendsto (fun R : ℝ=>R) atTop atTop)
  have hpow : Tendsto (fun R : ℝ=>R^α) atTop atTop := tendsto_rpow_atTop hα
  have hinv : Tendsto (fun R : ℝ=>32*‖H (-Complex.I)‖/R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hlim : Tendsto (fun R : ℝ=>8*C/R^α+32*‖H (-Complex.I)‖/R) atTop (𝓝 0) := by
    simpa only [add_zero] using! (tendsto_const_nhds.div_atTop hpow).add hinv
  have hzlim : Tendsto (fun R : ℝ=>∫ k in -R..R,powerCauchyRegular H (k:ℂ)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_ge_atTop (2:ℝ)] with R hR
    exact powerCauchyRegular_rectangle_norm_le H α C R hα hC hR hd hH
  have hz : (∫ k : ℝ,powerCauchyRegular H (k:ℂ))=0 := tendsto_nhds_unique ht hzlim
  have heq : (∫ k : ℝ,powerCauchyRegular H (k:ℂ))=
      (∫ k : ℝ,H (k:ℂ)/(1-Complex.I*(k:ℂ)))-Real.pi • (2*H (-Complex.I)) := by
    simp_rw [powerCauchyRegular_real_eq]
    rw [integral_sub hi hr,integral_smul_const,integral_univ_inv_one_add_sq]
  rw [heq] at hz
  have he := sub_eq_zero.mp hz
  simpa only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_ofNat,mul_assoc,mul_comm,mul_left_comm] using! he
end Qatlib.Concepts.LchsSimulation.LchsRep
