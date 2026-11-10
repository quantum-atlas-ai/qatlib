/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.Kernel.NearExponentialLchsKernel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Qatlib.Concepts.LchsSimulation.Kernel

open MeasureTheory Set
open scoped Classical ComplexOrder
set_option warningAsError false

theorem highKernel_fourier_integrable (β x : ℝ) (hβ : 0 < β) (hβ1 : β < 1) :
    Integrable (fun k : ℝ => highKernelG β k *
      Complex.exp (-Complex.I * (k : ℂ) * (x : ℂ))) := by
  have hg := (near_exponential_kernel_analytic_normalization β hβ hβ1).2.2.1
  have he : Continuous (fun k : ℝ => Complex.exp (-Complex.I * (k : ℂ) * (x : ℂ))) :=
    Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)
  apply hg.norm.mono' ((highKernelG_continuous β).mul he).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro k
  change ‖highKernelG β k * Complex.exp (-Complex.I * (k : ℂ) * (x : ℂ))‖ ≤ ‖highKernelG β k‖
  rw [norm_mul, Complex.norm_exp]
  simp

theorem near_exponential_kernel_scalar_semigroup_consumer :
    ∀ (β x : ℝ), 0 < β → β < 1 → 0 ≤ x →
      Integrable (fun k : ℝ => highKernelG β k *
        Complex.exp (-Complex.I * (k : ℂ) * (x : ℂ))) ∧
      (∫ k : ℝ, highKernelG β k * Complex.exp (-Complex.I * (k : ℂ) * (x : ℂ))) =
        (Real.exp (-x) : ℂ) := by
  intro β x hβ hβ1 hx
  have hi := highKernel_fourier_integrable β x hβ hβ1
  refine ⟨hi, ?_⟩
  let H := fun z : ℂ => highKernelF β z * Complex.exp (-Complex.I * z * (x : ℂ))
  have hH : DifferentiableOn ℂ H {z : ℂ | z.im ≤ 0} := by
    intro z hz
    exact ((highKernelF_analyticAt β z hz).mul
      ((analyticAt_const.mul analyticAt_id).mul analyticAt_const).cexp).differentiableAt.differentiableWithinAt
  have hbound (z : ℂ) (hz : z.im ≤ 0) :
      ‖H z‖ ≤ (1 / highKernelC β) * Real.exp
        (-(Real.cos (β * Real.pi / 2)) * ‖1 + Complex.I * z‖ ^ β) := by
    have he : ‖Complex.exp (-Complex.I * z * (x : ℂ))‖ ≤ 1 := by
      rw [Complex.norm_exp, Real.exp_le_one_iff]
      simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, neg_mul, one_mul, mul_zero, sub_zero, zero_sub, zero_add]
      nlinarith
    dsimp [H]
    rw [norm_mul]
    apply (mul_le_of_le_one_right (norm_nonneg (highKernelF β z)) he).trans
    simpa only [neg_mul, mul_neg, div_eq_mul_inv, one_mul, mul_comm] using!
        highKernelF_norm_le β hβ hβ1 z hz
  have hInt : Integrable (fun k : ℝ => H (k : ℂ) / (1 - Complex.I * (k : ℂ))) := by
    apply hi.congr
    exact Filter.Eventually.of_forall (fun k => by dsimp [H, highKernelG]; ring)
  have hv := highKernel_lower_cauchy_integral H β (Real.cos (β * Real.pi / 2))
    (1 / highKernelC β) hβ (highKernel_cos_pos β hβ hβ1)
    (by have := highKernelC_pos β; positivity) hH hbound hInt
  have hp : Complex.exp (-Complex.I * (-Complex.I) * (x : ℂ)) = (Real.exp (-x) : ℂ) := by
    simp [mul_neg, neg_mul, Complex.I_mul_I]
  calc
    _ = ∫ k : ℝ, H (k : ℂ) / (1 - Complex.I * (k : ℂ)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun k => by dsimp [H, highKernelG]; ring)
    _ = (2 * Real.pi : ℂ) * H (-Complex.I) := hv
    _ = ((2 * Real.pi : ℂ) * highKernelF β (-Complex.I)) * (Real.exp (-x) : ℂ) := by
      dsimp [H]
      rw [hp]
      ring
    _ = _ := by rw [highKernelF_pole_value, one_mul]

end Qatlib.Concepts.LchsSimulation.Kernel
