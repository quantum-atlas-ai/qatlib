/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.Kernel.NearExponentialLchsKernel
import Qatlib.Concepts.LchsSimulation.Kernel.NearExponentialModulusAnalytic

/-!
# Modulus bounds for the near-exponential kernel

The real-axis modulus of `highKernelG` is positive, smooth, and integrable for `0 < β < 1`.
Explicit integral and derivative estimates support coefficient-mass bounds for high-order LCHS
quadrature. See [AnChildsLin2026] for the mathematical setting.

## Main statements

* `highKernelG_abs_integral_le`: For `0 < β < 1`, the integral of the kernel modulus is at most
  `exp(1)^2 / Real.pi * (1 + 1 / (β * (1 - β)))`.
* `highKernelG_abs_deriv_le`: For `0 < β < 1` and positive `p`, the absolute value of the `p`-th
  derivative of the kernel modulus is at most `p.factorial * 32^p / highKernelC β`.

## References

* [An, Childs, and Lin, 2026][AnChildsLin2026]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.LchsSimulation.Kernel
open MeasureTheory
open scoped ContDiff

/-- The real-axis modulus of `highKernelG β` is continuous. -/
theorem highKernelG_abs_continuous (β : ℝ) : Continuous (fun k : ℝ => ‖highKernelG β k‖) :=
  (highKernelG_continuous β).norm

/-- For `0 < β < 1`, the real-axis modulus of `highKernelG β` is integrable. -/
theorem highKernelG_abs_integrable (β : ℝ) (hβ : 0 < β) (hβ1 : β < 1) :
    Integrable (fun k : ℝ => ‖highKernelG β k‖) :=
  (highKernelG_integrable β hβ hβ1).norm

/-- The modulus of `highKernelG β k` is strictly positive for every real `β` and `k`. -/
theorem highKernelG_abs_pos (β k : ℝ) : 0 < ‖highKernelG β k‖ := by
  apply norm_pos_iff.mpr
  unfold highKernelG highKernelF
  apply div_ne_zero
  · apply div_ne_zero
    · exact Complex.exp_ne_zero _
    · exact_mod_cast highKernelC_ne_zero β
  · intro hh
    have hre := congrArg Complex.re hh
    norm_num at hre

/-- The real-axis modulus of `highKernelG β` is infinitely differentiable. -/
theorem highKernelG_abs_contDiff (β : ℝ) :
    ContDiff ℝ ∞ (fun k : ℝ => ‖highKernelG β k‖) := by
  apply contDiff_iff_contDiffAt.mpr
  intro k
  have hf : ContDiffAt ℝ ∞ (fun x : ℝ => highKernelF β (x : ℂ)) k :=
    ((highKernelF_analyticAt β (k : ℂ) (by simp)).contDiffAt.restrict_scalars ℝ).comp k
      Complex.ofRealCLM.contDiff.contDiffAt
  have hd : ContDiffAt ℝ ∞ (fun x : ℝ => (1 : ℂ) - Complex.I * (x : ℂ)) k := by
    exact contDiffAt_const.sub (contDiffAt_const.mul Complex.ofRealCLM.contDiff.contDiffAt)
  have hn : (1 : ℂ) - Complex.I * (k : ℂ) ≠ 0 := by
    intro hh
    have hre := congrArg Complex.re hh
    norm_num at hre
  have hg : ContDiffAt ℝ ∞ (highKernelG β) k := by
    simpa only [highKernelG, div_eq_mul_inv] using! hf.mul (hd.inv hn)
  exact hg.norm ℂ (norm_pos_iff.mp (highKernelG_abs_pos β k))

/-- For `0 < β < 1`, the modulus of `highKernelG β k` is at most `1 / highKernelC β`. -/
theorem highKernelG_abs_le_invC (β : ℝ) (hβ : 0 < β) (hβ1 : β < 1) (k : ℝ) :
    ‖highKernelG β k‖ ≤ 1 / highKernelC β := by
  refine (highKernelG_norm_le β hβ hβ1 k).trans ?_
  apply div_le_div_of_nonneg_right _ (highKernelC_pos β).le
  apply Real.exp_le_one_iff.mpr
  have hr : 0 ≤ |k| ^ β := Real.rpow_nonneg (abs_nonneg k) β
  have hc := highKernel_cos_pos β hβ hβ1
  nlinarith

/-- For `0 < β < 1`, the integral of the kernel modulus is at most `exp(1)^2 / Real.pi * (1 + 1
/ (β * (1 - β)))`. See [AnChildsLin2026]. -/
theorem highKernelG_abs_integral_le :
    ∀ β : ℝ, 0 < β → β < 1 →
      (∫ k : ℝ, ‖highKernelG β k‖) ≤
        (Real.exp 1) ^ 2 / Real.pi * (1 + 1 / (β * (1 - β))) := by
  intro β hβ hβ1
  have hc := highKernel_cos_pos β hβ hβ1
  have hcos : 1 - β ≤ Real.cos (β * Real.pi / 2) := by
    have h := Real.le_sin_mul (by linarith : (0 : ℝ) ≤ 1 - β)
      (by linarith : (1 : ℝ) - β ≤ 1)
    rwa [show Real.pi / 2 * (1 - β) = Real.pi / 2 - β * Real.pi / 2 from by ring,
      Real.sin_pi_div_two_sub] at h
  have hE : (0 : ℝ) ≤ (Real.exp 1) ^ 2 / Real.pi :=
    div_nonneg (pow_nonneg (Real.exp_nonneg _) _) Real.pi_pos.le
  refine (highKernelG_abs_integral_le_aux β hβ hβ1).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hE
  have h2 : 1 / (β * Real.cos (β * Real.pi / 2)) ≤ 1 / (β * (1 - β)) := by
    rw [one_div_le_one_div (mul_pos hβ hc) (mul_pos hβ (sub_pos.mpr hβ1))]
    exact mul_le_mul_of_nonneg_left hcos hβ.le
  exact add_le_add (le_refl _) h2

/-- For `0 < β < 1` and positive `p`, the absolute value of the `p`-th derivative of the kernel
modulus is at most `p.factorial * 32^p / highKernelC β`. See [AnChildsLin2026]. -/
theorem highKernelG_abs_deriv_le :
    ∀ β : ℝ, 0 < β → β < 1 → ∀ p : ℕ, 1 ≤ p → ∀ k : ℝ,
      |iteratedDeriv p (fun x : ℝ => ‖highKernelG β x‖) k| ≤
        (p.factorial : ℝ) * (32 : ℝ) ^ p / highKernelC β := by
  intro β hβ hβ1 p hp k
  have h1 : ∀ x : ℝ, (modulusExtension β (x : ℂ)).re = ‖highKernelG β x‖ := by
    intro x
    rw [modulusExtension_ofReal, Complex.ofReal_re]
  have han : ∀ x : ℝ, AnalyticAt ℂ (modulusExtension β) (x : ℂ) :=
    fun x => modulusExtension_analyticAt β (by simp)
  have hfun : iteratedDeriv p (fun x : ℝ => ‖highKernelG β x‖) =
      fun x : ℝ => (iteratedDeriv p (modulusExtension β) (x : ℂ)).re := by
    rw [(funext h1).symm]
    funext x
    exact iteratedDeriv_re_comp_ofReal_eq (modulusExtension β) han p x
  rw [hfun, ← mul_div_assoc']
  have hb := modulusExtension_iteratedDeriv_le β hβ hβ1 p k
  have hinv : ((1 : ℝ) / 2) ^ p = ((2 : ℝ) ^ p)⁻¹ := by rw [one_div, inv_pow]
  calc |(iteratedDeriv p (modulusExtension β) (k : ℂ)).re| ≤
      ‖iteratedDeriv p (modulusExtension β) (k : ℂ)‖ := Complex.abs_re_le_norm _
    _ ≤ p.factorial * (4 / highKernelC β) / (1 / 2) ^ p := hb
    _ = p.factorial * (((4 : ℝ) * (2 : ℝ) ^ p) / highKernelC β) := by
        rw [hinv, div_eq_mul_inv, inv_inv, mul_assoc, div_mul_eq_mul_div]
    _ ≤ p.factorial * (((2 : ℝ) ^ 5) ^ p / highKernelC β) := by
        have h2p : (2 : ℝ) ^ (p + 2) ≤ ((2 : ℝ) ^ 5) ^ p := by
          have hle : p + 2 ≤ 5 * p := by omega
          have h9 := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hle
          rwa [pow_mul] at h9
        have h42 : (4 : ℝ) * (2 : ℝ) ^ p = (2 : ℝ) ^ (p + 2) := by
          rw [show (4 : ℝ) = (2 : ℝ) ^ 2 from by norm_num, ← pow_add, Nat.add_comm]
        rw [h42]
        exact mul_le_mul (le_refl (p.factorial : ℝ))
          (div_le_div_of_nonneg_right h2p (highKernelC_pos β).le)
          (div_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) (highKernelC_pos β).le)
          (Nat.cast_nonneg _)
    _ = p.factorial * ((32 : ℝ) ^ p / highKernelC β) := by
        rw [show ((2 : ℝ) ^ 5) ^ p = (32 : ℝ) ^ p from by
          rw [show (32 : ℝ) = (2 : ℝ) ^ 5 from by norm_num]]

end Qatlib.Concepts.LchsSimulation.Kernel
