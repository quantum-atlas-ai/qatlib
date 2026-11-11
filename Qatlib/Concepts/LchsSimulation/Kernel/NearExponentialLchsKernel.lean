/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.TimeOrdered.TimeOrderedConsumers
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Near-exponential analytic kernels for LCHS

`highKernelF` is built from a principal complex power, and `highKernelG` is its Cauchy-weighted
real boundary value. The module proves analyticity, normalization, integrability, and
quantitative unitary-weighted tail bounds, with an explicit cutoff for any positive precision.
See [AnChildsLin2026] for the mathematical setting.

## Main statements

* `near_exponential_kernel_analytic_normalization`: For `0 < β < 1`, the kernel numerator is
  analytic in the open lower half-plane and continuous on its closure, and `highKernelG β` is
  integrable with integral one.
* `near_exponential_kernel_actual_unitary_tail`: For `0 < β < 1` and `K ≥ 1`, the
  kernel-weighted integral of a continuous unitary family is entrywise integrable and its
  truncation error is at most `(highKernelTailC β / K) * exp (-K^β * cos (β * Real.pi / 2) /
  2)`.
* `near_exponential_kernel_chosen_precision_window`: For a continuous unitary family and
  positive `ε`, the cutoff `highKernelCutoff β ε` is at least one and gives kernel-weighted
  truncation error at most `ε` when `0 < β < 1`.

## References

* [An, Childs, and Lin, 2026][AnChildsLin2026]
-/


open Qatlib.Foundations.OperatorErrors.OperatorError

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Qatlib.Concepts.LchsSimulation.Kernel

open MeasureTheory Set
open Filter
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder Topology
set_option warningAsError false

/-- The positive normalization factor `2 * Real.pi * Real.exp (-(2 : ℝ)^β)` for the
principal-power kernel. -/
noncomputable def highKernelC (β : ℝ) : ℝ :=
  2 * Real.pi * Real.exp (-(2 : ℝ) ^ β)

/-- The analytic kernel numerator `Complex.exp (-(1 + Complex.I * z)^β)` divided by `highKernelC
β`, using the principal complex power. -/
noncomputable def highKernelF (β : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-Complex.cpow (1 + Complex.I * z) (β : ℂ)) / (highKernelC β : ℂ)

/-- The real-axis Cauchy-weighted kernel `highKernelF β k / (1 - Complex.I * k)`. -/
noncomputable def highKernelG (β k : ℝ) : ℂ :=
  highKernelF β (k : ℂ) / (1 - Complex.I * (k : ℂ))

/-- The explicit tail-budget constant built from `ceil (1 / β)`, its factorial, `highKernelC β`,
and `Real.cos (β * Real.pi / 2)`. -/
noncomputable def highKernelTailC (β : ℝ) : ℝ :=
  let m := Nat.ceil (1 / β)
  (2 : ℝ) ^ (m + 1) * (Nat.factorial m : ℝ) /
    (highKernelC β * (Real.cos (β * Real.pi / 2)) ^ m)

/-- The integer cutoff, at least one, defined from the logarithmic tail budget for kernel
parameter `β` and requested precision `ε`. -/
noncomputable def highKernelCutoff (β ε : ℝ) : ℕ :=
  max 1 (Nat.ceil (((2 / Real.cos (β * Real.pi / 2)) *
    Real.log (max (Real.exp (Real.cos (β * Real.pi / 2) / 2))
      (highKernelTailC β / ε))) ^ (1 / β)))

/-- The normalization factor `highKernelC β` is positive for every real `β`. -/
theorem highKernelC_pos (β : ℝ) : 0 < highKernelC β := by
  exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (Real.exp_pos _)

/-- The normalization factor `highKernelC β` is nonzero. -/
theorem highKernelC_ne_zero (β : ℝ) : highKernelC β ≠ 0 :=
  (highKernelC_pos β).ne'

/-- For `z` in the closed lower half-plane, `1 + Complex.I * z` lies in the complex slit plane. -/
theorem highKernel_slitPlane (z : ℂ) (hz : z.im ≤ 0) :
    1 + Complex.I * z ∈ Complex.slitPlane := by
  apply Or.inl
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
  linarith

/-- The kernel numerator `highKernelF β` is complex analytic at every point of the closed lower
half-plane. -/
theorem highKernelF_analyticAt (β : ℝ) (z : ℂ) (hz : z.im ≤ 0) :
    AnalyticAt ℂ (highKernelF β) z := by
  have ha : AnalyticAt ℂ (fun w : ℂ => 1 + Complex.I * w) z :=
    analyticAt_const.add (analyticAt_const.mul analyticAt_id)
  exact ((ha.cpow analyticAt_const (highKernel_slitPlane z hz)).neg.cexp).div
    analyticAt_const (by exact_mod_cast highKernelC_ne_zero β)

/-- The function `highKernelF β` is analytic on a neighborhood of each point in the open lower
half-plane. -/
theorem highKernelF_analyticOnNhd (β : ℝ) :
    AnalyticOnNhd ℂ (highKernelF β) {z : ℂ | z.im < 0} := by
  intro z hz
  exact highKernelF_analyticAt β z hz.le

/-- The function `highKernelF β` is continuous on the closed lower half-plane. -/
theorem highKernelF_continuousOn (β : ℝ) :
    ContinuousOn (highKernelF β) {z : ℂ | z.im ≤ 0} := by
  intro z hz
  exact (highKernelF_analyticAt β z hz).continuousAt.continuousWithinAt

/-- The real-axis kernel `highKernelG β` is continuous. -/
theorem highKernelG_continuous (β : ℝ) : Continuous (highKernelG β) := by
  apply continuous_iff_continuousAt.mpr
  intro k
  have hn : (1 : ℂ) - Complex.I * (k : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  exact ((highKernelF_analyticAt β (k : ℂ) (by simp)).continuousAt.comp
    Complex.continuous_ofReal.continuousAt).div
      (continuous_const.sub (continuous_const.mul Complex.continuous_ofReal)).continuousAt hn

/-- For `0 < β < 1`, the number `Real.cos (β * Real.pi / 2)` is positive. -/
theorem highKernel_cos_pos (β : ℝ) (hβ : 0 < β) (hβ1 : β < 1) :
    0 < Real.cos (β * Real.pi / 2) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> nlinarith [Real.pi_pos]

/-- For `0 < β < 1`, the tail constant `highKernelTailC β` is positive. -/
theorem highKernelTailC_pos (β : ℝ) (hβ : 0 < β) (hβ1 : β < 1) :
    0 < highKernelTailC β := by
  dsimp [highKernelTailC]
  exact div_pos (mul_pos (by positivity) (by positivity))
    (mul_pos (highKernelC_pos β) (pow_pos (highKernel_cos_pos β hβ hβ1) _))

/-- The cutoff `highKernelCutoff β ε` is at least one. -/
theorem highKernelCutoff_one_le (β ε : ℝ) : 1 ≤ highKernelCutoff β ε :=
  le_max_left _ _

/-- For `0 < β < 1` and `z` in the closed right half-plane, the real part of the principal power
`z^β` is at least `‖z‖^β * Real.cos (β * Real.pi / 2)`. -/
theorem highKernel_cpow_re_lower (β : ℝ) (hβ : 0 < β) (hβ1 : β < 1)
    (z : ℂ) (hz : 0 ≤ z.re) :
    ‖z‖ ^ β * Real.cos (β * Real.pi / 2) ≤ (Complex.cpow z (β : ℂ)).re := by
  rw [Complex.cpow_eq_pow, Complex.cpow_ofReal_re]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (norm_nonneg _) _)
  rw [← Real.cos_abs (Complex.arg z * β)]
  apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
  · nlinarith [Real.pi_pos]
  · rw [abs_mul, abs_of_pos hβ]
    have := Complex.abs_arg_le_pi_div_two_iff.mpr hz
    nlinarith

/-- For `0 < β < 1`, the kernel numerator on the closed lower half-plane is bounded by the
stated stretched-exponential envelope divided by `highKernelC β`. -/
theorem highKernelF_norm_le (β : ℝ) (hβ : 0 < β) (hβ1 : β < 1)
    (z : ℂ) (hz : z.im ≤ 0) :
    ‖highKernelF β z‖ ≤
      Real.exp (-(‖1 + Complex.I * z‖ ^ β) * Real.cos (β * Real.pi / 2)) /
        highKernelC β := by
  rw [highKernelF, norm_div, Complex.norm_exp, Complex.neg_re,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (highKernelC_pos β)]
  apply div_le_div_of_nonneg_right _ (highKernelC_pos β).le
  apply Real.exp_le_exp.mpr
  have hh := highKernel_cpow_re_lower β hβ hβ1 (1 + Complex.I * z) (by
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, zero_mul, one_mul, zero_sub]
    linarith)
  linarith

/-- For `0 < β < 1`, the real-axis kernel norm is at most `exp (-|k|^β * cos (β * Real.pi / 2))
/ highKernelC β`. -/
theorem highKernelG_norm_le (β : ℝ) (hβ : 0 < β) (hβ1 : β < 1) (k : ℝ) :
    ‖highKernelG β k‖ ≤
      Real.exp (-(|k| ^ β) * Real.cos (β * Real.pi / 2)) / highKernelC β := by
  have hd : 1 ≤ ‖(1 : ℂ) - Complex.I * (k : ℂ)‖ := by
    simpa using! Complex.re_le_norm ((1 : ℂ) - Complex.I * (k : ℂ))
  have hk : |k| ≤ ‖(1 : ℂ) + Complex.I * (k : ℂ)‖ := by
    simpa using! Complex.abs_im_le_norm ((1 : ℂ) + Complex.I * (k : ℂ))
  calc
    ‖highKernelG β k‖ = ‖highKernelF β (k : ℂ)‖ /
        ‖(1 : ℂ) - Complex.I * (k : ℂ)‖ := norm_div _ _
    _ ≤ ‖highKernelF β (k : ℂ)‖ := div_le_self (norm_nonneg _) hd
    _ ≤ Real.exp (-(‖1 + Complex.I * (k : ℂ)‖ ^ β) *
        Real.cos (β * Real.pi / 2)) / highKernelC β :=
      highKernelF_norm_le β hβ hβ1 _ (by simp)
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (highKernelC_pos β).le
      apply Real.exp_le_exp.mpr
      have hp := Real.rpow_le_rpow (abs_nonneg k) hk hβ.le
      have hc := highKernel_cos_pos β hβ hβ1
      nlinarith

/-- For positive `β` and `c`, the stretched-exponential envelope `Real.exp (-c * |k|^β)` is
integrable on the real line. -/
theorem highKernel_envelope_integrable (β c : ℝ) (hβ : 0 < β) (hc : 0 < c) :
    MeasureTheory.Integrable (fun k : ℝ => Real.exp (-c * |k| ^ β)) := by
  have hp : IntegrableOn (fun k : ℝ => Real.exp (-c * k ^ β)) (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [integral_exp_neg_mul_rpow hβ hc]
    exact (mul_pos (Real.rpow_pos_of_pos hc _)
      (Real.Gamma_pos_of_pos (by positivity))).ne'
  have hr : IntegrableOn (fun k : ℝ => Real.exp (-c * |k| ^ β)) (Ioi 0) :=
    hp.congr_fun (fun k hk => by rw [abs_of_pos hk]) measurableSet_Ioi
  have hl : IntegrableOn (fun k : ℝ => Real.exp (-c * |k| ^ β)) (Iio 0) := by
    have hr' : IntegrableOn (fun k : ℝ => Real.exp (-c * |k| ^ β)) (Ioi (-(0 : ℝ))) := by
      simpa only [neg_zero] using! hr
    simpa only [abs_neg] using! hr'.comp_neg_Iio (c := (0 : ℝ))
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  exact ⟨Iff.mpr integrableOn_Iic_iff_integrableOn_Iio hl, hr⟩

/-- For `0 < β < 1`, the real-axis kernel `highKernelG β` is integrable. -/
theorem highKernelG_integrable (β : ℝ) (hβ : 0 < β) (hβ1 : β < 1) :
    MeasureTheory.Integrable (highKernelG β) := by
  apply ((highKernel_envelope_integrable β (Real.cos (β * Real.pi / 2)) hβ
    (highKernel_cos_pos β hβ hβ1)).div_const (highKernelC β)).mono'
      (highKernelG_continuous β).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun k => by
    simpa [neg_mul, mul_comm] using! highKernelG_norm_le β hβ hβ1 k)

/-- For `0 < β < 1` and positive `ε`, the explicit tail budget evaluated at `highKernelCutoff β
ε` is at most `ε`. -/
theorem highKernelCutoff_tail_le (β ε : ℝ) (hβ : 0 < β) (hβ1 : β < 1)
    (hε : 0 < ε) :
    let K : ℝ := highKernelCutoff β ε
    (highKernelTailC β / K) *
      Real.exp (-(K ^ β) * Real.cos (β * Real.pi / 2) / 2) ≤ ε := by
  let c := Real.cos (β * Real.pi / 2)
  let T := highKernelTailC β
  let B := max (Real.exp (c / 2)) (T / ε)
  let W := ((2 / c) * Real.log B) ^ (1 / β)
  let K : ℝ := highKernelCutoff β ε
  have hc : 0 < c := highKernel_cos_pos β hβ hβ1
  have hT : 0 < T := highKernelTailC_pos β hβ hβ1
  have hB : 0 < B := (Real.exp_pos (c / 2)).trans_le (le_max_left _ _)
  have hlog : c / 2 ≤ Real.log B := by
    simpa only [Real.log_exp] using!
      Real.log_le_log (Real.exp_pos (c / 2)) (le_max_left _ (T / ε))
  have harg : 0 ≤ (2 / c) * Real.log B :=
    mul_nonneg (by positivity) (by linarith)
  have hW : W ≤ K := by
    apply (Nat.le_ceil _).trans
    change (Nat.ceil W : ℝ) ≤ ((max 1 (Nat.ceil W) : ℕ) : ℝ)
    exact_mod_cast le_max_right 1 (Nat.ceil W)
  have hK : 1 ≤ K := by
    dsimp [K]
    exact_mod_cast highKernelCutoff_one_le β ε
  have hWpow : W ^ β = (2 / c) * Real.log B := by
    dsimp [W]
    rw [← Real.rpow_mul harg, one_div_mul_cancel hβ.ne', Real.rpow_one]
  have hpow : (2 / c) * Real.log B ≤ K ^ β := by
    rw [← hWpow]
    exact Real.rpow_le_rpow (Real.rpow_nonneg harg _) hW hβ.le
  have hexp : Real.exp (-(K ^ β) * c / 2) ≤ B⁻¹ := by
    rw [← Real.exp_log hB, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hpow hc.le
    have heq : c * ((2 / c) * Real.log B) = 2 * Real.log B := by
      field_simp
    rw [heq] at hh
    linarith
  have hlast : T * B⁻¹ ≤ ε := by
    rw [← div_eq_mul_inv, div_le_iff₀ hB]
    have hh := mul_le_mul_of_nonneg_right (le_max_right (Real.exp (c / 2)) (T / ε)) hε.le
    rw [div_mul_cancel₀ _ hε.ne'] at hh
    simpa only [mul_comm] using! hh
  change (T / K) * Real.exp (-(K ^ β) * c / 2) ≤ ε
  exact (mul_le_mul (div_le_self hT.le hK) hexp (Real.exp_pos _).le hT.le).trans hlast

/-- For positive `β` and `c`, the stretched-exponential envelope has integral `2 * c^(-1 / β) *
Real.Gamma (1 / β + 1)`. -/
theorem highKernel_envelope_integral (β c : ℝ) (hβ : 0 < β) (hc : 0 < c) :
    (∫ k : ℝ, Real.exp (-c * |k| ^ β)) =
      2 * c ^ (-1 / β) * Real.Gamma (1 / β + 1) := by
  let f := fun k : ℝ => Real.exp (-c * |k| ^ β)
  have hf : Integrable f := highKernel_envelope_integrable β c hβ hc
  have hp : (∫ k in Ioi (0 : ℝ), f k) = c ^ (-1 / β) * Real.Gamma (1 / β + 1) := by
    rw [← integral_exp_neg_mul_rpow hβ hc]
    exact setIntegral_congr_fun measurableSet_Ioi (fun k hk => by
      dsimp [f]
      rw [abs_of_pos hk])
  have hn : (∫ k in Iic (0 : ℝ), f k) = ∫ k in Ioi (0 : ℝ), f k := by
    simpa only [f, neg_zero, abs_neg] using! integral_comp_neg_Iic 0 f
  rw [← integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hf]
  simp only [compl_Iic, hn, hp]
  ring

/-- For `0 < β < 1`, multiplying a continuous unitary matrix family by `highKernelG β` yields
both entrywise and matrix-valued integrable functions. -/
theorem highKernel_unitary_integrable (I : Type) [Fintype I] [DecidableEq I]
    (β : ℝ) (U : ℝ → Matrix I I ℂ) (hβ : 0 < β) (hβ1 : β < 1)
    (hU : Continuous U) (hu : ∀ k, U k ∈ Matrix.unitaryGroup I ℂ) :
    (∀ i j : I, Integrable (fun k : ℝ => highKernelG β k * U k i j)) ∧
      Integrable (fun k : ℝ => highKernelG β k • U k) := by
  have hg := highKernelG_integrable β hβ hβ1
  constructor
  · intro i j
    apply hg.norm.mono' ((highKernelG_continuous β).mul (hU.matrix_elem i j)).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun k => by
      change ‖highKernelG β k * U k i j‖ ≤ ‖highKernelG β k‖
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (entry_norm_bound_of_unitary (hu k) i j))
  · have hcont : Continuous (fun k : ℝ => highKernelG β k • U k) := by
      have := highKernelG_continuous β
      fun_prop
    apply hg.norm.mono' hcont.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun k => by
      rw [norm_smul]
      exact mul_le_of_le_one_right (norm_nonneg _) (l2_norm_unitary_le_one (hu k)))

/-- Outside a cutoff `K ≥ 1`, the kernel norm is bounded by the stated product of a
cutoff-dependent stretched-exponential factor and an integrable envelope. -/
theorem highKernelG_outside_norm_le (β K k : ℝ) (hβ : 0 < β) (hβ1 : β < 1)
    (hK : 1 ≤ K) (hk : K ≤ |k|) :
    ‖highKernelG β k‖ ≤
      (Real.exp (-(K ^ β) * Real.cos (β * Real.pi / 2) / 2) /
        (highKernelC β * K)) * Real.exp (-(Real.cos (β * Real.pi / 2) / 2) * |k| ^ β) := by
  let c := Real.cos (β * Real.pi / 2)
  have hc : 0 < c := highKernel_cos_pos β hβ hβ1
  have hK0 : 0 < K := by linarith
  have hd : K ≤ ‖(1 : ℂ) - Complex.I * (k : ℂ)‖ := hk.trans (by
    simpa using! Complex.abs_im_le_norm ((1 : ℂ) - Complex.I * (k : ℂ)))
  have hf : ‖highKernelF β (k : ℂ)‖ ≤ Real.exp (-(|k| ^ β) * c) / highKernelC β := by
    apply (highKernelF_norm_le β hβ hβ1 _ (by simp)).trans
    apply div_le_div_of_nonneg_right _ (highKernelC_pos β).le
    apply Real.exp_le_exp.mpr
    have hn : |k| ≤ ‖(1 : ℂ) + Complex.I * (k : ℂ)‖ := by
      simpa using! Complex.abs_im_le_norm ((1 : ℂ) + Complex.I * (k : ℂ))
    have hp := Real.rpow_le_rpow (abs_nonneg k) hn hβ.le
    nlinarith
  have he : Real.exp (-(|k| ^ β) * c) ≤
      Real.exp (-(K ^ β) * c / 2) * Real.exp (-(c / 2) * |k| ^ β) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hp := Real.rpow_le_rpow hK0.le hk hβ.le
    nlinarith
  calc
    ‖highKernelG β k‖ = ‖highKernelF β (k : ℂ)‖ /
        ‖(1 : ℂ) - Complex.I * (k : ℂ)‖ := norm_div _ _
    _ ≤ (Real.exp (-(|k| ^ β) * c) / highKernelC β) / K :=
      div_le_div₀ (by positivity [highKernelC_pos β]) hf hK0 hd
    _ ≤ (Real.exp (-(K ^ β) * c / 2) * Real.exp (-(c / 2) * |k| ^ β)) /
        (highKernelC β * K) := by
      rw [div_div]
      exact div_le_div_of_nonneg_right he (mul_pos (highKernelC_pos β) hK0).le
    _ = _ := by dsimp [c]; ring

/-- For `0 < β < 1`, the integral of the half-rate stretched-exponential envelope is at most
`highKernelC β * highKernelTailC β`. -/
theorem highKernel_envelope_integral_le (β : ℝ) (hβ : 0 < β) (hβ1 : β < 1) :
    (∫ k : ℝ, Real.exp (-(Real.cos (β * Real.pi / 2) / 2) * |k| ^ β)) ≤
      highKernelC β * highKernelTailC β := by
  let c := Real.cos (β * Real.pi / 2)
  let m := Nat.ceil (1 / β)
  have hc : 0 < c := highKernel_cos_pos β hβ hβ1
  have hc1 : c ≤ 1 := Real.cos_le_one _
  have hq : 1 ≤ 1 / β := (le_div_iff₀ hβ).mpr (by linarith)
  have hm : 1 / β ≤ (m : ℝ) := Nat.le_ceil _
  have hg : Real.Gamma (1 / β + 1) ≤ (Nat.factorial m : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial]
    exact Real.Gamma_strictMonoOn_Ici.monotoneOn (by change 2 ≤ 1 / β + 1; linarith)
      (by change 2 ≤ (m : ℝ) + 1; linarith) (by linarith)
  have hb : 1 ≤ 2 / c := (le_div_iff₀ hc).mpr (by linarith)
  have hp : (c / 2) ^ (-1 / β) ≤ (2 / c) ^ m := by
    rw [neg_div, Real.rpow_neg_eq_inv_rpow]
    have he : (c / 2)⁻¹ = 2 / c := by field_simp
    rw [he, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hb hm
  rw [highKernel_envelope_integral β (c / 2) hβ (by positivity)]
  have hbound := mul_le_mul hp hg (Real.Gamma_pos_of_pos (by positivity)).le
    (by positivity : 0 ≤ (2 / c) ^ m)
  have hfinal := mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 2)
  convert! hfinal using 1
  · ring
  · dsimp [highKernelTailC]
    change highKernelC β * (2 ^ (m + 1) * (Nat.factorial m : ℝ) /
      (highKernelC β * c ^ m)) = 2 * ((2 / c) ^ m * (Nat.factorial m : ℝ))
    rw [div_pow, pow_succ]
    field_simp [highKernelC_ne_zero β, hc.ne']

/-- For `0 < β < 1` and `K ≥ 1`, the kernel-weighted integral of a continuous unitary family is
entrywise integrable and its truncation error is at most `(highKernelTailC β / K) * exp
(-K^β * cos (β * Real.pi / 2) / 2)`. See [AnChildsLin2026]. -/
theorem near_exponential_kernel_actual_unitary_tail :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (β K : ℝ)
      (U : ℝ → Matrix I I ℂ), 0 < β → β < 1 → 1 ≤ K → Continuous U →
      (∀ k, U k ∈ Matrix.unitaryGroup I ℂ) →
      (∀ i j : I, Integrable (fun k : ℝ => highKernelG β k * U k i j)) ∧
      ‖(∫ k : ℝ, highKernelG β k • U k) -
        (∫ k in -K..K, highKernelG β k • U k)‖ ≤
        (highKernelTailC β / K) *
          Real.exp (-(K ^ β) * Real.cos (β * Real.pi / 2) / 2) := by
  intro I _ _ β K U hβ hβ1 hK hU hu
  obtain ⟨hentries, hint⟩ := highKernel_unitary_integrable I β U hβ hβ1 hU hu
  refine ⟨hentries, ?_⟩
  let c := Real.cos (β * Real.pi / 2)
  let a := Real.exp (-(K ^ β) * c / 2) / (highKernelC β * K)
  let e := fun k : ℝ => Real.exp (-(c / 2) * |k| ^ β)
  have hc : 0 < c := highKernel_cos_pos β hβ hβ1
  have hK0 : 0 < K := by linarith
  have hC := highKernelC_pos β
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have he : Integrable e := highKernel_envelope_integrable β (c / 2) hβ (by positivity)
  have hsub : (∫ k : ℝ, highKernelG β k • U k) -
      (∫ k in -K..K, highKernelG β k • U k) =
      ∫ k in (Ioc (-K) K)ᶜ, highKernelG β k • U k := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    rw [← integral_add_compl measurableSet_Ioc hint]
    abel
  rw [hsub]
  calc
    _ ≤ ∫ k in (Ioc (-K) K)ᶜ, ‖highKernelG β k • U k‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ k in (Ioc (-K) K)ᶜ, a * e k := by
      apply integral_mono_ae hint.norm.integrableOn ((he.const_mul a).integrableOn)
      apply ae_restrict_of_forall_mem measurableSet_Ioc.compl
      intro k hk
      have hkk : K ≤ |k| := by
        simp only [mem_compl_iff, mem_Ioc, not_and_or, not_lt, not_le] at hk
        rcases hk with hk | hk
        · exact le_trans (by linarith : K ≤ -k) (neg_le_abs k)
        · exact hk.le.trans (le_abs_self k)
      change ‖highKernelG β k • U k‖ ≤ a * e k
      rw [norm_smul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (l2_norm_unitary_le_one (hu k))).trans
        (highKernelG_outside_norm_le β K k hβ hβ1 hK hkk)
    _ ≤ ∫ k : ℝ, a * e k := setIntegral_le_integral (he.const_mul a)
      (Filter.Eventually.of_forall (fun k => mul_nonneg ha (Real.exp_pos _).le))
    _ = a * ∫ k : ℝ, e k := integral_const_mul _ _
    _ ≤ a * (highKernelC β * highKernelTailC β) :=
      mul_le_mul_of_nonneg_left (highKernel_envelope_integral_le β hβ hβ1) ha
    _ = _ := by dsimp [a, c]; field_simp [highKernelC_ne_zero β]

/-- For a continuous unitary family and positive `ε`, the cutoff `highKernelCutoff β ε` is at
least one and gives kernel-weighted truncation error at most `ε` when `0 < β < 1`. See
[AnChildsLin2026]. -/
theorem near_exponential_kernel_chosen_precision_window :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (β ε : ℝ)
      (U : ℝ → Matrix I I ℂ), 0 < β → β < 1 → 0 < ε → Continuous U →
      (∀ k, U k ∈ Matrix.unitaryGroup I ℂ) →
      let K : ℝ := highKernelCutoff β ε
      1 ≤ K ∧ ‖(∫ k : ℝ, highKernelG β k • U k) -
        (∫ k in -K..K, highKernelG β k • U k)‖ ≤ ε := by
  intro I _ _ β ε U hβ hβ1 hε hU hu K
  have hK : 1 ≤ K := by
    dsimp [K]
    exact_mod_cast highKernelCutoff_one_le β ε
  exact ⟨hK, (near_exponential_kernel_actual_unitary_tail I β K U hβ hβ1 hK hU hu).2.trans
    (highKernelCutoff_tail_le β ε hβ hβ1 hε)⟩

/-- The regularized lower-half-plane Cauchy expression formed from the divided slope of `H` at
`-Complex.I` and the correction `H (-Complex.I) / (1 + Complex.I * z)`. -/
private noncomputable def lowerCauchyRegular (H : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.I * dslope H (-Complex.I) z - H (-Complex.I) / (1 + Complex.I * z)

/-- If `H` is complex differentiable on the closed lower half-plane, then `lowerCauchyRegular H`
is differentiable there as well. -/
private theorem lowerCauchyRegular_differentiableOn (H : ℂ → ℂ)
    (hd : DifferentiableOn ℂ H {z : ℂ | z.im ≤ 0}) :
    DifferentiableOn ℂ (lowerCauchyRegular H) {z : ℂ | z.im ≤ 0} := by
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

/-- Away from the stated denominator zeros, `lowerCauchyRegular H` equals `H z / (1 - Complex.I
* z)` minus the explicit pole correction. -/
private theorem lowerCauchyRegular_eq (H : ℂ → ℂ) (z : ℂ)
    (hz : z ≠ -Complex.I) (hm : (1 : ℂ) - Complex.I * z ≠ 0)
    (hp : (1 : ℂ) + Complex.I * z ≠ 0) :
    lowerCauchyRegular H z = H z / (1 - Complex.I * z) -
      2 * H (-Complex.I) / ((1 - Complex.I * z) * (1 + Complex.I * z)) := by
  rw [lowerCauchyRegular, dslope_of_ne H hz]
  simp only [slope, smul_eq_mul, vsub_eq_sub]
  have hz' : z - -Complex.I ≠ 0 := sub_ne_zero.mpr hz
  field_simp
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_three]
  ring

/-- On the real axis, `lowerCauchyRegular H` equals the Cauchy-weighted boundary value minus `2
* H (-Complex.I)` times `(1 + k^2)⁻¹`. -/
private theorem lowerCauchyRegular_real_eq (H : ℂ → ℂ) (k : ℝ) :
    lowerCauchyRegular H (k : ℂ) = H (k : ℂ) / (1 - Complex.I * (k : ℂ)) -
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
  rw [lowerCauchyRegular_eq H _ hz hm hp]
  have he : ((1 : ℂ) - Complex.I * (k : ℂ)) * (1 + Complex.I * (k : ℂ)) =
      ((1 + k ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    simp [Complex.I_sq]
  rw [he]
  simp [div_eq_mul_inv, mul_comm, Complex.real_smul]

/-- Under the stated stretched-exponential bound on `H`, the regularized expression outside
radius `R ≥ 2` satisfies the explicit exponential and inverse-square norm bound. -/
private theorem lowerCauchyRegular_norm_le (H : ℂ → ℂ) (β c A R : ℝ)
    (hβ : 0 < β) (hc : 0 < c) (hA : 0 ≤ A) (hR : 2 ≤ R)
    (hH : ∀ z : ℂ, z.im ≤ 0 →
      ‖H z‖ ≤ A * Real.exp (-c * ‖1 + Complex.I * z‖ ^ β))
    (z : ℂ) (hz : z.im ≤ 0) (hn : R ≤ ‖z‖) :
    ‖lowerCauchyRegular H z‖ ≤
      2 * A * Real.exp (-c * (R / 2) ^ β) / R + 8 * ‖H (-Complex.I)‖ / R ^ 2 := by
  have hR0 : 0 < R := by linarith
  have hm : R / 2 ≤ ‖(1 : ℂ) - Complex.I * z‖ := by
    have hh := norm_sub_norm_le (Complex.I * z) (1 : ℂ)
    rw [norm_sub_rev] at hh
    simp only [norm_mul, Complex.norm_I, one_mul, norm_one] at hh
    linarith
  have hp : R / 2 ≤ ‖(1 : ℂ) + Complex.I * z‖ := by
    have hh := norm_sub_norm_le (Complex.I * z) (-1 : ℂ)
    simp only [norm_mul, Complex.norm_I, one_mul, norm_neg, norm_one, sub_neg_eq_add] at hh
    rw [add_comm] at hh
    linarith
  have hm0 : (1 : ℂ) - Complex.I * z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hm)
  have hp0 : (1 : ℂ) + Complex.I * z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hp)
  have hz0 : z ≠ -Complex.I := by
    intro he
    rw [he] at hn
    norm_num at hn
    linarith
  have hbound : ‖H z‖ ≤ A * Real.exp (-c * (R / 2) ^ β) := by
    apply (hH z hz).trans
    apply mul_le_mul_of_nonneg_left _ hA
    apply Real.exp_le_exp.mpr
    have hh := Real.rpow_le_rpow (by positivity : 0 ≤ R / 2) hp hβ.le
    nlinarith
  rw [lowerCauchyRegular_eq H z hz0 hm0 hp0]
  apply (norm_sub_le _ _).trans
  simp only [norm_div, norm_mul]
  rw [show ‖(2 : ℂ)‖ = 2 by norm_num]
  have h1 : ‖H z‖ / ‖(1 : ℂ) - Complex.I * z‖ ≤
      (A * Real.exp (-c * (R / 2) ^ β)) / (R / 2) :=
    div_le_div₀ (by positivity) hbound (by positivity) hm
  have h2 : 2 * ‖H (-Complex.I)‖ /
      (‖(1 : ℂ) - Complex.I * z‖ * ‖(1 : ℂ) + Complex.I * z‖) ≤
      (2 * ‖H (-Complex.I)‖) / ((R / 2) * (R / 2)) := by
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul hm hp (by positivity) (norm_nonneg _))
  apply (add_le_add h1 h2).trans_eq
  field_simp
  ring

/-- For differentiable `H` with the stated stretched-exponential decay, the integral of its
regularized expression over `[-R, R]` obeys the explicit exponential and inverse-radius
bound. -/
private theorem lowerCauchyRegular_rectangle_norm_le (H : ℂ → ℂ) (β c A R : ℝ)
    (hβ : 0 < β) (hc : 0 < c) (hA : 0 ≤ A) (hR : 2 ≤ R)
    (hd : DifferentiableOn ℂ H {z : ℂ | z.im ≤ 0})
    (hH : ∀ z : ℂ, z.im ≤ 0 →
      ‖H z‖ ≤ A * Real.exp (-c * ‖1 + Complex.I * z‖ ^ β)) :
    ‖∫ k in -R..R, lowerCauchyRegular H (k : ℂ)‖ ≤
      8 * A * Real.exp (-c * (R / 2) ^ β) + 32 * ‖H (-Complex.I)‖ / R := by
  let g := lowerCauchyRegular H
  let B := 2 * A * Real.exp (-c * (R / 2) ^ β) / R + 8 * ‖H (-Complex.I)‖ / R ^ 2
  have hR0 : 0 < R := by linarith
  have hg := lowerCauchyRegular_differentiableOn H hd
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
      apply lowerCauchyRegular_norm_le H β c A R hβ hc hA hR hH
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
      apply lowerCauchyRegular_norm_le H β c A R hβ hc hA hR hH
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

/-- For a complex differentiable function with the stated lower-half-plane decay and boundary
integrability, its Cauchy-weighted real-line integral equals `2 * Real.pi * H (-Complex.I)`. -/
theorem highKernel_lower_cauchy_integral (H : ℂ → ℂ) (β c A : ℝ)
    (hβ : 0 < β) (hc : 0 < c) (hA : 0 ≤ A)
    (hd : DifferentiableOn ℂ H {z : ℂ | z.im ≤ 0})
    (hH : ∀ z : ℂ, z.im ≤ 0 →
      ‖H z‖ ≤ A * Real.exp (-c * ‖1 + Complex.I * z‖ ^ β))
    (hi : Integrable (fun k : ℝ => H (k : ℂ) / (1 - Complex.I * (k : ℂ)))) :
    (∫ k : ℝ, H (k : ℂ) / (1 - Complex.I * (k : ℂ))) =
      (2 * Real.pi : ℂ) * H (-Complex.I) := by
  have hr : Integrable (fun k : ℝ => ((1 + k ^ 2)⁻¹ : ℝ) • (2 * H (-Complex.I))) :=
    integrable_inv_one_add_sq.smul_const _
  have hg : Integrable (fun k : ℝ => lowerCauchyRegular H (k : ℂ)) := by
    apply (hi.sub hr).congr
    exact Eventually.of_forall (fun k => (lowerCauchyRegular_real_eq H k).symm)
  have ht := intervalIntegral_tendsto_integral hg
    (tendsto_neg_atTop_atBot : Tendsto (fun R : ℝ => -R) atTop atBot)
    (tendsto_id : Tendsto (fun R : ℝ => R) atTop atTop)
  have hpow : Tendsto (fun R : ℝ => (R / 2) ^ β) atTop atTop :=
    (tendsto_rpow_atTop hβ).comp
      ((tendsto_div_const_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).mpr tendsto_id)
  have hexp : Tendsto (fun R : ℝ => Real.exp (-c * (R / 2) ^ β)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg (neg_lt_zero.mpr hc)).mpr hpow)
  have hinv : Tendsto (fun R : ℝ => 32 * ‖H (-Complex.I)‖ / R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hlim : Tendsto (fun R : ℝ => 8 * A * Real.exp (-c * (R / 2) ^ β) +
      32 * ‖H (-Complex.I)‖ / R) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using! (hexp.const_mul (8 * A)).add hinv
  have hzlim : Tendsto (fun R : ℝ => ∫ k in -R..R, lowerCauchyRegular H (k : ℂ))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with R hR
    exact lowerCauchyRegular_rectangle_norm_le H β c A R hβ hc hA hR hd hH
  have hz : (∫ k : ℝ, lowerCauchyRegular H (k : ℂ)) = 0 := tendsto_nhds_unique ht hzlim
  have heq : (∫ k : ℝ, lowerCauchyRegular H (k : ℂ)) =
      (∫ k : ℝ, H (k : ℂ) / (1 - Complex.I * (k : ℂ))) -
        Real.pi • (2 * H (-Complex.I)) := by
    simp_rw [lowerCauchyRegular_real_eq]
    rw [integral_sub hi hr, integral_smul_const, integral_univ_inv_one_add_sq]
  rw [heq] at hz
  have he := sub_eq_zero.mp hz
  simpa only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat, mul_assoc, mul_comm,
    mul_left_comm] using! he

/-- The normalization of `highKernelF β` gives `(2 * Real.pi) * highKernelF β (-Complex.I) = 1`. -/
theorem highKernelF_pole_value (β : ℝ) :
    (2 * Real.pi : ℂ) * highKernelF β (-Complex.I) = 1 := by
  have hp : 1 + Complex.I * (-Complex.I) = (2 : ℂ) := by
    norm_num [mul_neg, Complex.I_mul_I]
  have hc : (highKernelC β : ℂ) ≠ 0 := by exact_mod_cast highKernelC_ne_zero β
  have he : Complex.exp (-Complex.cpow (2 : ℂ) (β : ℂ)) =
      (Real.exp (-(2 : ℝ) ^ β) : ℂ) := by
    rw [Complex.cpow_eq_pow, ← Complex.ofReal_ofNat,
        ← Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2)]
    simp only [Complex.ofReal_neg, Complex.ofReal_exp]
  rw [highKernelF, hp, he]
  dsimp [highKernelC]
  push_cast
  field_simp

/-- For `0 < β < 1`, the kernel numerator is analytic in the open lower half-plane and
continuous on its closure, and `highKernelG β` is integrable with integral one. See
[AnChildsLin2026]. -/
theorem near_exponential_kernel_analytic_normalization :
    ∀ β : ℝ, 0 < β → β < 1 →
      AnalyticOnNhd ℂ (highKernelF β) {z : ℂ | z.im < 0} ∧
      ContinuousOn (highKernelF β) {z : ℂ | z.im ≤ 0} ∧
      Integrable (highKernelG β) ∧ (∫ k : ℝ, highKernelG β k) = 1 := by
  intro β hβ hβ1
  refine ⟨highKernelF_analyticOnNhd β, highKernelF_continuousOn β,
    highKernelG_integrable β hβ hβ1, ?_⟩
  have hi := highKernelG_integrable β hβ hβ1
  have hvalue := highKernel_lower_cauchy_integral (highKernelF β) β
    (Real.cos (β * Real.pi / 2)) (1 / highKernelC β) hβ
    (highKernel_cos_pos β hβ hβ1) (by have := highKernelC_pos β; positivity)
    (fun z hz => (highKernelF_analyticAt β z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => by
      simpa only [neg_mul, mul_neg, div_eq_mul_inv, one_mul, mul_comm] using!
          highKernelF_norm_le β hβ hβ1 z hz) hi
  exact hvalue.trans (highKernelF_pole_value β)

end Qatlib.Concepts.LchsSimulation.Kernel
