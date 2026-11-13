/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.Kernel.NearExponentialLchsKernel
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Analytic extension of the kernel modulus

`modulusExtension` extends the real-axis modulus of `highKernelG` to the strip `|z.im| < 1`.
Strip norm bounds and Cauchy estimates give explicit derivative bounds, while a separate
argument bounds the real-line modulus integral. See [AnChildsLin2026] for the mathematical
setting.

## Main statements

* `modulusExtension_ofReal`: On real inputs, `modulusExtension β` equals the complex coercion of
  the norm of `highKernelG β`.
* `modulusExtension_iteratedDeriv_le`: For `0 < β < 1`, the `p`-th complex derivative of
  `modulusExtension β` at a real point has norm at most `p.factorial * (4 / highKernelC β) / (1
  / 2)^p`.
* `highKernelG_abs_integral_le_aux`: For `0 < β < 1`, the integral of the kernel modulus is at
  most `exp(1)^2 / Real.pi * (1 + 1 / (β * cos (β * Real.pi / 2)))`.

## References

* [An, Childs, and Lin, 2026][AnChildsLin2026]
-/

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Qatlib.Concepts.LchsSimulation.Kernel

open MeasureTheory Set
open Filter
open scoped ENNReal ComplexConjugate

/-- For nonnegative `x`, `Real.exp (-x) ≤ 1 / (1 + x)`. -/
private theorem exp_neg_le_inv_one_add (x : ℝ) (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 / (1 + x) := by
  have h1 : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
  have h2 : Real.exp (-x) * (1 + x) ≤ Real.exp (-x) * Real.exp x :=
    mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) + x ≤ Real.exp x) (Real.exp_pos _).le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h2
  exact (le_div_iff₀ (by linarith : (0 : ℝ) < 1 + x)).mpr h2

/-- For `r ≥ 1 / 2`, the negative half power `r^(-1 / 2)` is at most two. -/
private theorem half_neg_rpow_le_two (r : ℝ) (hr : 1 / 2 ≤ r) :
    r ^ (-(1 / 2 : ℝ)) ≤ 2 := by
  have hr0 : (0 : ℝ) < r := by linarith
  have h4 : (1 : ℝ) ≤ 4 * r := by nlinarith
  have h5 : r⁻¹ ≤ 4 * (r * r⁻¹) := by
    calc r⁻¹ = 1 * r⁻¹ := (one_mul _).symm
      _ ≤ (4 * r) * r⁻¹ := mul_le_mul_of_nonneg_right h4 (by positivity)
      _ = 4 * (r * r⁻¹) := by ring
  rw [mul_inv_cancel₀ hr0.ne', mul_one] at h5
  rw [Real.rpow_neg_eq_inv_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_le_iff]
  exact ⟨by norm_num, h5.trans_eq (by norm_num : (4 : ℝ) = 2 ^ 2)⟩

/-- An integrable function bounded by `B` on `(0, 1)` and by `B' * k^(-(β + 1))` on `[1, ∞)` has
positive-half-line integral at most `B + B' / β` when `β > 0`. -/
private theorem integral_Ioi_le_of_bounds (β : ℝ) (hβ : 0 < β) (B B' : ℝ)
    (f : ℝ → ℝ) (hint : IntegrableOn f (Ioi (0 : ℝ)))
    (h1 : ∀ k ∈ Ioo (0 : ℝ) 1, f k ≤ B)
    (h2 : ∀ k ∈ Ici (1 : ℝ), f k ≤ B' * k ^ (-(β + 1))) :
    (∫ k in Ioi (0 : ℝ), f k) ≤ B + B' / β := by
  have ha : (-(β + 1) : ℝ) < -1 := by linarith
  have htail_int : IntegrableOn (fun k : ℝ => k ^ (-(β + 1))) (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt ha one_pos
  have htail : (∫ k in Ioi (1 : ℝ), k ^ (-(β + 1))) = 1 / β := by
    rw [integral_Ioi_rpow_of_lt ha one_pos, Real.one_rpow]
    ring
  have hfioo : IntegrableOn f (Ioo (0 : ℝ) 1) := hint.mono_set Ioo_subset_Ioi_self
  have hfioi : IntegrableOn f (Ioi (1 : ℝ)) := hint.mono_set (Ioi_subset_Ioi zero_le_one)
  have hfici : IntegrableOn f (Ici (1 : ℝ)) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr hfioi
  have hB'int : IntegrableOn (fun k : ℝ => B' * k ^ (-(β + 1))) (Ici (1 : ℝ)) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr (Integrable.const_mul htail_int B')
  have hdisj : Disjoint (Ioo (0 : ℝ) 1) (Ici (1 : ℝ)) := by
    rw [Set.disjoint_right]
    intro y hy hy2
    rw [Set.mem_Ici] at hy
    rw [Set.mem_Ioo] at hy2
    linarith
  have hvol : volume (Ioo (0 : ℝ) 1) ≠ ∞ := by
    rw [Real.volume_Ioo]
    simp
  have hB1 : (∫ _k in Ioo (0 : ℝ) 1, B) = B := by
    rw [setIntegral_const, Real.volume_real_Ioo_of_le (by norm_num), sub_zero, one_smul]
  rw [← Ioo_union_Ici_eq_Ioi (by norm_num : (0 : ℝ) < 1),
    setIntegral_union hdisj measurableSet_Ici hfioo hfici]
  calc (∫ k in Ioo (0 : ℝ) 1, f k) + (∫ k in Ici (1 : ℝ), f k)
      ≤ (∫ _k in Ioo (0 : ℝ) 1, B) + (∫ k in Ici (1 : ℝ), B' * k ^ (-(β + 1))) :=
        add_le_add
          (setIntegral_mono_on hfioo (integrableOn_const hvol) measurableSet_Ioo h1)
          (setIntegral_mono_on hfici hB'int measurableSet_Ici h2)
    _ = B + B' / β := by
        rw [hB1, integral_Ici_eq_integral_Ioi, integral_const_mul, htail]
        ring

/-- For `0 < β < 1`, the integral of the kernel modulus is at most `exp(1)^2 / Real.pi * (1 + 1
/ (β * cos (β * Real.pi / 2)))`. -/
theorem highKernelG_abs_integral_le_aux (β : ℝ) (hβ : 0 < β) (hβ1 : β < 1) :
    (∫ k : ℝ, ‖highKernelG β k‖) ≤
      (Real.exp 1) ^ 2 / Real.pi * (1 + 1 / (β * Real.cos (β * Real.pi / 2))) := by
  have hc0 : 0 < Real.cos (β * Real.pi / 2) := highKernel_cos_pos β hβ hβ1
  set c := Real.cos (β * Real.pi / 2) with hcdef
  set M2 := (Real.exp 1) ^ 2 / (2 * Real.pi) with hM2def
  have hM20 : 0 < M2 := by positivity
  have h2b : (2 : ℝ) ^ β ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (le_of_lt one_lt_two) hβ1.le
    rwa [Real.rpow_one] at h
  have hexp2 : Real.exp ((2 : ℝ) ^ β) ≤ (Real.exp 1) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hCinv : 1 / highKernelC β ≤ M2 := by
    rw [highKernelC, Real.exp_neg,
      show 1 / (2 * Real.pi * (Real.exp ((2 : ℝ) ^ β))⁻¹) =
        Real.exp ((2 : ℝ) ^ β) / (2 * Real.pi) from by field_simp]
    exact div_le_div_of_nonneg_right hexp2 (by positivity)
  have hint : Integrable (fun k : ℝ => ‖highKernelG β k‖) :=
    (highKernelG_integrable β hβ hβ1).norm
  have hPW : ∀ k : ℝ,
      ‖highKernelG β k‖ ≤ M2 / (1 + |k| ^ β * c) / max 1 |k| := by
    intro k
    have hF : ‖highKernelF β (k : ℂ)‖ ≤ Real.exp (-(|k| ^ β * c)) / highKernelC β := by
      refine (highKernelF_norm_le β hβ hβ1 (k : ℂ) (by simp)).trans ?_
      refine div_le_div_of_nonneg_right (Real.exp_le_exp.mpr ?_) (highKernelC_pos β).le
      have hn : |k| ≤ ‖(1 : ℂ) + Complex.I * (k : ℂ)‖ := by
        simpa using! Complex.abs_im_le_norm ((1 : ℂ) + Complex.I * (k : ℂ))
      have hp := Real.rpow_le_rpow (abs_nonneg k) hn hβ.le
      nlinarith
    have hd : max 1 |k| ≤ ‖(1 : ℂ) - Complex.I * (k : ℂ)‖ := by
      refine max_le ?_ ?_
      · simpa using! Complex.re_le_norm ((1 : ℂ) - Complex.I * (k : ℂ))
      · simpa using! Complex.abs_im_le_norm ((1 : ℂ) - Complex.I * (k : ℂ))
    have hE := exp_neg_le_inv_one_add (|k| ^ β * c) (by positivity)
    have hmax0 : (0 : ℝ) < max 1 |k| :=
      lt_of_lt_of_le zero_lt_one (le_max_left 1 |k|)
    have hc2 : 0 ≤ Real.exp (-(|k| ^ β * c)) / highKernelC β :=
      div_nonneg (Real.exp_nonneg _) (highKernelC_pos β).le
    have hxp : 0 < 1 + |k| ^ β * c := by
      have hx0 : 0 ≤ |k| ^ β * c := mul_nonneg (Real.rpow_nonneg (abs_nonneg k) _) hc0.le
      linarith
    have hkey' : Real.exp (-(|k| ^ β * c)) / highKernelC β ≤ M2 / (1 + |k| ^ β * c) := by
      rw [div_le_div_iff₀ (highKernelC_pos β) hxp]
      have h9 := mul_le_mul_of_nonneg_right hE hxp.le
      rw [one_div_mul_cancel hxp.ne'] at h9
      have h10 : (1 : ℝ) ≤ M2 * highKernelC β :=
        (div_le_iff₀ (highKernelC_pos β)).mp hCinv
      linarith
    calc ‖highKernelG β k‖
        = ‖highKernelF β (k : ℂ)‖ / ‖(1 : ℂ) - Complex.I * (k : ℂ)‖ := norm_div _ _
      _ ≤ (Real.exp (-(|k| ^ β * c)) / highKernelC β) / ‖(1 : ℂ) - Complex.I * (k : ℂ)‖ :=
          div_le_div_of_nonneg_right hF (norm_nonneg _)
      _ ≤ (Real.exp (-(|k| ^ β * c)) / highKernelC β) / max 1 |k| :=
          div_le_div_of_nonneg_left hc2 hmax0 hd
      _ ≤ M2 / (1 + |k| ^ β * c) / max 1 |k| :=
          div_le_div_of_nonneg_right hkey' (le_of_lt hmax0)
  have hL1 : ∀ k : ℝ, |k| < 1 → ‖highKernelG β k‖ ≤ M2 := by
    intro k hk
    refine (hPW k).trans ?_
    have h1x : (1 : ℝ) ≤ 1 + |k| ^ β * c := by
      have h : 0 ≤ |k| ^ β * c := by positivity
      linarith
    have hmx : (1 : ℝ) ≤ max 1 |k| := le_max_left _ _
    calc M2 / (1 + |k| ^ β * c) / max 1 |k| ≤ M2 / (1 + |k| ^ β * c) :=
        div_le_self (div_nonneg (le_of_lt hM20) (by positivity)) hmx
      _ ≤ M2 := div_le_self (le_of_lt hM20) h1x
  have hL2 : ∀ k : ℝ, 1 ≤ |k| → ‖highKernelG β k‖ ≤ M2 / c * |k| ^ (-(β + 1)) := by
    intro k hk
    refine (hPW k).trans ?_
    have hpos : 0 < |k| := lt_of_lt_of_le zero_lt_one hk
    have hm : max 1 |k| = |k| := max_eq_right hk
    have hp : |k| ^ β * |k| = |k| ^ (β + 1) := by
      rw [Real.rpow_add hpos β 1, Real.rpow_one]
    have hsplit : (1 + |k| ^ β * c) * |k| = |k| + c * |k| ^ (β + 1) := by
      rw [← hp]; ring
    have hck : (0 : ℝ) < c * |k| ^ (β + 1) :=
      mul_pos hc0 (Real.rpow_pos_of_pos hpos _)
    have hmul : |k| ^ (-(β + 1)) * |k| ^ (β + 1) = 1 := by
      rw [← Real.rpow_add hpos (-(β + 1)) (β + 1),
        show (-(β + 1 : ℝ)) + (β + 1) = 0 from by ring, Real.rpow_zero]
    have hst : |k| ^ (-(β + 1)) = (|k| ^ (β + 1))⁻¹ :=
      eq_inv_of_mul_eq_one_left hmul
    calc M2 / (1 + |k| ^ β * c) / max 1 |k|
        = M2 / (|k| + c * |k| ^ (β + 1)) := by rw [hm, div_div, hsplit]
      _ ≤ M2 / (c * |k| ^ (β + 1)) :=
          div_le_div_of_nonneg_left (le_of_lt hM20) hck (by linarith)
      _ = M2 / c * |k| ^ (-(β + 1)) := by
          rw [hst, ← one_div, div_mul_eq_div_mul_one_div]
  have hψcont : Continuous (fun k : ℝ => ‖highKernelG β (-k)‖) :=
    ((highKernelG_continuous β).comp continuous_neg).norm
  have hψint : Integrable (fun k : ℝ => ‖highKernelG β (-k)‖) := by
    apply ((highKernel_envelope_integrable β c hβ hc0).div_const (highKernelC β)).mono'
      hψcont.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun k => by
      simpa [abs_neg, neg_mul, mul_comm] using! highKernelG_norm_le β hβ hβ1 (-k))
  have hEq : (∫ k in Iic (0 : ℝ), ‖highKernelG β k‖) =
      ∫ k in Ioi (0 : ℝ), ‖highKernelG β (-k)‖ := by
    simpa only [neg_zero, neg_neg] using!
      integral_comp_neg_Iic (0 : ℝ) (fun k => ‖highKernelG β (-k)‖)
  have hR : (∫ k in Ioi (0 : ℝ), ‖highKernelG β k‖) ≤ M2 + M2 / c / β := by
    refine integral_Ioi_le_of_bounds β hβ M2 (M2 / c) (fun k => ‖highKernelG β k‖)
      hint.integrableOn (fun k hk => ?_) (fun k hk => ?_)
    · have hk2 := mem_Ioo.mp hk
      exact hL1 k (by rw [abs_of_pos hk2.1]; exact hk2.2)
    · have hk1 : 1 ≤ k := mem_Ici.mp hk
      have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk1
      have hstep := hL2 k (by rw [abs_of_pos hk0]; exact hk1)
      rwa [abs_of_pos hk0] at hstep
  have hL' : (∫ k in Ioi (0 : ℝ), ‖highKernelG β (-k)‖) ≤ M2 + M2 / c / β := by
    refine integral_Ioi_le_of_bounds β hβ M2 (M2 / c) (fun k => ‖highKernelG β (-k)‖)
      hψint.integrableOn (fun k hk => ?_) (fun k hk => ?_)
    · have hk2 := mem_Ioo.mp hk
      exact hL1 (-k) (by rw [abs_neg, abs_of_pos hk2.1]; exact hk2.2)
    · have hk1 : 1 ≤ k := mem_Ici.mp hk
      have hk0 : 0 ≤ k := le_of_lt (lt_of_lt_of_le zero_lt_one hk1)
      have hstep := hL2 (-k) (by rw [abs_neg, abs_of_nonneg hk0]; exact hk1)
      rwa [abs_neg, abs_of_nonneg hk0] at hstep
  rw [← integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hint, compl_Iic, hEq]
  calc (∫ k in Ioi (0 : ℝ), ‖highKernelG β (-k)‖) + ∫ k in Ioi (0 : ℝ), ‖highKernelG β k‖
      ≤ 2 * (M2 + M2 / c / β) := by
        rw [two_mul]
        exact add_le_add hL' hR
    _ = (Real.exp 1) ^ 2 / Real.pi * (1 + 1 / (β * c)) := by
        rw [hM2def]
        have hE0 : (0 : ℝ) < (Real.exp 1) ^ 2 := pow_pos (Real.exp_pos 1) 2
        field_simp [Real.pi_ne_zero, hβ.ne', hc0.ne', hE0.ne']

/-- The complex extension of the real-axis kernel modulus formed from the symmetric
principal-power exponential and the two inverse square-root factors. -/
noncomputable def modulusExtension (β : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(((1 + Complex.I * z) ^ (β : ℂ) + (1 - Complex.I * z) ^ (β : ℂ)) / 2)) /
    (highKernelC β : ℂ) *
    (1 + Complex.I * z) ^ (Complex.ofReal (-(1 / 2 : ℝ))) *
    (1 - Complex.I * z) ^ (Complex.ofReal (-(1 / 2 : ℝ)))

/-- The real part of `1 + Complex.I * z` is `1 - z.im`. -/
private theorem re_add_I_mul (z : ℂ) : (1 + Complex.I * z).re = 1 - z.im := by
  simp
  ring

/-- The real part of `1 - Complex.I * z` is `1 + z.im`. -/
private theorem re_sub_I_mul (z : ℂ) : (1 - Complex.I * z).re = 1 + z.im := by
  simp

/-- The function `modulusExtension β` is analytic at every point with `|z.im| < 1`. -/
theorem modulusExtension_analyticAt (β : ℝ) {z : ℂ} (hz : |z.im| < 1) :
    AnalyticAt ℂ (modulusExtension β) z := by
  have him := abs_lt.mp hz
  have hu : 0 < (1 + Complex.I * z).re := by rw [re_add_I_mul]; linarith
  have hv : 0 < (1 - Complex.I * z).re := by rw [re_sub_I_mul]; linarith
  have au : AnalyticAt ℂ (fun w : ℂ => 1 + Complex.I * w) z :=
    analyticAt_const.add (analyticAt_const.mul analyticAt_id)
  have av : AnalyticAt ℂ (fun w : ℂ => 1 - Complex.I * w) z :=
    analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
  have pu : AnalyticAt ℂ (fun w : ℂ => (1 + Complex.I * w) ^ (β : ℂ)) z :=
    au.cpow (g := fun _ : ℂ => (β : ℝ)) analyticAt_const (Or.inl hu)
  have pv : AnalyticAt ℂ (fun w : ℂ => (1 - Complex.I * w) ^ (β : ℂ)) z :=
    av.cpow (g := fun _ : ℂ => (β : ℝ)) analyticAt_const (Or.inl hv)
  have pe : AnalyticAt ℂ (fun w : ℂ => Complex.exp
      (-(((1 + Complex.I * w) ^ (β : ℂ) + (1 - Complex.I * w) ^ (β : ℂ)) / 2))) z :=
    ((pu.add pv).div analyticAt_const two_ne_zero).neg.cexp
  have hC : ((highKernelC β : ℝ) : ℂ) ≠ 0 := by exact_mod_cast highKernelC_ne_zero β
  have p1 : AnalyticAt ℂ (fun w : ℂ =>
      (1 + Complex.I * w) ^ (Complex.ofReal (-(1 / 2 : ℝ)))) z :=
    au.cpow (g := fun _ : ℂ => Complex.ofReal (-(1 / 2 : ℝ))) analyticAt_const (Or.inl hu)
  have p2 : AnalyticAt ℂ (fun w : ℂ =>
      (1 - Complex.I * w) ^ (Complex.ofReal (-(1 / 2 : ℝ)))) z :=
    av.cpow (g := fun _ : ℂ => Complex.ofReal (-(1 / 2 : ℝ))) analyticAt_const (Or.inl hv)
  exact ((pe.div analyticAt_const hC).mul p1).mul p2

/-- On real inputs, `modulusExtension β` equals the complex coercion of the norm of `highKernelG
β`. -/
theorem modulusExtension_ofReal (β : ℝ) (k : ℝ) :
    modulusExtension β (k : ℂ) = ((‖highKernelG β k‖ : ℝ) : ℂ) := by
  have hzc : conj ((1 : ℂ) + Complex.I * (k : ℂ)) = 1 - Complex.I * (k : ℂ) := by
    simp
    ring
  have hre : ((1 : ℂ) + Complex.I * (k : ℂ)).re = 1 := by simp
  have harg : ((1 : ℂ) + Complex.I * (k : ℂ)).arg ≠ Real.pi := by
    intro h
    rw [Complex.arg_eq_pi_iff] at h
    linarith
  have h1 : (1 - Complex.I * (k : ℂ)) ^ (β : ℂ) =
      conj (((1 : ℂ) + Complex.I * (k : ℂ)) ^ (β : ℂ)) := by
    rw [← hzc, Complex.conj_cpow _ (β : ℂ) harg, Complex.conj_ofReal]
  have h2 : (1 - Complex.I * (k : ℂ)) ^ (Complex.ofReal (-(1 / 2 : ℝ))) =
      conj (((1 : ℂ) + Complex.I * (k : ℂ)) ^ (Complex.ofReal (-(1 / 2 : ℝ)))) := by
    rw [← hzc, Complex.conj_cpow _ _ harg, Complex.conj_ofReal]
  have hz0 : 0 < ‖(1 : ℂ) + Complex.I * (k : ℂ)‖ := by
    refine norm_pos_iff.mpr ?_
    intro h
    have hre' := congrArg Complex.re h
    simp at hre'
  have hnorm : Complex.normSq (((1 : ℂ) + Complex.I * (k : ℂ)) ^
      (Complex.ofReal (-(1 / 2 : ℝ)))) = ‖(1 : ℂ) + Complex.I * (k : ℂ)‖⁻¹ := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_cpow_real, pow_two,
      ← Real.rpow_add hz0 (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ)),
      show (-(1 / 2 : ℝ)) + (-(1 / 2 : ℝ)) = -1 from by norm_num,
      Real.rpow_neg_eq_inv_rpow, Real.rpow_one]
  have hR : ‖highKernelG β k‖ =
      Real.exp (-(((1 : ℂ) + Complex.I * (k : ℂ)) ^ (β : ℂ)).re) /
        (highKernelC β * ‖(1 : ℂ) + Complex.I * (k : ℂ)‖) := by
    rw [highKernelG, highKernelF, norm_div, norm_div, Complex.norm_exp, Complex.neg_re,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (highKernelC_pos β), ← hzc,
      Complex.norm_conj, div_div, Complex.cpow_eq_pow]
  rw [modulusExtension, h1, h2, Complex.add_conj,
    show -((Complex.ofReal (2 * (((1 : ℂ) + Complex.I * (k : ℂ)) ^ (β : ℂ)).re : ℝ)) /
        (2 : ℂ)) =
      Complex.ofReal (-((((1 : ℂ) + Complex.I * (k : ℂ)) ^ (β : ℂ)).re : ℝ)) from by
      push_cast; ring,
    mul_assoc, Complex.mul_conj, hnorm, hR, ← Complex.ofReal_exp]
  push_cast
  rw [div_eq_mul_inv, mul_assoc, ← mul_inv, ← div_eq_mul_inv]

/-- For `0 < β < 1` and `|z.im| ≤ 1 / 2`, the extension norm is at most `4 / highKernelC β`. -/
theorem modulusExtension_norm_le (β : ℝ) (hβ : 0 < β) (hβ1 : β < 1) {z : ℂ}
    (hz : |z.im| ≤ 1 / 2) :
    ‖modulusExtension β z‖ ≤ 4 / highKernelC β := by
  have him := abs_le.mp hz
  have hc := highKernel_cos_pos β hβ hβ1
  have hu0 : 0 ≤ (1 + Complex.I * z).re := by rw [re_add_I_mul]; linarith
  have hv0 : 0 ≤ (1 - Complex.I * z).re := by rw [re_sub_I_mul]; linarith
  have hu1 : 1 / 2 ≤ ‖1 + Complex.I * z‖ := by
    have h := Complex.re_le_norm (1 + Complex.I * z)
    rw [re_add_I_mul] at h
    linarith
  have hv1 : 1 / 2 ≤ ‖1 - Complex.I * z‖ := by
    have h := Complex.re_le_norm (1 - Complex.I * z)
    rw [re_sub_I_mul] at h
    linarith
  have hu := highKernel_cpow_re_lower β hβ hβ1 _ hu0
  have hv := highKernel_cpow_re_lower β hβ hβ1 _ hv0
  have hu' : 0 ≤ ((1 + Complex.I * z) ^ (β : ℂ)).re :=
    (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hc.le).trans hu
  have hv' : 0 ≤ ((1 - Complex.I * z) ^ (β : ℂ)).re :=
    (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hc.le).trans hv
  have hexp : ‖Complex.exp (-(((1 + Complex.I * z) ^ (β : ℂ) +
      (1 - Complex.I * z) ^ (β : ℂ)) / 2))‖ ≤ 1 := by
    rw [Complex.norm_exp, Real.exp_le_one_iff, Complex.neg_re, Complex.div_re,
      Complex.add_re]
    norm_num [Complex.normSq]
    linarith
  have hw : ∀ w : ℂ, 1 / 2 ≤ ‖w‖ →
      ‖w ^ (Complex.ofReal (-(1 / 2 : ℝ)))‖ ≤ 2 := by
    intro w hw1
    rw [Complex.norm_cpow_real]
    exact half_neg_rpow_le_two _ hw1
  have hC' : ‖((highKernelC β : ℝ) : ℂ)‖ = highKernelC β := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (highKernelC_pos β)]
  have hA : ‖Complex.exp (-(((1 + Complex.I * z) ^ (β : ℂ) +
      (1 - Complex.I * z) ^ (β : ℂ)) / 2))‖ / ‖((highKernelC β : ℝ) : ℂ)‖ ≤
      1 / highKernelC β := by
    rw [hC']
    exact div_le_div_of_nonneg_right hexp (highKernelC_pos β).le
  have hcinv0 : (0 : ℝ) ≤ 1 / highKernelC β :=
    div_nonneg zero_le_one (highKernelC_pos β).le
  calc ‖modulusExtension β z‖
      = ‖Complex.exp (-(((1 + Complex.I * z) ^ (β : ℂ) +
          (1 - Complex.I * z) ^ (β : ℂ)) / 2))‖ / ‖((highKernelC β : ℝ) : ℂ)‖ *
        ‖(1 + Complex.I * z) ^ (Complex.ofReal (-(1 / 2 : ℝ)))‖ *
        ‖(1 - Complex.I * z) ^ (Complex.ofReal (-(1 / 2 : ℝ)))‖ := by
        rw [modulusExtension, norm_mul, norm_mul, norm_div]
    _ ≤ (1 / highKernelC β) * 2 * 2 := by
        refine mul_le_mul
          (mul_le_mul hA (hw _ hu1) (norm_nonneg _) hcinv0) (hw _ hv1)
          (norm_nonneg _) (mul_nonneg hcinv0 (by norm_num))
    _ = 4 / highKernelC β := by ring

/-- For `0 < β < 1`, the `p`-th complex derivative of `modulusExtension β` at a real point has
norm at most `p.factorial * (4 / highKernelC β) / (1 / 2)^p`. -/
theorem modulusExtension_iteratedDeriv_le (β : ℝ) (hβ : 0 < β) (hβ1 : β < 1)
    (p : ℕ) (k : ℝ) :
    ‖iteratedDeriv p (modulusExtension β) (k : ℂ)‖ ≤
      p.factorial * (4 / highKernelC β) / (1 / 2) ^ p := by
  have himof : ∀ w : ℂ, ‖w - (k : ℂ)‖ ≤ 1 / 2 → |w.im| ≤ 1 / 2 := by
    intro w hw
    have h := Complex.abs_im_le_norm (w - (k : ℂ))
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at h
    exact h.trans hw
  have hdiff : DiffContOnCl ℂ (modulusExtension β) (Metric.ball (k : ℂ) (1 / 2)) := by
    apply DifferentiableOn.diffContOnCl
    intro w hw
    have hw' : w ∈ Metric.closedBall (k : ℂ) (1 / 2) :=
      Metric.closure_ball_subset_closedBall hw
    have hw2 : ‖w - (k : ℂ)‖ ≤ 1 / 2 := by
      have h1 := Metric.mem_closedBall.mp hw'
      rwa [dist_eq_norm] at h1
    exact (AnalyticAt.differentiableAt (modulusExtension_analyticAt β
      (lt_of_le_of_lt (himof w hw2) (by norm_num : (1 / 2 : ℝ) < 1)))).differentiableWithinAt
  have hsph : ∀ z ∈ Metric.sphere (k : ℂ) (1 / 2),
      ‖modulusExtension β z‖ ≤ 4 / highKernelC β := by
    intro z hz
    have h1 : ‖z - (k : ℂ)‖ = 1 / 2 := by
      have h := Metric.mem_sphere.mp hz
      rwa [dist_eq_norm] at h
    exact modulusExtension_norm_le β hβ hβ1 (himof z h1.le)
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le p one_half_pos hdiff hsph

/-- If `f` is analytic at every real point, each iterated complex derivative is analytic there,
and the iterated real derivative of the restricted real part equals its real part. -/
private theorem iteratedDeriv_re_ofReal_aux (f : ℂ → ℂ)
    (han : ∀ x : ℝ, AnalyticAt ℂ f (x : ℂ)) :
    ∀ p : ℕ, (∀ x : ℝ, AnalyticAt ℂ (iteratedDeriv p f) (x : ℂ)) ∧
      (∀ k : ℝ, iteratedDeriv p (fun x : ℝ => (f (x : ℂ)).re) k =
        (iteratedDeriv p f (k : ℂ)).re) := by
  intro p
  induction p with
  | zero =>
    refine ⟨fun x => by rw [iteratedDeriv_zero]; exact han x, fun k => by
      rw [iteratedDeriv_zero, iteratedDeriv_zero]⟩
  | succ p ih =>
    have hfun : iteratedDeriv p (fun y : ℝ => (f (y : ℂ)).re) =
        fun x : ℝ => (iteratedDeriv p f (x : ℂ)).re := funext ih.2
    refine ⟨fun x => by rw [iteratedDeriv_succ]; exact (ih.1 x).deriv, fun k => ?_⟩
    rw [iteratedDeriv_succ, iteratedDeriv_succ, hfun]
    have hd : HasDerivAt (iteratedDeriv p f)
        (deriv (iteratedDeriv p f) (k : ℂ)) (k : ℂ) :=
      ((ih.1 k).differentiableAt).hasDerivAt
    exact (hd.real_of_complex).deriv

/-- For a function analytic at every real point, taking the real part of its iterated complex
derivative agrees with iterated real differentiation of the restricted real part. -/
theorem iteratedDeriv_re_comp_ofReal_eq (f : ℂ → ℂ) (han : ∀ x : ℝ, AnalyticAt ℂ f (x : ℂ))
    (p : ℕ) (k : ℝ) :
    iteratedDeriv p (fun x : ℝ => (f (x : ℂ)).re) k = (iteratedDeriv p f (k : ℂ)).re :=
  (iteratedDeriv_re_ofReal_aux f han p).2 k

end Qatlib.Concepts.LchsSimulation.Kernel
