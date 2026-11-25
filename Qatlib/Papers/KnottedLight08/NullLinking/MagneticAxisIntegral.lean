/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.NullLinking.MagneticAxisGauss

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Integration along the oriented magnetic axis

The limiting axial density has an elementary antiderivative with
limits minus one and one; its improper integral is two.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.KnottedLight08.NullLinking

open MeasureTheory Filter
open scoped Topology

/-- The axial density has an antiderivative whose limits at infinity
are minus one and one. -/
private theorem hasDerivAt_axis_primitive (s : ℝ) :
    HasDerivAt (fun x : ℝ => x / Real.sqrt (x ^ 2 + 1))
      (1 / Real.sqrt (s ^ 2 + 1) ^ 3) s := by
  have hd : HasDerivAt (fun x : ℝ => x ^ 2 + 1) (2 * s) s := by
    simpa using ((hasDerivAt_id s).pow 2).add_const 1
  have hS : 0 < Real.sqrt (s ^ 2 + 1) := Real.sqrt_pos.2 (by positivity)
  have hr := (hasDerivAt_id s).div (hd.sqrt (by positivity)) hS.ne'
  convert hr using 1
  · rfl
  · let R := Real.sqrt (s ^ 2 + 1)
    have hh : R ^ 2 = s ^ 2 + 1 := Real.sq_sqrt (by positivity)
    have hR : R ≠ 0 := hS.ne'
    change 1 / R ^ 3 = (1 * R - s * (2 * s / (2 * R))) / R ^ 2
    have h : R ^ 2 - s ^ 2 = 1 := by linarith only [hh]
    conv_lhs => rw [← h]
    field_simp

/-- The axial antiderivative tends to one at the positive end. -/
private theorem tendsto_axis_primitive_atTop :
    Tendsto (fun x : ℝ => x / Real.sqrt (x ^ 2 + 1)) atTop (𝓝 1) := by
  have hc : ContinuousAt (fun x : ℝ => (Real.sqrt (1 + x ^ 2))⁻¹) 0 := by
    have hd : Continuous (fun x : ℝ => Real.sqrt (1 + x ^ 2)) := by fun_prop
    exact hd.continuousAt.inv₀ (by simp)
  have h := hc.tendsto.comp tendsto_inv_atTop_zero
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero, Real.sqrt_one, inv_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  change (Real.sqrt (1 + (x⁻¹) ^ 2))⁻¹ = x / Real.sqrt (x ^ 2 + 1)
  rw [show 1 + (x⁻¹) ^ 2 = (x ^ 2 + 1) / x ^ 2 by field_simp [hx.ne']]
  rw [Real.sqrt_div (by positivity), Real.sqrt_sq hx.le]
  exact inv_div _ _

/-- The axial antiderivative is odd and tends to minus one at the
negative end. -/
private theorem tendsto_axis_primitive_atBot :
    Tendsto (fun x : ℝ => x / Real.sqrt (x ^ 2 + 1)) atBot (𝓝 (-1)) := by
  simpa only [Function.comp_apply, neg_sq, neg_div, neg_neg] using
    (tendsto_axis_primitive_atTop.comp tendsto_neg_atBot_atTop).neg

/-- The full-line axial density integrates to two. -/
theorem integral_magnetic_axis_density :
    (∫ s : ℝ, 1 / Real.sqrt (s ^ 2 + 1) ^ 3) = 2 := by
  let g (s : ℝ) := 1 / Real.sqrt (s ^ 2 + 1) ^ 3
  have hc : Continuous g := by
    dsimp [g]
    exact continuous_const.div (by fun_prop) (fun _ => by positivity)
  have hnorm (s : ℝ) : ‖g s‖ = g s := Real.norm_of_nonneg (by dsimp [g]; positivity)
  have hlim : Tendsto (fun b : ℝ => ∫ x in -b..b, g x) atTop (𝓝 2) := by
    have h := tendsto_axis_primitive_atTop.sub (tendsto_axis_primitive_atBot.comp tendsto_neg_atTop_atBot)
    apply (show Tendsto _ _ (𝓝 (2 : ℝ)) from by norm_num at h ⊢; exact h).congr
    intro b
    simpa only [g, Function.comp_apply, neg_sq] using
      (intervalIntegral.integral_eq_sub_of_hasDerivAt (a := -b) (b := b)
        (fun x _ => hasDerivAt_axis_primitive x) (hc.intervalIntegrable (-b) b)).symm
  have hg : Integrable g := by
    apply integrable_of_intervalIntegral_norm_tendsto 2
      (fun b => (hc.intervalIntegrable (-b) b).1) tendsto_neg_atTop_atBot tendsto_id
    simpa only [hnorm] using hlim
  simpa only [g, sub_neg_eq_add, one_add_one_eq_two] using
    integral_of_hasDerivAt_of_tendsto hasDerivAt_axis_primitive hg
      tendsto_axis_primitive_atBot tendsto_axis_primitive_atTop

/-- The limiting positively oriented axis–pole Gauss kernel has total
integral one, with the pole angle traversed once. -/
theorem integral_magnetic_axis_pole_kernel :
    (∫ p : ℝ × ℝ, rescaledMagneticGaussKernel 0 p.1 p.2 ∂(volume.prod
      (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))))) = 1 := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))
  let f (s : ℝ) := (4 * Real.pi)⁻¹ * (1 / Real.sqrt (s ^ 2 + 1) ^ 3)
  change (∫ p : ℝ × ℝ, rescaledMagneticGaussKernel 0 p.1 p.2 ∂(volume.prod μ)) = _
  calc
    _ = ∫ p : ℝ × ℝ, f p.1 * (1 : ℝ) ∂(volume.prod μ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun p => by
        change rescaledMagneticGaussKernel 0 p.1 p.2 = f p.1 * 1
        rw [rescaledMagneticGaussKernel_zero]
        dsimp [f]
        ring
    _ = (∫ s : ℝ, f s) * (∫ _ : ℝ, (1 : ℝ) ∂μ) :=
      integral_prod_mul f (fun _ => (1 : ℝ))
    _ = 1 := by
      have hm : μ.real Set.univ = 2 * Real.pi := by
        simp only [μ, Measure.real, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
        exact ENNReal.toReal_ofReal (by positivity)
      rw [integral_const, hm, smul_eq_mul]
      dsimp [f]
      rw [integral_const_mul, integral_magnetic_axis_density, mul_one]
      field_simp [Real.pi_ne_zero]
      norm_num

end Qatlib.Papers.KnottedLight08.NullLinking
