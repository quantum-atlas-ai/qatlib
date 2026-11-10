/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NonhomogPDE18.InverseProfile

def modeledF (L Δ a : ℝ) : ℝ :=
  a * (1 - Real.exp (-(L ^ 2 * (a ^ 2 + Δ ^ 2 + Δ ^ 4)) / (2 * (1 + Δ ^ 2)))) /
    (Real.sqrt (1 + Δ ^ 2) * (a ^ 2 + Δ ^ 2 + Δ ^ 4))

def modeledEigenvalue (L Δ a : ℝ) : ℝ :=
  2 * a * Real.sqrt Real.pi * Δ *
      (1 - Real.exp (-(L ^ 2 * (a ^ 2 + Δ ^ 2 + Δ ^ 4)) / (2 * (1 + Δ ^ 2)))) /
    (Real.sqrt (1 + Δ ^ 2) * (a ^ 2 + Δ ^ 2 + Δ ^ 4))

theorem modeledEigenvalue_eq (L Δ a : ℝ) :
    modeledEigenvalue L Δ a = 2 * Real.sqrt Real.pi * Δ * modeledF L Δ a := by
  unfold modeledEigenvalue modeledF
  ring

theorem modeledF_atTop {Δ : ℝ} (hΔ : 0 < Δ) {a : ℝ} (ha : a ≠ 0) :
    Filter.Tendsto (fun L : ℝ => modeledF L Δ a) Filter.atTop
      (nhds (a / (Real.sqrt (1 + Δ ^ 2) * (a ^ 2 + Δ ^ 2 + Δ ^ 4)))) := by
  have hpos : 0 < a ^ 2 + Δ ^ 2 + Δ ^ 4 := by positivity
  have hd : (0 : ℝ) < 2 * (1 + Δ ^ 2) := by positivity

  have hexp : Filter.Tendsto
      (fun L : ℝ => Real.exp (-(L ^ 2 * (a ^ 2 + Δ ^ 2 + Δ ^ 4)) / (2 * (1 + Δ ^ 2))))
      Filter.atTop (nhds 0) := by
    have hsq : Filter.Tendsto (fun L : ℝ => L ^ 2) Filter.atTop Filter.atTop :=
      Filter.tendsto_pow_atTop two_ne_zero
    have hpoly : Filter.Tendsto (fun L : ℝ => L ^ 2 * (a ^ 2 + Δ ^ 2 + Δ ^ 4))
        Filter.atTop Filter.atTop := hsq.atTop_mul_const hpos
    have harg : Filter.Tendsto
        (fun L : ℝ => -(L ^ 2 * (a ^ 2 + Δ ^ 2 + Δ ^ 4)) / (2 * (1 + Δ ^ 2)))
        Filter.atTop Filter.atBot := by
      have h1 : Filter.Tendsto
          (fun L : ℝ => (-(2 * (1 + Δ ^ 2))⁻¹) * (L ^ 2 * (a ^ 2 + Δ ^ 2 + Δ ^ 4)))
          Filter.atTop Filter.atBot :=
        Filter.Tendsto.const_mul_atTop_of_neg
          (by
            have hpos : 0 < (2 * (1 + Δ ^ 2))⁻¹ := by positivity
            linarith)
          hpoly
      refine h1.congr' ?_
      filter_upwards with L
      field_simp
      try ring
    exact Real.tendsto_exp_atBot.comp harg
  have hnum : Filter.Tendsto
      (fun L : ℝ => a * (1 - Real.exp (-(L ^ 2 * (a ^ 2 + Δ ^ 2 + Δ ^ 4)) / (2 * (1 + Δ ^ 2)))))
      Filter.atTop (nhds (a * (1 - 0))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub hexp)
  have := hnum.div_const (Real.sqrt (1 + Δ ^ 2) * (a ^ 2 + Δ ^ 2 + Δ ^ 4))
  simpa [modeledF] using this

theorem modeledF_zero_precision {a : ℝ} (ha : a ≠ 0) :
    Filter.Tendsto
      (fun Δ : ℝ => a / (Real.sqrt (1 + Δ ^ 2) * (a ^ 2 + Δ ^ 2 + Δ ^ 4)))
      (nhds 0) (nhds (1 / a)) := by
  have hden0 : Real.sqrt (1 + 0 ^ 2) * (a ^ 2 + 0 ^ 2 + 0 ^ 4) ≠ 0 := by
    have h1 : Real.sqrt (1 + 0 ^ 2) ≠ 0 := by
      have hpos : 0 < Real.sqrt (1 + 0 ^ 2) :=
        Real.sqrt_pos.mpr (by norm_num)
      linarith
    have h2 : a ^ 2 + 0 ^ 2 + 0 ^ 4 ≠ 0 := by
      have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
      have hpos : 0 < a ^ 2 := lt_of_le_of_ne (sq_nonneg a) (Ne.symm ha2)
      linarith
    exact mul_ne_zero h1 h2
  have hcont : ContinuousAt
      (fun Δ : ℝ => a / (Real.sqrt (1 + Δ ^ 2) * (a ^ 2 + Δ ^ 2 + Δ ^ 4))) 0 := by
    refine ContinuousAt.div (by fun_prop) ?_ hden0
    fun_prop
  have hval : a / a ^ 2 = a⁻¹ := by
    have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
    rw [div_eq_iff ha2, pow_two, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  simpa [hval] using hcont.tendsto

end Qatlib.Papers.NonhomogPDE18.InverseProfile
