/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.PoissonValueExecution

set_option backward.isDefEq.respectTransparency false

/-!
# Poisson Term Error

Torus Fourier constructions for Effective Gauge.
Proves `poissonPeriod_inverse_error`, `poissonTerm_approximation_error`.
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Original `poissonPeriod_inverse_error` guarantee for the `PoissonTermError` construction; the complete source hypotheses are retained. -/
theorem poissonPeriod_inverse_error (length ell : ℝ) (hl : 5<length)
    (he : |length-physicalPeriod| ≤ ell) :
    ‖(length : ℂ)⁻¹-(physicalPeriod : ℂ)⁻¹‖ ≤ ell/30 := by
  have hl0 : 0<length := by linarith
  have hL6 : (6 : ℝ)<physicalPeriod := by dsimp only [physicalPeriod]; linarith [Real.pi_gt_three]
  have hell : 0 ≤ ell := (abs_nonneg _).trans he
  have hden : 30 ≤ length*physicalPeriod := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ length-5) (by linarith : 0 ≤ physicalPeriod-6)]
  have hid : length⁻¹-physicalPeriod⁻¹=(physicalPeriod-length)/(length*physicalPeriod) := by
    field_simp [hl0.ne',physicalPeriod_pos.ne']
  rw [← Complex.ofReal_inv,← Complex.ofReal_inv,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
    hid,abs_div,abs_of_pos (mul_pos hl0 physicalPeriod_pos),abs_sub_comm]
  exact div_le_div₀ hell he (by norm_num) hden

/-- The coefficient error multiplies the exact unit mode. The mode error
multiplies beta-hat, so there is no hidden assumption that it is unit. -/
theorem poissonTerm_approximation_error (beta betaHat mode modeHat : ℂ)
    (B E d length ell : ℝ) (hB : 0 ≤ B) (hE : 0 ≤ E) (hd : 0 ≤ d)
    (hbeta : ‖beta‖ ≤ 3*B) (herror : ‖betaHat-beta‖ ≤ 3*E)
    (hmode : ‖mode‖=1) (hmodeError : ‖modeHat-mode‖ ≤ d)
    (hlength : 5<length) (hperiod : |length-physicalPeriod| ≤ ell) :
    ‖betaHat*modeHat/(length : ℂ)-beta*mode/(physicalPeriod : ℂ)‖ ≤
      3*E/5+3*(B+E)*d/5+3*B*ell/30 := by
  have hl0 : 0<length := by linarith
  have hell : 0 ≤ ell := (abs_nonneg _).trans hperiod
  have hhat : ‖betaHat‖ ≤ 3*(B+E) := by
    have h := (norm_le_norm_sub_add betaHat beta).trans (add_le_add herror hbeta)
    linarith
  let t1 := (betaHat-beta)*mode/(length : ℂ)
  let t2 := betaHat*(modeHat-mode)/(length : ℂ)
  let t3 := beta*mode*((length : ℂ)⁻¹-(physicalPeriod : ℂ)⁻¹)
  have heq : betaHat*modeHat/(length : ℂ)-beta*mode/(physicalPeriod : ℂ)=t1+t2+t3 := by
    dsimp only [t1,t2,t3]
    simp only [div_eq_mul_inv]
    ring
  have ht1 : ‖t1‖ ≤ 3*E/5 := by
    dsimp only [t1]
    rw [norm_div,norm_mul,hmode,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hl0]
    exact div_le_div₀ (by positivity) herror (by norm_num) hlength.le
  have ht2 : ‖t2‖ ≤ 3*(B+E)*d/5 := by
    dsimp only [t2]
    rw [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hl0]
    exact div_le_div₀ (by positivity)
      (mul_le_mul hhat hmodeError (norm_nonneg _) (by positivity)) (by norm_num) hlength.le
  have ht3 : ‖t3‖ ≤ 3*B*ell/30 := by
    dsimp only [t3]
    rw [norm_mul,norm_mul,hmode,mul_one]
    have he' := mul_le_mul hbeta (poissonPeriod_inverse_error length ell hlength hperiod)
      (norm_nonneg _) (by positivity : 0 ≤ 3*B)
    exact he'.trans_eq (by ring)
  rw [heq]
  exact ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
    (add_le_add (add_le_add ht1 ht2) ht3)

end Qatlib.Concepts.EffectiveGauge.TorusFourier
