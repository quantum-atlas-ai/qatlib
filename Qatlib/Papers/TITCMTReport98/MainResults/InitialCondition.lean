/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TITCMTReport98.MainResults.SqrtSchedule
import Qatlib.Papers.TITCMTReport98.MainResults.InverseSchedule
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TITCMTReport98.MainResults

open Complex Filter
open scoped Topology

theorem gamma_ne_zero_of_im_ne_zero (s : ℂ) (hs : s.im ≠ 0) : Complex.Gamma s ≠ 0 := by
  refine Complex.Gamma_ne_zero ?_
  intro m hm
  exact hs (by rw [hm]; simp)

theorem sqrtScheduleModeCoeff2_ne_zero (h c : ℝ) (hh : 0 < h) (hc : 0 < c) :
    sqrtScheduleModeCoeff2 h c ≠ 0 := by
  unfold sqrtScheduleModeCoeff2
  have hγ : ((c : ℂ) ^ 2 / (2 * (h : ℂ))) = ((c ^ 2 / (2 * h) : ℝ) : ℂ) := by
    push_cast
    ring
  have hG : Complex.Gamma (-(I * ((c : ℂ) ^ 2 / (2 * (h : ℂ))))) ≠ 0 := by
    refine gamma_ne_zero_of_im_ne_zero _ ?_
    rw [hγ]
    have hval : (-(I * ((c ^ 2 / (2 * h) : ℝ) : ℂ))).im = -(c ^ 2 / (2 * h)) := by
      rw [Complex.neg_im, Complex.mul_im]
      simp only [Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [hval]
    have hpos : 0 < c ^ 2 / (2 * h) := by positivity
    exact ne_of_lt (by linarith)
  have hfac : I * (h : ℂ) / (c : ℂ) ^ 2 ≠ 0 := by
    refine div_ne_zero (mul_ne_zero Complex.I_ne_zero ?_) (pow_ne_zero 2 ?_)
    · exact ofReal_ne_zero.mpr hh.ne'
    · exact ofReal_ne_zero.mpr hc.ne'
  exact mul_ne_zero hfac (inv_ne_zero hG)

theorem sqrtSchedule_mode_cancellation_exists (h c : ℝ) (hh : 0 < h) (hc : 0 < c) :
    ∃ C1 C2 : ℂ, C1 ≠ 0 ∧
      C1 * sqrtScheduleModeCoeff1 h c + C2 * sqrtScheduleModeCoeff2 h c = 0 := by
  refine ⟨sqrtScheduleModeCoeff2 h c, -sqrtScheduleModeCoeff1 h c,
    sqrtScheduleModeCoeff2_ne_zero h c hh hc, ?_⟩
  ring

theorem sqrtSchedule_A34_cancellation (h c : ℝ) (hh : 0 < h) (hc : 0 < c) (C1 : ℂ) :
    C1 * sqrtScheduleModeCoeff1 h c
      + (I * (c : ℂ) ^ 2 / (h : ℂ)
          * Complex.Gamma (-(I * ((c : ℂ) ^ 2 / (2 * (h : ℂ)))))
          / Complex.Gamma (1 / 2 - I * ((c : ℂ) ^ 2 / (2 * (h : ℂ)))) * C1)
        * sqrtScheduleModeCoeff2 h c = 0 := by
  unfold sqrtScheduleModeCoeff1 sqrtScheduleModeCoeff2
  set z : ℂ := (c : ℂ) ^ 2 / (2 * (h : ℂ)) with hz
  set g1 : ℂ := Complex.Gamma (1 / 2 - I * z) with hg1
  set g2 : ℂ := Complex.Gamma (-(I * z)) with hg2
  have hzr : z = ((c ^ 2 / (2 * h) : ℝ) : ℂ) := by
    rw [hz]
    push_cast
    ring
  have hΓ1 : g1 ≠ 0 := by
    rw [hg1]
    refine Complex.Gamma_ne_zero_of_re_pos ?_
    rw [hzr]
    have hre : (1 / 2 - I * ((c ^ 2 / (2 * h) : ℝ) : ℂ)).re = 1 / 2 := by
      have hm : (I * ((c ^ 2 / (2 * h) : ℝ) : ℂ)).re = 0 := by
        rw [Complex.mul_re]
        simp only [Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
        ring
      have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hhalf, Complex.sub_re, Complex.ofReal_re, hm]
      norm_num
    rw [hre]
    norm_num
  have hΓ2 : g2 ≠ 0 := by
    rw [hg2]
    refine gamma_ne_zero_of_im_ne_zero _ ?_
    rw [hzr]
    have hval : (-(I * ((c ^ 2 / (2 * h) : ℝ) : ℂ))).im = -(c ^ 2 / (2 * h)) := by
      rw [Complex.neg_im, Complex.mul_im]
      simp only [Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [hval]
    have hpos : 0 < c ^ 2 / (2 * h) := by positivity
    linarith
  have hconst : (I * (c : ℂ) ^ 2 / (h : ℂ)) * (I * (h : ℂ) / (c : ℂ) ^ 2) = -1 := by
    have hhC : (h : ℂ) ≠ 0 := ofReal_ne_zero.mpr hh.ne'
    have hcC : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
    field_simp
    linear_combination Complex.I_mul_I
  calc C1 * g1⁻¹
        + (I * (c : ℂ) ^ 2 / (h : ℂ) * g2 / g1 * C1) * (I * (h : ℂ) / (c : ℂ) ^ 2 * g2⁻¹)
      = C1 * g1⁻¹
        + ((I * (c : ℂ) ^ 2 / (h : ℂ)) * (I * (h : ℂ) / (c : ℂ) ^ 2))
          * (g2 * g2⁻¹) * g1⁻¹ * C1 := by
        ring
    _ = C1 * g1⁻¹ + (-1) * 1 * g1⁻¹ * C1 := by
        rw [hconst, mul_inv_cancel₀ hΓ2]
    _ = 0 := by ring

end Qatlib.Papers.TITCMTReport98.MainResults
