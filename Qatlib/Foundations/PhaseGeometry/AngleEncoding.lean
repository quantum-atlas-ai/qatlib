/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

namespace Qatlib.Foundations.PhaseGeometry.AngleEncoding

set_option autoImplicit false

noncomputable section

def phaseMean (θ : ℝ) : ℝ := (1 - Real.cos (θ / 2)) / 2

theorem phaseMean_error_le
    {θhat θ ε : ℝ}
    (hclose : |θhat - θ| ≤ ε) (h0 : 0 ≤ θhat) (hpi : θhat < Real.pi)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    |phaseMean θhat - phaseMean θ| ≤
      |Real.cos ((θhat + ε) / 2) - Real.cos (θhat / 2)| := by

  have hε4pos : 0 < ε / 4 := by linarith
  have hε4le : ε / 4 ≤ 1 / 4 := by linarith
  have hε4_le_pi2 : ε / 4 ≤ Real.pi / 2 := by nlinarith [Real.pi_gt_three]
  have hθ_le : θ ≤ θhat + ε := by
    have := (abs_le.1 hclose).1
    linarith
  have hθ_ge : θhat - ε ≤ θ := by
    have := (abs_le.1 hclose).2
    linarith

  have hmean : phaseMean θhat - phaseMean θ
      = -(Real.cos (θhat / 2) - Real.cos (θ / 2)) / 2 := by
    unfold phaseMean
    ring
  rw [hmean, abs_div, abs_neg, abs_two]

  rw [Real.cos_sub_cos, Real.cos_sub_cos]
  rw [show (θhat / 2 + θ / 2) / 2 = (θhat + θ) / 4 by ring]
  rw [show (θhat / 2 - θ / 2) / 2 = (θhat - θ) / 4 by ring]
  rw [show ((θhat + ε) / 2 + θhat / 2) / 2 = (2 * θhat + ε) / 4 by ring]
  rw [show ((θhat + ε) / 2 - θhat / 2) / 2 = ε / 4 by ring]

  have hsin_eps : 0 ≤ Real.sin (ε / 4) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hε4pos.le (by linarith [hε4_le_pi2])

  have hw_pos : 0 < (2 * θhat + ε) / 4 := by linarith [h0, hε0]
  have hw_lt_pi : (2 * θhat + ε) / 4 < Real.pi := by
    have hlt : (2 * θhat + ε) / 4 < (2 * Real.pi + ε) / 4 := by
      apply div_lt_div_of_pos_right _ (by norm_num)
      linarith [hpi]
    have h2 : (2 * Real.pi + ε) / 4 = Real.pi / 2 + ε / 4 := by ring
    rw [h2] at hlt
    have h3 : Real.pi / 2 + ε / 4 ≤ Real.pi := by nlinarith [Real.pi_gt_three, hε1]
    linarith
  have hsinw : 0 < Real.sin ((2 * θhat + ε) / 4) :=
    Real.sin_pos_of_pos_of_lt_pi hw_pos hw_lt_pi

  have hv_abs : |(θhat - θ) / 4| ≤ ε / 4 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    exact div_le_div_of_nonneg_right hclose (by norm_num)
  have hA : |Real.sin ((θhat - θ) / 4)| ≤ Real.sin (ε / 4) := by
    rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi (by linarith [hv_abs, hε4_le_pi2])]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [abs_nonneg ((θhat - θ) / 4)]) hε4_le_pi2 hv_abs

  have hu_le_w : (θhat + θ) / 4 ≤ (2 * θhat + ε) / 4 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    linarith [hθ_le]
  have hw_ge : ε / 4 ≤ (2 * θhat + ε) / 4 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    linarith [h0]
  have hu_ge : -(ε / 4) ≤ (θhat + θ) / 4 := by
    have h2 : (2 * θhat - ε) / 4 = θhat / 2 - ε / 4 := by ring
    have h3 : (2 * θhat - ε) / 4 ≤ (θhat + θ) / 4 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      linarith [hθ_ge]
    have h4 : (0 : ℝ) ≤ θhat / 2 := by linarith [h0]
    linarith
  have hu_abs_le_w : |(θhat + θ) / 4| ≤ (2 * θhat + ε) / 4 := by
    rw [abs_le]
    exact ⟨by linarith [hu_ge, hw_ge], hu_le_w⟩

  have hB : |Real.sin ((θhat + θ) / 4)| ≤ 2 * Real.sin ((2 * θhat + ε) / 4) := by
    by_cases hcase : (2 * θhat + ε) / 4 ≤ Real.pi / 2
    · have huabs_pi : |(θhat + θ) / 4| ≤ Real.pi := by
        linarith [hu_abs_le_w, hw_lt_pi]
      rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi huabs_pi]
      have hmono := Real.sin_le_sin_of_le_of_le_pi_div_two
        (x := |(θhat + θ) / 4|) (y := (2 * θhat + ε) / 4)
        (by linarith [abs_nonneg ((θhat + θ) / 4)]) hcase hu_abs_le_w
      nlinarith [hmono, hsinw.le]
    · push Not at hcase

      have hw_ub : (2 * θhat + ε) / 4 < Real.pi / 2 + 1 / 4 := by
        have hlt : (2 * θhat + ε) / 4 < (2 * Real.pi + ε) / 4 := by
          apply div_lt_div_of_pos_right _ (by norm_num)
          linarith [hpi]
        have h2 : (2 * Real.pi + ε) / 4 = Real.pi / 2 + ε / 4 := by ring
        rw [h2] at hlt
        linarith [hε4le]
      have hcos14 : (1 : ℝ) / 2 ≤ Real.cos (1 / 4) := by
        have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := (1 : ℝ) / 4) (y := Real.pi / 3)
          (by norm_num) (by nlinarith [Real.pi_gt_three])
          (by nlinarith [Real.pi_gt_three])
        rwa [Real.cos_pi_div_three] at h
      have hpiw_lb : Real.pi / 2 - 1 / 4 ≤ Real.pi - (2 * θhat + ε) / 4 := by
        linarith [hw_ub]
      have hpiw_ub : Real.pi - (2 * θhat + ε) / 4 ≤ Real.pi / 2 := by linarith [hcase]
      have hmono := Real.sin_le_sin_of_le_of_le_pi_div_two
        (x := Real.pi / 2 - 1 / 4) (y := Real.pi - (2 * θhat + ε) / 4)
        (by linarith [Real.pi_gt_three]) hpiw_ub hpiw_lb
      rw [Real.sin_pi_div_two_sub] at hmono
      rw [Real.sin_pi_sub] at hmono
      have hsinw_half : (1 : ℝ) / 2 ≤ Real.sin ((2 * θhat + ε) / 4) := by linarith [hmono, hcos14]
      have hsinu_le_one : |Real.sin ((θhat + θ) / 4)| ≤ 1 := by
        rw [abs_le]
        exact ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
      nlinarith [hsinw_half, hsinu_le_one]

  have hL : |-2 * Real.sin ((θhat + θ) / 4) * Real.sin ((θhat - θ) / 4)| / 2
      = |Real.sin ((θhat + θ) / 4)| * |Real.sin ((θhat - θ) / 4)| := by
    rw [show (-2 : ℝ) * Real.sin ((θhat + θ) / 4) * Real.sin ((θhat - θ) / 4)
        = -((2 : ℝ) * (Real.sin ((θhat + θ) / 4) * Real.sin ((θhat - θ) / 4))) by ring]
    simp only [abs_neg, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    ring
  have hR : |-2 * Real.sin ((2 * θhat + ε) / 4) * Real.sin (ε / 4)|
      = 2 * Real.sin ((2 * θhat + ε) / 4) * Real.sin (ε / 4) := by
    rw [show (-2 : ℝ) * Real.sin ((2 * θhat + ε) / 4) * Real.sin (ε / 4)
        = -((2 : ℝ) * (Real.sin ((2 * θhat + ε) / 4) * Real.sin (ε / 4))) by ring]
    simp only [abs_neg]
    rw [abs_of_nonneg (by
      exact mul_nonneg (by norm_num) (mul_nonneg hsinw.le hsin_eps))]
    ring
  rw [hL, hR]
  exact mul_le_mul hB hA (abs_nonneg _) (by linarith [hsinw.le])

theorem phaseMean_lipschitz (a b : ℝ) : |phaseMean a - phaseMean b| ≤ |a - b| / 4 := by
  have h := Real.abs_cos_sub_cos_le (a/2) (b/2)
  have hdiff : phaseMean a - phaseMean b = -(Real.cos (a/2) - Real.cos (b/2)) / 2 := by
    unfold phaseMean; ring
  rw [hdiff, abs_div, abs_neg, abs_two]
  rw [show a/2-b/2=(a-b)/2 by ring, abs_div, abs_two] at h
  linarith

theorem phaseMean_error_restricted {θhat θ ε : ℝ}
    (hθ : 0 ≤ θ) (hclose : |θhat - θ| ≤ ε) (h0 : 0 ≤ θhat)
    (hguard : θhat ≤ Real.pi - 2 * ε) (hε0 : 0 < ε) (_hε1 : ε ≤ 1) :
    |phaseMean θhat - phaseMean θ| ≤
      (1/2) * |Real.cos ((θhat + ε)/2) - Real.cos (θhat/2)| := by
  have hθle : θ ≤ θhat + ε := by linarith [(abs_le.1 hclose).1]
  have hεpi : ε / 4 ≤ Real.pi / 2 := by nlinarith [Real.pi_gt_three]
  have hsinε : 0 ≤ Real.sin (ε/4) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hw0 : 0 ≤ (2*θhat+ε)/4 := by linarith
  have hwpi : (2*θhat+ε)/4 ≤ Real.pi/2 := by linarith
  have hu0 : 0 ≤ (θhat+θ)/4 := by linarith
  have hule : (θhat+θ)/4 ≤ (2*θhat+ε)/4 := by linarith
  have hsu : |Real.sin ((θhat+θ)/4)| ≤ Real.sin ((2*θhat+ε)/4) := by
    rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hu0 (by linarith))]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hwpi hule
  have hv : |(θhat-θ)/4| ≤ ε/4 := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<4)]
    linarith
  have hsv : |Real.sin ((θhat-θ)/4)| ≤ Real.sin (ε/4) := by
    rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi (by linarith)]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [abs_nonneg ((θhat-θ)/4), Real.pi_pos]) hεpi hv
  have hsw : 0 ≤ Real.sin ((2*θhat+ε)/4) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hw0 (by linarith)
  have hd : phaseMean θhat - phaseMean θ = -(Real.cos (θhat/2)-Real.cos (θ/2))/2 := by
    unfold phaseMean; ring
  rw [hd, abs_div, abs_neg, abs_two, Real.cos_sub_cos, Real.cos_sub_cos]
  rw [show (θhat/2+θ/2)/2=(θhat+θ)/4 by ring,
    show (θhat/2-θ/2)/2=(θhat-θ)/4 by ring,
    show ((θhat+ε)/2+θhat/2)/2=(2*θhat+ε)/4 by ring,
    show ((θhat+ε)/2-θhat/2)/2=ε/4 by ring]
  simp only [abs_mul, abs_neg, abs_two, abs_of_nonneg hsw, abs_of_nonneg hsinε]
  nlinarith [mul_le_mul hsu hsv (abs_nonneg _) hsw]

theorem phaseMean_neg (θ : ℝ) : phaseMean (-θ) = phaseMean θ := by
  simp [phaseMean, neg_div, Real.cos_neg]

theorem phaseMean_period (θ : ℝ) : phaseMean (θ + 4 * Real.pi) = phaseMean θ := by
  unfold phaseMean
  rw [show (θ + 4 * Real.pi)/2 = θ/2 + 2*Real.pi by ring, Real.cos_add_two_pi]

theorem phaseMean_complement (θ : ℝ) :
    phaseMean (2 * Real.pi - θ) = 1 - phaseMean θ := by
  unfold phaseMean
  rw [show (2 * Real.pi - θ)/2 = Real.pi - θ/2 by ring, Real.cos_pi_sub]
  ring

theorem phaseMean_not_injective : ¬Function.Injective phaseMean := by
  intro h
  have he := h (phaseMean_period 0)
  have hp := Real.pi_pos
  linarith

end

end Qatlib.Foundations.PhaseGeometry.AngleEncoding
