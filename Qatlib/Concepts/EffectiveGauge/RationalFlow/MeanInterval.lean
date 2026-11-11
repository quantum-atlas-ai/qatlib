/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.MeanCell
import Mathlib.Tactic.FieldSimp

/-!
# Mean Interval

Rational Flow constructions for Effective Gauge.
Defines `RationalMeanInterval`, `RationalMeanInterval.midpoint`, `RationalMeanInterval.radius`.
Proves `scalar_interval_product`, `meanQuotient_real_bounds`, `meanIntervalQuotient_sound`.
-/


set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Data and hypotheses for Rational Mean Interval in the Rational Flow construction. -/
structure RationalMeanInterval where
  lower : ℚ
  upper : ℚ
  deriving DecidableEq, Repr

/-- Definition of midpoint in the Rational Flow construction. -/
def RationalMeanInterval.midpoint (I : RationalMeanInterval) : ℚ := (I.lower+I.upper)/2
/-- Definition of radius in the Rational Flow construction. -/
def RationalMeanInterval.radius (I : RationalMeanInterval) : ℚ := (I.upper-I.lower)/2

/-- Definition of mean Interval Quotient in the Rational Flow construction. -/
def meanIntervalQuotient (a e length width : ℚ) : RationalMeanInterval :=
  ⟨min (min ((a-e)/length) ((a-e)/(length+width)))
      (min ((a+e)/length) ((a+e)/(length+width))),
    max (max ((a-e)/length) ((a-e)/(length+width)))
      (max ((a+e)/length) ((a+e)/(length+width)))⟩

noncomputable section

/-- Original `scalar_interval_product` guarantee for the `MeanInterval` construction; the complete source hypotheses are retained. -/
private theorem scalar_interval_product (z lo hi t : ℝ) (ht : lo ≤ t ∧ t ≤ hi) :
    min (z*lo) (z*hi) ≤ z*t ∧ z*t ≤ max (z*lo) (z*hi) := by
  by_cases hz : 0 ≤ z
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left ht.1 hz),
      (mul_le_mul_of_nonneg_left ht.2 hz).trans (le_max_right _ _)⟩
  · have hz' : z ≤ 0 := (lt_of_not_ge hz).le
    exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left ht.2 hz'),
      (mul_le_mul_of_nonpos_left ht.1 hz').trans (le_max_left _ _)⟩

/-- Original `meanQuotient_real_bounds` guarantee for the `MeanInterval` construction; the complete source hypotheses are retained. -/
private theorem meanQuotient_real_bounds (a e length width x y : ℝ) (hl : 0<length)
    (hx : |x-a| ≤ e) (hy : length ≤ y ∧ y ≤ length+width) :
    min (min ((a-e)/length) ((a-e)/(length+width)))
        (min ((a+e)/length) ((a+e)/(length+width))) ≤ x/y ∧
      x/y ≤ max (max ((a-e)/length) ((a-e)/(length+width)))
        (max ((a+e)/length) ((a+e)/(length+width))) := by
  have hy0 : 0<y := hl.trans_le hy.1
  have ht : (length+width)⁻¹ ≤ y⁻¹ ∧ y⁻¹ ≤ length⁻¹ := by
    constructor
    · simpa only [one_div] using one_div_le_one_div_of_le hy0 hy.2
    · simpa only [one_div] using one_div_le_one_div_of_le hl hy.1
  have hlo := scalar_interval_product (a-e) _ _ _ ht
  have hhi := scalar_interval_product (a+e) _ _ _ ht
  have hx' := abs_le.mp hx
  have hlow : (a-e)*y⁻¹ ≤ x*y⁻¹ := mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr hy0.le)
  have hhigh : x*y⁻¹ ≤ (a+e)*y⁻¹ := mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr hy0.le)
  simp only [← div_eq_mul_inv] at hlo hhi hlow hhigh
  have hlo' : min ((a-e)/length) ((a-e)/(length+width)) ≤ (a-e)/y := by
    simpa only [min_comm] using hlo.1
  have hhi' : (a+e)/y ≤ max ((a+e)/length) ((a+e)/(length+width)) := by
    simpa only [max_comm] using hhi.2
  constructor
  · exact (min_le_left _ _).trans (hlo'.trans hlow)
  · exact (hhigh.trans hhi').trans (le_max_right _ _)

/-- Original `meanIntervalQuotient_sound` guarantee for the `MeanInterval` construction; the complete source hypotheses are retained. -/
theorem meanIntervalQuotient_sound (a e length width : ℚ) (x y : ℝ)
    (hl : 0<(length : ℝ)) (hx : |x-(a : ℝ)| ≤ (e : ℝ))
    (hy : (length : ℝ) ≤ y ∧ y ≤ (length+width : ℚ)) :
    ((meanIntervalQuotient a e length width).lower : ℝ) ≤ x/y ∧
      x/y ≤ ((meanIntervalQuotient a e length width).upper : ℝ) := by
  have h := meanQuotient_real_bounds (a : ℝ) (e : ℝ) (length : ℝ) (width : ℝ) x y hl hx
    (by simpa only [Rat.cast_add] using hy)
  simpa [meanIntervalQuotient] using h

/-- Original `rationalMeanInterval_midpoint_error` guarantee for the `MeanInterval` construction; the complete source hypotheses are retained. -/
theorem rationalMeanInterval_midpoint_error (I : RationalMeanInterval) (x : ℝ)
    (hx : (I.lower : ℝ) ≤ x ∧ x ≤ (I.upper : ℝ)) :
    |x-(I.midpoint : ℝ)| ≤ (I.radius : ℝ) := by
  apply abs_le.mpr
  simp only [RationalMeanInterval.midpoint,RationalMeanInterval.radius,Rat.cast_div,
    Rat.cast_add,Rat.cast_sub,Rat.cast_ofNat]
  constructor <;> linarith [hx.1,hx.2]

/-- Original `meanQuotient_corner_error` guarantee for the `MeanInterval` construction; the complete source hypotheses are retained. -/
private theorem meanQuotient_corner_error (a e length width x y B : ℝ)
    (he : 0 ≤ e) (hl : 6 ≤ length) (hx : |x-a| ≤ e) (hB : |x| ≤ B)
    (hy : length ≤ y ∧ y ≤ length+width) :
    |x/y-a/length| ≤ e/6+B*width/36 := by
  have hl0 : 0<length := lt_of_lt_of_le (by norm_num) hl
  have hy0 : 0<y := hl0.trans_le hy.1
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hB
  have hw0 : 0 ≤ width := by linarith [hy.1,hy.2]
  have hgap : |length-y| ≤ width := by
    rw [abs_of_nonpos (by linarith [hy.1]),neg_sub]
    linarith [hy.2]
  have hden : 36 ≤ y*length := by
    have h := mul_le_mul (hl.trans hy.1) hl (by norm_num : (0 : ℝ) ≤ 6) hy0.le
    norm_num at h ⊢
    exact h
  have heq : x/y-a/length=(x-a)/length+x*(length-y)/(y*length) := by
    field_simp
    ring
  rw [heq]
  calc
    _ ≤ |(x-a)/length|+|x*(length-y)/(y*length)| := abs_add_le _ _
    _ = |x-a|/length+|x| * |length-y|/(y*length) := by
      simp only [abs_div,abs_mul,abs_of_pos hl0,abs_of_pos hy0]
    _ ≤ e/6+B*width/36 := by
      apply add_le_add
      · exact (div_le_div_of_nonneg_right hx hl0.le).trans
          (div_le_div_of_nonneg_left he (by norm_num) hl)
      · exact (div_le_div_of_nonneg_right (mul_le_mul hB hgap (abs_nonneg _) hB0)
          (mul_nonneg hy0.le hl0.le)).trans
          (div_le_div_of_nonneg_left (mul_nonneg hB0 hw0) (by norm_num) hden)

/-- Original `meanIntervalQuotient_radius_bound` guarantee for the `MeanInterval` construction; the complete source hypotheses are retained. -/
theorem meanIntervalQuotient_radius_bound (a e length width : ℚ)
    (he : 0 ≤ e) (hl : 6 ≤ length) (hw : 0 ≤ width) :
    ((meanIntervalQuotient a e length width).radius : ℝ) ≤
      (e : ℝ)/6+(|(a : ℝ)|+(e : ℝ))*(width : ℝ)/36 := by
  have heR : (0 : ℝ) ≤ e := by exact_mod_cast he
  have hlR : (6 : ℝ) ≤ length := by exact_mod_cast hl
  have hwR : (0 : ℝ) ≤ width := by exact_mod_cast hw
  let B := |(a : ℝ)|+(e : ℝ)
  let R := (e : ℝ)/6+B*(width : ℝ)/36
  have hlow : |(a : ℝ)-(e : ℝ)-(a : ℝ)| ≤ (e : ℝ) := by
    simpa only [sub_sub_cancel_left,abs_neg,abs_of_nonneg heR] using (le_rfl : (e : ℝ) ≤ e)
  have hhigh : |(a : ℝ)+(e : ℝ)-(a : ℝ)| ≤ (e : ℝ) := by
    simpa only [add_sub_cancel_left,abs_of_nonneg heR] using (le_rfl : (e : ℝ) ≤ e)
  have hBlow : |(a : ℝ)-(e : ℝ)| ≤ B := by
    simpa only [B,abs_of_nonneg heR] using abs_sub (a : ℝ) (e : ℝ)
  have hBhigh : |(a : ℝ)+(e : ℝ)| ≤ B := by
    simpa only [B,abs_of_nonneg heR] using abs_add_le (a : ℝ) (e : ℝ)
  have h1 := abs_le.mp (meanQuotient_corner_error (a : ℝ) (e : ℝ) (length : ℝ) (width : ℝ)
    ((a : ℝ)-(e : ℝ)) (length : ℝ) B heR hlR hlow hBlow ⟨le_rfl,by linarith⟩)
  have h2 := abs_le.mp (meanQuotient_corner_error (a : ℝ) (e : ℝ) (length : ℝ) (width : ℝ)
    ((a : ℝ)-(e : ℝ)) ((length : ℝ)+(width : ℝ)) B heR hlR hlow hBlow ⟨by linarith,le_rfl⟩)
  have h3 := abs_le.mp (meanQuotient_corner_error (a : ℝ) (e : ℝ) (length : ℝ) (width : ℝ)
    ((a : ℝ)+(e : ℝ)) (length : ℝ) B heR hlR hhigh hBhigh ⟨le_rfl,by linarith⟩)
  have h4 := abs_le.mp (meanQuotient_corner_error (a : ℝ) (e : ℝ) (length : ℝ) (width : ℝ)
    ((a : ℝ)+(e : ℝ)) ((length : ℝ)+(width : ℝ)) B heR hlR hhigh hBhigh ⟨by linarith,le_rfl⟩)
  have hlo : (a : ℝ)/(length : ℝ)-R ≤
      ((meanIntervalQuotient a e length width).lower : ℝ) := by
    dsimp only [R]
    simp only [meanIntervalQuotient,Rat.cast_min,Rat.cast_div,Rat.cast_sub,Rat.cast_add]
    exact le_min (le_min (by linarith [h1.1]) (by linarith [h2.1]))
      (le_min (by linarith [h3.1]) (by linarith [h4.1]))
  have hhi : ((meanIntervalQuotient a e length width).upper : ℝ) ≤
      (a : ℝ)/(length : ℝ)+R := by
    dsimp only [R]
    simp only [meanIntervalQuotient,Rat.cast_max,Rat.cast_div,Rat.cast_sub,Rat.cast_add]
    exact max_le (max_le (by linarith [h1.2]) (by linarith [h2.2]))
      (max_le (by linarith [h3.2]) (by linarith [h4.2]))
  simp only [RationalMeanInterval.radius,Rat.cast_div,Rat.cast_sub,Rat.cast_ofNat]
  change _ ≤ R
  linarith

end
end Qatlib.Concepts.EffectiveGauge.RationalFlow
