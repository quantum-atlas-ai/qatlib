/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhMoments
import Qatlib.Papers.CommutLCHS26.QuadratureCmp.MomentRates
import Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhBudget
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhMomentBounds
open Set Filter MeasureTheory
open scoped BigOperators Topology
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhMoments
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.Moments
open Qatlib.Papers.CommutLCHS26.MainResults.KernelStrip

theorem jacobian_cell {η h t : ℝ} (hη : 0 ≤ η) (hh : 0 ≤ h) (hh1 : h ≤ 1) (ht : 0 ≤ t) :
    h * η * Real.cosh (t + h) ≤ Real.exp 1 * (η * Real.sinh (t + h) - η * Real.sinh t) := by
  have hsh : 0 ≤ Real.sinh h := Real.sinh_nonneg_iff.mpr hh
  have hst : 0 ≤ Real.sinh t := Real.sinh_nonneg_iff.mpr ht
  have hct : 0 ≤ Real.cosh t := (Real.cosh_pos t).le
  have hcosh : Real.cosh (t + h) ≤ Real.exp h * Real.cosh t := by
    rw [Real.cosh_add, ← Real.cosh_add_sinh]
    nlinarith [mul_le_mul_of_nonneg_right (Real.sinh_lt_cosh (x := t)).le hsh]
  have hdiff : h * Real.cosh t ≤ Real.sinh (t + h) - Real.sinh t := by
    rw [Real.sinh_add]
    have ha := mul_le_mul_of_nonneg_left (Real.one_le_cosh h) hst
    have hb := mul_le_mul_of_nonneg_right (Real.self_le_sinh_iff.mpr hh) hct
    nlinarith
  have hj := mul_le_mul_of_nonneg_left hcosh (mul_nonneg hh hη)
  have he := Real.exp_le_exp.mpr hh1
  have hd := mul_le_mul_of_nonneg_left hdiff (mul_nonneg (Real.exp_pos 1).le hη)
  have hs := mul_le_mul_of_nonneg_right he (mul_nonneg (mul_nonneg hh hη) hct)
  nlinarith

theorem power_cell {a b ν : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hν : 0 ≤ ν) :
    (b - a) * b ^ ν ≤ (ν + 1) * ∫ x in a..b, x ^ ν := by
  have hb : 0 ≤ b := ha.trans hab
  have hpow := Real.rpow_le_rpow ha hab hν
  have hm := mul_le_mul_of_nonneg_left hpow ha
  rw [integral_rpow (Or.inl (by linarith : -1 < ν))]
  have hne : ν + 1 ≠ 0 := by linarith
  rw [mul_div_cancel₀ _ hne]
  rw [Real.rpow_add_of_nonneg hb hν (by norm_num : (0 : ℝ) ≤ 1),
    Real.rpow_add_of_nonneg ha hν (by norm_num : (0 : ℝ) ≤ 1), Real.rpow_one, Real.rpow_one]
  nlinarith

theorem weighted_cell (f : ℝ → ℝ) (hf : Continuous f) (hn : ∀ x, 0 ≤ f x)
    (hm : AntitoneOn f (Ici 0)) {a b ν : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hν : 0 ≤ ν) :
    (b - a) * b ^ ν * f b ≤ (ν + 1) * ∫ x in a..b, f x * |x| ^ ν := by
  have hw : Continuous (fun x : ℝ => f x * |x| ^ ν) :=
    hf.mul (continuous_abs.rpow_const (fun _ => Or.inr hν))
  have hp := mul_le_mul_of_nonneg_right (power_cell ha hab hν) (hn b)
  have hi : (∫ x in a..b, x ^ ν) * f b ≤ ∫ x in a..b, f x * |x| ^ ν := by
    rw [← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_mono_on hab
      (((Real.continuous_rpow_const hν).intervalIntegrable a b).mul_const (f b))
      (hw.intervalIntegrable a b)
    intro x hx
    have hx0 : 0 ≤ x := ha.trans hx.1
    have hfb : f b ≤ f x := hm hx0 (ha.trans hab) hx.2
    rw [abs_of_nonneg hx0]
    nlinarith [mul_le_mul_of_nonneg_left hfb (Real.rpow_nonneg hx0 ν)]
  nlinarith [mul_le_mul_of_nonneg_left hi (by linarith : 0 ≤ ν + 1)]

theorem finite_sinh_moment (f : ℝ → ℝ) (hf : Continuous f) (hn : ∀ x, 0 ≤ f x)
    (hm : AntitoneOn f (Ici 0)) (heven : ∀ x, f (-x) = f x) {ν η h : ℝ}
    (hν : 0 ≤ ν) (hη : 0 ≤ η) (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hi : IntegrableOn (fun x => f x * |x| ^ ν) (Ioi 0)) (N : ℕ) :
    (∑ q ∈ Finset.Icc (-(N : ℤ)) N,
      h * η * Real.cosh (h * (q : ℝ)) * f (η * Real.sinh (h * (q : ℝ))) *
        |η * Real.sinh (h * (q : ℝ))| ^ ν) ≤
      h * η * f 0 * (0 : ℝ) ^ ν +
        2 * Real.exp 1 * (ν + 1) * ∫ x in Ioi 0, f x * |x| ^ ν := by
  let k := fun j : ℕ => η * Real.sinh (h * (j : ℝ))
  let w := fun x : ℝ => f x * |x| ^ ν
  let F := fun q : ℤ => h * η * Real.cosh (h * (q : ℝ)) *
    f (η * Real.sinh (h * (q : ℝ))) * |η * Real.sinh (h * (q : ℝ))| ^ ν
  have hw : Continuous w := hf.mul (continuous_abs.rpow_const (fun _ => Or.inr hν))
  have hkn (j : ℕ) : 0 ≤ k j := by dsimp [k]; positivity
  have hkm (j : ℕ) : k j ≤ k (j + 1) := by
    apply mul_le_mul_of_nonneg_left _ hη
    apply Real.sinh_le_sinh.mpr
    push_cast
    nlinarith
  have hcell (j : ℕ) : F (j + 1 : ℕ) ≤
      Real.exp 1 * (ν + 1) * ∫ x in k j..k (j + 1), w x := by
    have hj := jacobian_cell hη hh hh1 (mul_nonneg hh (Nat.cast_nonneg j))
    have he : h * (j : ℝ) + h = h * (j + 1 : ℕ) := by push_cast; ring
    rw [he] at hj
    have hJ : h * η * Real.cosh (h * (j + 1 : ℕ)) ≤
        Real.exp 1 * (k (j + 1) - k j) := hj
    have hwc := weighted_cell f hf hn hm (hkn j) (hkm j) hν
    have hsample := mul_le_mul_of_nonneg_right hJ
      (mul_nonneg (hn (k (j + 1))) (Real.rpow_nonneg (hkn (j + 1)) ν))
    have hbound := mul_le_mul_of_nonneg_left hwc (Real.exp_pos 1).le
    dsimp only [F]
    simp only [Int.cast_natCast]
    change h * η * Real.cosh (h * (j + 1 : ℕ)) * f (k (j + 1)) * |k (j + 1)| ^ ν ≤ _
    rw [abs_of_nonneg (hkn (j + 1))]
    dsimp only [w] at *
    nlinarith
  have hs := Finset.sum_le_sum (s := Finset.range N) (fun j _ => hcell j)
  rw [← Finset.mul_sum, intervalIntegral.sum_integral_adjacent_intervals
    (fun j _ => hw.intervalIntegrable (k j) (k (j + 1)))] at hs
  have hk0 : k 0 = 0 := by simp [k]
  rw [hk0] at hs
  have htail : (∫ x in (0 : ℝ)..k N, w x) ≤ ∫ x in Ioi 0, w x := by
    rw [intervalIntegral.integral_of_le (hkn N)]
    apply setIntegral_mono_set hi
    · exact ae_of_all _ (fun x => mul_nonneg (hn x) (Real.rpow_nonneg (abs_nonneg x) ν))
    · exact ae_of_all _ (fun _ hx => hx.1)
  have hsum := hs.trans (mul_le_mul_of_nonneg_left htail (by positivity))
  have hF : Function.Even F := by
    intro q
    dsimp [F]
    simp only [Int.cast_neg, mul_neg, Real.cosh_neg, Real.sinh_neg, heven, abs_neg]
  have he := Finset.sum_Icc_of_even_eq_range hF N
  rw [Finset.sum_range_succ'] at he
  simp only [two_nsmul, Nat.cast_zero] at he
  have hF0 : F 0 = h * η * f 0 * (0 : ℝ) ^ ν := by simp [F]
  change (∑ q ∈ Finset.Icc (-(N : ℤ)) N, F q) ≤ _
  dsimp only [w] at *
  nlinarith

theorem norm_coefficient_continuous (n : ℕ) (b c d : ℝ) (hb : 0 < b) :
    Continuous (fun x : ℝ => ‖coefficient n b c d (x : ℂ)‖) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hc := (coefficient_analytic n b c d (ρ := 0) (by norm_num) (Or.inr hb)
    (x : ℂ) (by simp)).continuousAt
  exact (hc.comp (by fun_prop)).norm

theorem capped_continuous (β c : ℝ) : Continuous (cappedDensity β c) := by
  have hp : Continuous (fun x : ℝ => (max 1 |x|) ^ β) :=
    (continuous_const.max continuous_abs).rpow_const (fun _ => Or.inl (by positivity))
  exact hp.mul (by fun_prop)

theorem capped_integrable (β : ℝ) {c : ℝ} (hc : 0 < c) : Integrable (cappedDensity β c) := by
  by_cases hβ : β ≤ 0
  · exact cappedDensity_integrable hβ hc
  · obtain ⟨K, _, hpeak⟩ := positive_power_peak (lt_of_not_ge hβ)
    have hi :=
        (cappedDensity_integrable (β := 0) (by norm_num) (by positivity : 0 < 2 * c)).const_mul
        (1 + K * c ^ β)
    apply hi.mono' (capped_continuous β c).aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (cappedDensity_nonneg β c x)]
    exact cappedDensity_positive_majorant hpeak hc x

theorem weighted_integrable (n : ℕ) (b c d ν : ℝ) (hb : 0 < b) (hc : 0 < c) (hν : 0 ≤ ν) :
    Integrable (fun x : ℝ => ‖coefficient n b c d (x : ℂ)‖ * |x| ^ ν) := by
  have hw : Continuous (fun x : ℝ => ‖coefficient n b c d (x : ℂ)‖ * |x| ^ ν) :=
    (norm_coefficient_continuous n b c d hb).mul (continuous_abs.rpow_const (fun _ => Or.inr hν))
  have hi :=
      (capped_integrable (ν - (n + 1 : ℕ)) hc).const_mul (kernelScale n b c d / (min 1 b) ^ n)
  apply hi.mono' hw.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖coefficient n b c d (x : ℂ)‖ * |x| ^ ν)]
  exact weighted_norm_majorant n b c d ν x hb hν

theorem capped_half_three_regimes (n : ℕ) (ν : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c →
      (∫ x in Ioi 0, cappedDensity (ν - (n + 1 : ℕ)) c x) ≤ C * momentGrowth n ν c := by
  by_cases hn : ν < n
  · have hβ : ν - (n + 1 : ℕ) < -1 := by push_cast; linarith
    have hd : 1 / (ν - n) < 0 := div_neg_of_pos_of_neg (by norm_num) (sub_neg.mpr hn)
    refine ⟨1 - 1 / (ν - n), by linarith, fun c hc => ?_⟩
    have hi := cappedDensity_subcritical hβ hc
    have he : ν - (n + 1 : ℕ) + 1 = ν - n := by push_cast; ring
    simpa only [he, momentGrowth, if_pos hn, mul_one] using! hi
  · by_cases he : ν = n
    · subst ν
      refine ⟨1 + 2 * Real.sqrt Real.pi, by positivity, fun c hc => ?_⟩
      have hβ : (n : ℝ) - (n + 1 : ℕ) = -1 := by push_cast; ring
      rw [hβ]
      have hi := cappedDensity_critical hc
      have hl : 0 ≤ Real.log (1 + c) := Real.log_nonneg (by linarith)
      simp only [momentGrowth, lt_self_iff_false, if_false, if_true]
      nlinarith [mul_nonneg hl (Real.sqrt_nonneg Real.pi)]
    · have hnν : (n : ℝ) < ν := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm he)
      let β := ν - (n + 1 : ℕ)
      have hβ : -1 < β := by dsimp [β]; push_cast; linarith
      have hex : β + 1 = ν - n := by dsimp [β]; push_cast; ring
      by_cases hβ0 : β ≤ 0
      · refine ⟨1 + |gaussianMoment β|, by positivity, fun c hc => ?_⟩
        have hi := cappedDensity_supercritical hβ hβ0 hc
        change (∫ x in Ioi 0, cappedDensity β c x) ≤ _
        rw [hex] at hi
        simp only [momentGrowth, if_neg hn, if_neg he]
        nlinarith [Real.rpow_nonneg hc.le (ν - n), abs_nonneg (gaussianMoment β)]
      · have hβp : 0 < β := lt_of_not_ge hβ0
        obtain ⟨K, hK, hpeak⟩ := positive_power_peak hβp
        refine ⟨(1 + K) * (1 + 8 * Real.sqrt Real.pi), by positivity, fun c hc => ?_⟩
        have hAc : 0 ≤ 1 + K * c ^ β := by positivity
        have hmono : (∫ x in Ioi 0, cappedDensity β c x) ≤
            (1 + K * c ^ β) * ∫ x in Ioi 0, cappedDensity 0 (2 * c) x := by
          rw [← integral_const_mul]
          apply setIntegral_mono_on (capped_integrable β hc).integrableOn
            (((capped_integrable 0 (by positivity : 0 < 2 * c)).const_mul (1 + K * c ^ β)).integrableOn)
            measurableSet_Ioi
          intro x _
          exact cappedDensity_positive_majorant hpeak hc x
        have hgauss : (∫ x in Ioi 0, cappedDensity 0 (2 * c) x) ≤ 1 + 8 * c * Real.sqrt Real.pi := by
          have hi := gaussian_integrable (by positivity : 0 < 2 * c)
          have hbound := setIntegral_le_integral (s := Ioi (0 : ℝ)) hi
            (ae_of_all _ (fun x : ℝ => (Real.exp_pos (-x ^ 2 / (4 * (2 * c) ^ 2))).le))
          rw [gaussian_integral (by positivity : 0 < 2 * c)] at hbound
          simp only [cappedDensity, Real.rpow_zero, one_mul]
          nlinarith [mul_nonneg hc.le (Real.sqrt_nonneg Real.pi)]
        have hbound := (hmono.trans (mul_le_mul_of_nonneg_left hgauss hAc)).trans
          (positive_power_growth hβp hK.le hc)
        change (∫ x in Ioi 0, cappedDensity β c x) ≤ _
        simpa only [momentGrowth, if_neg hn, if_neg he, hex] using! hbound

theorem continuous_moments (n : ℕ) (b ν : ℝ) (hb : 0 < b) (hν : 0 ≤ ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c → ∀ d : ℝ,
      2 * (∫ x in Ioi (0 : ℝ), ‖coefficient n b c d (x : ℂ)‖ * |x| ^ ν) ≤
        kernelScale n b c d * C * momentGrowth n ν c := by
  obtain ⟨C, hC, hcap⟩ := capped_half_three_regimes n ν
  have hm : 0 < (min 1 b) ^ n := pow_pos (lt_min (by norm_num) hb) _
  refine ⟨2 * C / (min 1 b) ^ n, by positivity, fun c hc d => ?_⟩
  have hA : 0 ≤ kernelScale n b c d / (min 1 b) ^ n := by unfold kernelScale; positivity
  have hi : (∫ x in Ioi (0 : ℝ), ‖coefficient n b c d (x : ℂ)‖ * |x| ^ ν) ≤
      (kernelScale n b c d / (min 1 b) ^ n) *
        ∫ x in Ioi 0, cappedDensity (ν - (n + 1 : ℕ)) c x := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on (weighted_integrable n b c d ν hb hc hν).integrableOn
      (((capped_integrable (ν - (n + 1 : ℕ)) hc).const_mul
        (kernelScale n b c d / (min 1 b) ^ n)).integrableOn) measurableSet_Ioi
    intro x _
    exact weighted_norm_majorant n b c d ν x hb hν
  have hbnd := hi.trans (mul_le_mul_of_nonneg_left (hcap c hc) hA)
  calc
    _ ≤ 2 * ((kernelScale n b c d / (min 1 b) ^ n) * (C * momentGrowth n ν c)) :=
      mul_le_mul_of_nonneg_left hbnd (by norm_num)
    _ = _ := by ring

open Qatlib.Papers.CommutLCHS26.QuadratureCmp

theorem moment_eq_samples (n : ℕ) (b c d ν η h : ℝ) (N : ℕ) (hη : 0 ≤ η) (hh : 0 ≤ h) :
    SinhMoments.moment n b c d ν η h N =
      ∑ q ∈ Finset.Icc (-(N : ℤ)) N,
        h * η * Real.cosh (h * (q : ℝ)) * ‖coefficient n b c d ((η * Real.sinh (h * (q : ℝ)) : ℝ) : ℂ)‖ *
          |η * Real.sinh (h * (q : ℝ))| ^ ν := by
  unfold SinhMoments.moment
  apply Finset.sum_congr rfl
  intro q _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

theorem actual_to_continuous (n : ℕ) (b c d ν η h : ℝ) (N : ℕ) (hb : 0 < b)
    (hc : 0 < c) (hν : 0 ≤ ν) (hη : 0 ≤ η) (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    SinhMoments.moment n b c d ν η h N ≤
      h * η * (kernelScale n b c d / b ^ n) * (0 : ℝ) ^ ν +
        2 * Real.exp 1 * (ν + 1) *
          ∫ x in Ioi (0 : ℝ), ‖coefficient n b c d (x : ℂ)‖ * |x| ^ ν := by
  rw [moment_eq_samples n b c d ν η h N hη hh]
  have hm := finite_sinh_moment (fun x : ℝ => ‖coefficient n b c d (x : ℂ)‖)
    (norm_coefficient_continuous n b c d hb) (fun _ => norm_nonneg _)
    (Trapezoid.real_norm_antitone n b c d hb) (fun x => Trapezoid.real_norm_even n b c d x hb)
    hν hη hh hh1 (weighted_integrable n b c d ν hb hc hν).integrableOn N
  simpa only [Complex.ofReal_zero, norm_coefficient_zero n b c d hb] using! hm

theorem corrected_moments (n : ℕ) (b ν : ℝ) (hb : 0 < b) (hν : 0 ≤ ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c → ∀ d η h : ℝ, 0 ≤ η → 0 ≤ h → h ≤ 1 → ∀ N : ℕ,
      SinhMoments.moment n b c d ν η h N ≤ kernelScale n b c d *
        (h * η / b ^ n * (0 : ℝ) ^ ν + C * momentGrowth n ν c) := by
  obtain ⟨C, hC, hcont⟩ := continuous_moments n b ν hb hν
  refine ⟨Real.exp 1 * (ν + 1) * C, by positivity, fun c hc d η h hη hh hh1 N => ?_⟩
  have hm := actual_to_continuous n b c d ν η h N hb hc hν hη hh hh1
  have hi := mul_le_mul_of_nonneg_left (hcont c hc d)
    (by positivity : 0 ≤ Real.exp 1 * (ν + 1))
  calc
    _ ≤ h * η * (kernelScale n b c d / b ^ n) * (0 : ℝ) ^ ν +
        (Real.exp 1 * (ν + 1)) * (2 * ∫ x in Ioi (0 : ℝ), ‖coefficient n b c d (x : ℂ)‖ * |x| ^ ν) := by
      convert! hm using 1; ring
    _ ≤ h * η * (kernelScale n b c d / b ^ n) * (0 : ℝ) ^ ν +
        (Real.exp 1 * (ν + 1)) * (kernelScale n b c d * C * momentGrowth n ν c) :=
      _root_.add_le_add le_rfl hi
    _ = _ := by ring

theorem positive_order_moments (n : ℕ) (b ν : ℝ) (hb : 0 < b) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c → ∀ d η h : ℝ, 0 ≤ η → 0 ≤ h → h ≤ 1 → ∀ N : ℕ,
      SinhMoments.moment n b c d ν η h N ≤ kernelScale n b c d * C * momentGrowth n ν c := by
  obtain ⟨C, hC, hm⟩ := corrected_moments n b ν hb hν.le
  refine ⟨C, hC, fun c hc d η h hη hh hh1 N => ?_⟩
  simpa only [Real.zero_rpow hν.ne', mul_zero, zero_add, mul_assoc] using! hm c hc d η h hη hh hh1 N

theorem growth_ge_one (n : ℕ) (ν : ℝ) {c : ℝ} (hc : 0 ≤ c) : 1 ≤ momentGrowth n ν c := by
  unfold momentGrowth
  split_ifs
  · norm_num
  · have hlog : 0 ≤ Real.log (1 + c) := Real.log_nonneg (by linarith)
    linarith
  · have hp : 0 ≤ c ^ (ν - n) := Real.rpow_nonneg hc _
    linarith

theorem capped_scale_moments (n : ℕ) (b ν E : ℝ) (hb : 0 < b) (hν : 0 ≤ ν) (hE : 0 ≤ E) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c → ∀ d η h : ℝ, 0 ≤ η → η ≤ E → 0 ≤ h → h ≤ 1 → ∀ N : ℕ,
      SinhMoments.moment n b c d ν η h N ≤ kernelScale n b c d * C * momentGrowth n ν c := by
  obtain ⟨C, hC, hm⟩ := corrected_moments n b ν hb hν
  have hEb : 0 ≤ E / b ^ n := div_nonneg hE (pow_nonneg hb.le n)
  refine ⟨E / b ^ n + C, by positivity, fun c hc d η h hη hηE hh hh1 N => ?_⟩
  have hzero : (0 : ℝ) ^ ν ≤ 1 := by
    by_cases he : ν = 0
    · simp [he]
    · simp [Real.zero_rpow he]
  have hηh : h * η ≤ E := (mul_le_of_le_one_left hη hh1).trans hηE
  have hcent : h * η / b ^ n * (0 : ℝ) ^ ν ≤ E / b ^ n := by
    calc
      _ ≤ h * η / b ^ n := mul_le_of_le_one_right (by positivity) hzero
      _ ≤ _ := div_le_div_of_nonneg_right hηh (pow_nonneg hb.le n)
  have hcg : h * η / b ^ n * (0 : ℝ) ^ ν ≤ E / b ^ n * momentGrowth n ν c :=
    hcent.trans (le_mul_of_one_le_right hEb (growth_ge_one n ν hc.le))
  have hks : 0 ≤ kernelScale n b c d := by unfold kernelScale; positivity
  calc
    _ ≤ kernelScale n b c d * (h * η / b ^ n * (0 : ℝ) ^ ν + C * momentGrowth n ν c) :=
      hm c hc d η h hη hh hh1 N
    _ ≤ kernelScale n b c d * (E / b ^ n * momentGrowth n ν c + C * momentGrowth n ν c) :=
      mul_le_mul_of_nonneg_left (_root_.add_le_add hcg le_rfl) hks
    _ = _ := by ring

theorem canonical_scale_moments (n : ℕ) (b ν : ℝ) (hb : 0 < b) (hν : 0 ≤ ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c → ∀ d η h : ℝ,
      0 ≤ η → η ≤ min 1 b → 0 ≤ h → h ≤ 1 → ∀ N : ℕ,
        SinhMoments.moment n b c d ν η h N ≤ kernelScale n b c d * C * momentGrowth n ν c :=
  capped_scale_moments n b ν (min 1 b) hb hν (le_min (by norm_num) hb.le)

theorem capped_scale_rates (n : ℕ) (b ν E : ℝ) (hb : 0 < b) (hν : 0 ≤ ν) (hE : 0 ≤ E)
    (d η h : ℝ → ℝ) (N : ℝ → ℕ)
    (ha : ∀ᶠ c : ℝ in atTop, 0 ≤ η c ∧ η c ≤ E ∧ 0 ≤ h c ∧ h c ≤ 1) :
    (fun c : ℝ => SinhMoments.moment n b c (d c) ν (η c) (h c) (N c)) =O[atTop]
      (fun c => kernelScale n b c (d c) * MomentRates.rate n ν c) := by
  obtain ⟨C, hC, hbound⟩ := capped_scale_moments n b ν E hb hν hE
  obtain ⟨D, _, hrate⟩ := MomentRates.growth_le_rate n ν
  apply Asymptotics.IsBigO.of_bound (C * D)
  filter_upwards [eventually_ge_atTop (1 : ℝ), ha] with c hc ha
  have hc0 : 0 < c := by linarith
  have hp : 0 ≤ SinhMoments.moment n b c (d c) ν (η c) (h c) (N c) := by
    unfold SinhMoments.moment; positivity
  have hks : 0 ≤ kernelScale n b c (d c) := by unfold kernelScale; positivity
  have hr := (MomentRates.rate_pos n ν hc).le
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp, abs_of_nonneg (mul_nonneg hks hr)]
  calc
    _ ≤ kernelScale n b c (d c) * C * momentGrowth n ν c := hbound c hc0 (d c) (η c) (h c) ha.1 ha.2.1 ha.2.2.1 ha.2.2.2 (N c)
    _ ≤ kernelScale n b c (d c) * C * (D * MomentRates.rate n ν c) :=
      mul_le_mul_of_nonneg_left (hrate c hc) (mul_nonneg hks hC.le)
    _ = _ := by ring

open Complex Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
open Qatlib.Papers.CommutLCHS26.MainResults.SinhStrip
open Qatlib.Papers.CommutLCHS26.MainResults.SinhWidth
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhBudget
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhRule
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.Trapezoid (cutoff)
set_option warningAsError false
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
local instance : ContinuousENorm (Matrix ι ι ℂ) :=
  SeminormedAddGroup.toESeminormedAddMonoid.toContinuousENorm

theorem kernel_corrected_moments (n : ℕ) (b ν : ℝ) (hb : 0 < b) (hν : 0 ≤ ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c → ∀ d η β : ℝ,
      0 < η → 0 < β → β < Real.pi / 4 → ∀ T : ℝ, 0 ≤ T →
      ∀ H L : Matrix ι ι ℂ, H.IsHermitian → L.PosSemidef →
        (β : EReal) < analyticWidth n b c d T η H L → ∀ εm εt : ℝ, 0 < εm → 0 < εt →
        let M := stripMass n b c d η β (T * ‖L‖)
        let h := step β M εm
        let Y := selectedWindow n b c d η εt
        let N := cutoff Y h
        0 < h ∧
        ‖(∫ k : ℝ, integrand n b c d T H L (k : ℂ)) - finiteIdeal n b c d T η h H L N‖ ≤ εm + εt ∧
        SinhMoments.moment n b c d ν η h N ≤ kernelScale n b c d *
          (h * η / b ^ n * (0 : ℝ) ^ ν + C * momentGrowth n ν c) := by
  obtain ⟨C, hC, hm⟩ := corrected_moments n b ν hb hν
  refine ⟨C, hC, fun c hc d η β hη hβ hβπ T hT H L hH hL hw εm εt hemp hetp => ?_⟩
  have he := selected_error n b c d η β hb hc hη hβ hβπ H L hH hL hT hemp hetp hw
  refine ⟨he.1, he.2, ?_⟩
  exact hm c hc d η _ hη.le he.1.le (min_le_left _ _) _

end Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhMomentBounds
