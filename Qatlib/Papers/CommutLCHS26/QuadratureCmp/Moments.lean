/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.QuadratureCmp.Trapezoid
import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-!
# Finite quadrature coefficient moments

This module bounds finite symmetric mesh moments of the kernel coefficients in
[AftabAnTrivisa2026]. The majorant `cappedDensity` separates Gaussian decay from polynomial
weights, and `kernelScale` records the coefficient prefactor.

The resulting estimates distinguish moment orders below, at, and above the threshold `n`, with
constant, logarithmic, and power growth in the Gaussian scale.

## Main statements

* `moment_three_regimes`: a uniform finite-moment bound in the three regimes.
* `finite_rule_moments`: the bound for cutoff quadrature coefficients.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.CommutLCHS26.QuadratureCmp.Moments
open Set MeasureTheory
open scoped BigOperators
open Qatlib.Papers.CommutLCHS26.MainResults.KernelStrip
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.Trapezoid

/-- For a nonnegative even integrable function decreasing on the positive half-line, a finite
symmetric mesh sum is bounded by the central sample plus twice the positive-half-line
integral. -/
theorem finite_even_mass (f : ℝ → ℝ) (hf : AntitoneOn f (Ici 0))
    (hn : ∀ x, 0 ≤ f x) (heven : ∀ x, f (-x) = f x) (hi : Integrable f)
    (N : ℕ) {h : ℝ} (hh : 0 < h) :
    h * (∑ q ∈ Finset.Icc (-(N : ℤ)) N, f (h * (q : ℝ))) ≤
      h * f 0 + 2 * ∫ x in Ioi 0, f x := by
  have hfZ : (fun q : ℤ => f (h * (q : ℝ))).Even := by
    intro q
    simpa only [Int.cast_neg, mul_neg] using! heven (h * (q : ℝ))
  have he := Finset.sum_Icc_of_even_eq_range hfZ N
  have hhead : (∑ j ∈ Finset.range (N + 1), f (h * ((j : ℤ) : ℝ))) =
      (∑ j ∈ Finset.range N, f (h * (j + 1 : ℕ))) + f 0 := by
    simp only [Finset.sum_range_succ', Int.cast_natCast, Nat.cast_zero, mul_zero]
  rw [hhead] at he
  simp only [two_nsmul] at he
  have ht := scaled_antitone_tail f hf hn hi 0 hh
  have hs := ht.1.sum_le_tsum (Finset.range N) (fun _ _ => hn _)
  have hb := (mul_le_mul_of_nonneg_left hs hh.le).trans ht.2
  simp only [Nat.cast_zero, zero_add, mul_zero] at hb
  rw [he]
  simp only [Int.cast_zero, mul_zero]
  nlinarith

/-- For positive `b`, the coefficient denominator is bounded below by `(min 1 b)ⁿ * (max 1
|x|)^(n + 1)`. -/
theorem denominator_lower (n : ℕ) {b x : ℝ} (hb : 0 < b) :
    (min 1 b) ^ n * (max 1 |x|) ^ (n + 1) ≤
      Real.sqrt (1 + x ^ 2) * Real.sqrt (b ^ 2 + x ^ 2) ^ n := by
  have h1 : max 1 |x| ≤ Real.sqrt (1 + x ^ 2) := by
    apply max_le
    · exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [sq_nonneg x])
    · rw [← Real.sqrt_sq_eq_abs x]
      exact Real.sqrt_le_sqrt (by linarith)
  have h2 : min 1 b * max 1 |x| ≤ Real.sqrt (b ^ 2 + x ^ 2) := by
    by_cases hx : |x| ≤ 1
    · rw [max_eq_left hx, mul_one]
      exact (min_le_right _ _).trans
          ((Real.le_sqrt hb.le (by positivity)).mpr (by nlinarith [sq_nonneg x]))
    · rw [max_eq_right (le_of_not_ge hx)]
      calc
        min 1 b * |x| ≤ |x| := mul_le_of_le_one_left (abs_nonneg _) (min_le_left _ _)
        _ ≤ Real.sqrt (b ^ 2 + x ^ 2) := by
          rw [← Real.sqrt_sq_eq_abs x]
          exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg b])
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ min 1 b * max 1 |x|) h2 n
  have h := mul_le_mul h1 hp (by positivity : 0 ≤ (min 1 b * max 1 |x|) ^ n)
    (Real.sqrt_nonneg _)
  convert! h using 1
  ring

/-- The capped power density `(max 1 |x|)^β` multiplied by the Gaussian `exp (-x² / (4c²))`. -/
def cappedDensity (β c x : ℝ) : ℝ :=
  (max 1 |x|) ^ β * Real.exp (-x ^ 2 / (4 * c ^ 2))

/-- The capped Gaussian density is nonnegative. -/
theorem cappedDensity_nonneg (β c x : ℝ) : 0 ≤ cappedDensity β c x := by
  unfold cappedDensity
  positivity

/-- The capped Gaussian density is even. -/
theorem cappedDensity_even (β c x : ℝ) : cappedDensity β c (-x) = cappedDensity β c x := by
  simp only [cappedDensity, abs_neg, neg_sq]

/-- For nonpositive exponent, the capped Gaussian density is decreasing on the nonnegative
half-line. -/
theorem cappedDensity_antitone {β c : ℝ} (hβ : β ≤ 0) :
    AntitoneOn (cappedDensity β c) (Ici 0) := by
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  have hp : (max 1 |y|) ^ β ≤ (max 1 |x|) ^ β := by
    apply Real.rpow_le_rpow_of_nonpos (by positivity)
      (max_le_max_left 1 (by simpa only [abs_of_nonneg hx0, abs_of_nonneg hy0] using! hxy)) hβ
  have he : Real.exp (-y ^ 2 / (4 * c ^ 2)) ≤ Real.exp (-x ^ 2 / (4 * c ^ 2)) := by
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (neg_le_neg ((sq_le_sq₀ hx hy).mpr hxy)) (by positivity)
  exact mul_le_mul hp he (Real.exp_pos _).le (by positivity)

/-- For positive `c` and nonpositive exponent, the capped Gaussian density is integrable. -/
theorem cappedDensity_integrable {β c : ℝ} (hβ : β ≤ 0) (hc : 0 < c) :
    Integrable (cappedDensity β c) := by
  have hp : Continuous (fun x : ℝ => (max 1 |x|) ^ β) :=
    (continuous_const.max continuous_abs).rpow_const (fun _ => Or.inl (by positivity))
  have hd : Continuous (cappedDensity β c) := hp.mul (by fun_prop)
  apply (gaussian_integrable hc).mono' hd.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (cappedDensity_nonneg β c x)]
  exact mul_le_of_le_one_left (Real.exp_pos _).le
    (Real.rpow_le_one_of_one_le_of_nonpos (le_max_left _ _) hβ)

/-- For `β < -1` and positive `c`, the positive-half-line density integral is at most `1 - 1 /
(β + 1)`. -/
theorem cappedDensity_subcritical {β c : ℝ} (hβ : β < -1) (hc : 0 < c) :
    (∫ x in Ioi 0, cappedDensity β c x) ≤ 1 - 1 / (β + 1) := by
  have hi := cappedDensity_integrable (by linarith : β ≤ 0) hc
  have he (x : ℝ) : Real.exp (-x ^ 2 / (4 * c ^ 2)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg x]) (by positivity)
  have hn : (∫ x in (0 : ℝ)..1, cappedDensity β c x) ≤ 1 := by
    calc
      _ ≤ ∫ _x in (0 : ℝ)..1, (1 : ℝ) := by
        apply intervalIntegral.integral_mono_on (by norm_num) hi.intervalIntegrable
          intervalIntegrable_const
        intro x _
        exact mul_le_one₀ (Real.rpow_le_one_of_one_le_of_nonpos (le_max_left _ _)
          (by linarith)) (Real.exp_pos _).le (he x)
      _ = 1 := by simp
  have ht : (∫ x in Ioi (1 : ℝ), cappedDensity β c x) ≤ -1 / (β + 1) := by
    calc
      _ ≤ ∫ x in Ioi (1 : ℝ), x ^ β := by
        apply setIntegral_mono_on hi.integrableOn
          (integrableOn_Ioi_rpow_of_lt hβ (by norm_num)) measurableSet_Ioi
        intro x hx
        have hx1 : 1 < x := hx
        have hx0 : 0 ≤ x := le_trans (by norm_num) hx1.le
        simp only [cappedDensity, abs_of_nonneg hx0, max_eq_right hx1.le]
        exact mul_le_of_le_one_right (Real.rpow_nonneg hx0 _) (he x)
      _ = -1 / (β + 1) := by rw [integral_Ioi_rpow_of_lt hβ (by norm_num)]; simp
  have hs := intervalIntegral.integral_interval_add_Ioi (a := 0) (b := 1)
    hi.integrableOn hi.integrableOn
  rw [← hs]
  calc
    _ ≤ 1 + -1 / (β + 1) := add_le_add hn ht
    _ = _ := by ring

/-- The real-axis kernel prefactor `(b + 1)ⁿ / (2π) * exp (d - 1 / (4c²))`. -/
def kernelScale (n : ℕ) (b c d : ℝ) : ℝ :=
  (b + 1) ^ n / (2 * Real.pi) * Real.exp (d - 1 / (4 * c ^ 2))

/-- For positive `b` and nonnegative moment order, the weighted coefficient norm is bounded by
`kernelScale / (min 1 b)ⁿ` times the corresponding capped density. -/
theorem weighted_norm_majorant (n : ℕ) (b c d ν x : ℝ) (hb : 0 < b) (hν : 0 ≤ ν) :
    ‖coefficient n b c d (x : ℂ)‖ * |x| ^ ν ≤
      (kernelScale n b c d / (min 1 b) ^ n) *
        cappedDensity (ν - (n + 1 : ℕ)) c x := by
  have hm : 0 < min 1 b := lt_min (by norm_num) hb
  have hX : 0 < max 1 |x| := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hD : 0 < Real.sqrt (1 + x ^ 2) * Real.sqrt (b ^ 2 + x ^ 2) ^ n := by positivity
  have hA : 0 ≤ kernelScale n b c d := by unfold kernelScale; positivity
  have hp : |x| ^ ν ≤ (max 1 |x|) ^ ν :=
    Real.rpow_le_rpow (abs_nonneg _) (le_max_right _ _) hν
  rw [real_norm n b c d x hb]
  change (kernelScale n b c d * Real.exp (-x ^ 2 / (4 * c ^ 2)) /
    (Real.sqrt (1 + x ^ 2) * Real.sqrt (b ^ 2 + x ^ 2) ^ n)) * |x| ^ ν ≤ _
  calc
    _ = (kernelScale n b c d * Real.exp (-x ^ 2 / (4 * c ^ 2)) * |x| ^ ν) /
        (Real.sqrt (1 + x ^ 2) * Real.sqrt (b ^ 2 + x ^ 2) ^ n) := by ring
    _ ≤ (kernelScale n b c d * Real.exp (-x ^ 2 / (4 * c ^ 2)) * (max 1 |x|) ^ ν) /
        (Real.sqrt (1 + x ^ 2) * Real.sqrt (b ^ 2 + x ^ 2) ^ n) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) hD.le
    _ ≤ (kernelScale n b c d * Real.exp (-x ^ 2 / (4 * c ^ 2)) * (max 1 |x|) ^ ν) /
        ((min 1 b) ^ n * (max 1 |x|) ^ (n + 1)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (denominator_lower n hb)
    _ = _ := by
      unfold cappedDensity
      rw [Real.rpow_sub_natCast hX.ne']
      field_simp

/-- The finite symmetric mesh sum of coefficient norms weighted by the absolute node value to
the power `ν`, multiplied by the mesh step. -/
def moment (n : ℕ) (b c d ν h : ℝ) (N : ℕ) : ℝ :=
  h * ∑ q ∈ Finset.Icc (-(N : ℤ)) N,
    ‖coefficient n b c d ((h * (q : ℝ) : ℝ) : ℂ)‖ * |h * (q : ℝ)| ^ ν

/-- For a nonnegative mesh step, `moment` equals the weighted sum of the norms of the complex
quadrature coefficients. -/
theorem moment_eq_weights (n : ℕ) (b c d ν h : ℝ) (N : ℕ) (hh : 0 ≤ h) :
    moment n b c d ν h N = ∑ q ∈ Finset.Icc (-(N : ℤ)) N,
      ‖(h : ℂ) * coefficient n b c d ((h * (q : ℝ) : ℝ) : ℂ)‖ * |h * (q : ℝ)| ^ ν := by
  simp only [moment, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- For moment order at most `n + 1` and mesh step in `(0, 1]`, the finite moment is bounded by
the kernel prefactor times one plus twice the corresponding density integral. -/
theorem moment_le_capped (n : ℕ) (b c d ν h : ℝ) (N : ℕ) (hb : 0 < b) (hc : 0 < c)
    (hν : 0 ≤ ν) (hνn : ν ≤ (n + 1 : ℕ)) (hh : 0 < h) (hh1 : h ≤ 1) :
    moment n b c d ν h N ≤ (kernelScale n b c d / (min 1 b) ^ n) *
      (1 + 2 * ∫ x in Ioi 0, cappedDensity (ν - (n + 1 : ℕ)) c x) := by
  let β := ν - (n + 1 : ℕ)
  let C := kernelScale n b c d / (min 1 b) ^ n
  have hβ : β ≤ 0 := sub_nonpos.mpr hνn
  have hC : 0 ≤ C := by dsimp [C, kernelScale]; positivity
  have hm := finite_even_mass (cappedDensity β c) (cappedDensity_antitone hβ)
    (cappedDensity_nonneg β c) (cappedDensity_even β c) (cappedDensity_integrable hβ hc) N hh
  have hf0 : cappedDensity β c 0 = 1 := by simp [cappedDensity]
  rw [hf0, mul_one] at hm
  change moment n b c d ν h N ≤ C * (1 + 2 * ∫ x in Ioi 0, cappedDensity β c x)
  calc
    _ ≤ h * ∑ q ∈ Finset.Icc (-(N : ℤ)) N, C * cappedDensity β c (h * (q : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hh.le
      apply Finset.sum_le_sum
      intro q _
      exact weighted_norm_majorant n b c d ν _ hb hν
    _ = C * (h * ∑ q ∈ Finset.Icc (-(N : ℤ)) N, cappedDensity β c (h * (q : ℝ))) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ C * (1 + 2 * ∫ x in Ioi 0, cappedDensity β c x) :=
      mul_le_mul_of_nonneg_left (by linarith [hm]) hC

/-- For `0 ≤ ν < n` and mesh step in `(0, 1]`, the finite moment is at most `kernelScale` times
`(3 - 2 / (ν - n)) / (min 1 b)ⁿ`. -/
theorem moment_subcritical (n : ℕ) (b c d ν h : ℝ) (N : ℕ) (hb : 0 < b) (hc : 0 < c)
    (hν : 0 ≤ ν) (hνn : ν < n) (hh : 0 < h) (hh1 : h ≤ 1) :
    moment n b c d ν h N ≤ kernelScale n b c d *
      ((3 - 2 / (ν - n)) / (min 1 b) ^ n) := by
  have hνn' : ν ≤ (n + 1 : ℕ) := by push_cast; linarith
  have hm := moment_le_capped n b c d ν h N hb hc hν hνn' hh hh1
  have hi := cappedDensity_subcritical (β := ν - (n + 1 : ℕ)) (by push_cast; linarith) hc
  have hC : 0 ≤ kernelScale n b c d / (min 1 b) ^ n := by unfold kernelScale; positivity
  calc
    _ ≤ (kernelScale n b c d / (min 1 b) ^ n) *
        (1 + 2 * (1 - 1 / (ν - (n + 1 : ℕ) + 1))) :=
      hm.trans (mul_le_mul_of_nonneg_left (by linarith) hC)
    _ = _ := by push_cast; ring

/-- For nonpositive exponent, the capped Gaussian density is at most one. -/
theorem cappedDensity_le_one {β c : ℝ} (hβ : β ≤ 0) (x : ℝ) :
    cappedDensity β c x ≤ 1 := by
  apply mul_le_one₀ (Real.rpow_le_one_of_one_le_of_nonpos (le_max_left _ _) hβ)
    (Real.exp_pos _).le
  exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg x])
    (by positivity))

/-- For positive `c`, the critical density integral is at most `1 + log (1 + c) + 2 sqrt π`. -/
theorem cappedDensity_critical {c : ℝ} (hc : 0 < c) :
    (∫ x in Ioi 0, cappedDensity (-1) c x) ≤
      1 + Real.log (1 + c) + 2 * Real.sqrt Real.pi := by
  let L := max 1 c
  have hL1 : 1 ≤ L := le_max_left _ _
  have hLc : c ≤ L := le_max_right _ _
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) hL1
  have hi := cappedDensity_integrable (by norm_num : (-1 : ℝ) ≤ 0) hc
  have hn : (∫ x in (0 : ℝ)..1, cappedDensity (-1) c x) ≤ 1 := by
    calc
      _ ≤ ∫ _x in (0 : ℝ)..1, (1 : ℝ) :=
        intervalIntegral.integral_mono (by norm_num) hi.intervalIntegrable
          intervalIntegrable_const (cappedDensity_le_one (by norm_num))
      _ = 1 := by simp
  have hzero : (0 : ℝ) ∉ uIcc 1 L := by
    rw [uIcc_of_le hL1]
    intro hz
    norm_num at hz
  have hm : (∫ x in (1 : ℝ)..L, cappedDensity (-1) c x) ≤ Real.log L := by
    calc
      _ ≤ ∫ x in (1 : ℝ)..L, x⁻¹ := by
        apply intervalIntegral.integral_mono_on hL1 hi.intervalIntegrable
          ((continuousOn_inv₀.mono (subset_compl_singleton_iff.mpr hzero)).intervalIntegrable)
        intro x hx
        have hx1 : 1 ≤ x := hx.1
        have hx0 : 0 ≤ x := le_trans (by norm_num) hx1
        simp only [cappedDensity, abs_of_nonneg hx0, max_eq_right hx1, Real.rpow_neg_one]
        apply mul_le_of_le_one_right (inv_nonneg.mpr hx0)
        exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg x])
          (by positivity))
      _ = Real.log L := by rw [integral_inv hzero, div_one]
  have ht : (∫ x in Ioi L, cappedDensity (-1) c x) ≤ 2 * Real.sqrt Real.pi := by
    calc
      _ ≤ ∫ x in Ioi L, L⁻¹ * Real.exp (-x ^ 2 / (4 * c ^ 2)) := by
        apply setIntegral_mono_on hi.integrableOn
          (((gaussian_integrable hc).const_mul _).integrableOn) measurableSet_Ioi
        intro x hx
        have hxL : L < x := hx
        have hx1 : 1 ≤ x := hL1.trans hxL.le
        have hx0 : 0 ≤ x := hL.le.trans hxL.le
        simp only [cappedDensity, abs_of_nonneg hx0, max_eq_right hx1, Real.rpow_neg_one]
        exact mul_le_mul_of_nonneg_right (inv_anti₀ hL hxL.le) (Real.exp_pos _).le
      _ = L⁻¹ * ∫ x in Ioi L, Real.exp (-x ^ 2 / (4 * c ^ 2)) := integral_const_mul _ _
      _ ≤ L⁻¹ * (2 * c * Real.sqrt Real.pi) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hL.le)
        rw [← gaussian_integral hc]
        exact setIntegral_le_integral (gaussian_integrable hc)
            (ae_of_all _ (fun x => (Real.exp_pos _).le))
      _ ≤ 2 * Real.sqrt Real.pi := by
        have hz := (div_le_one hL).mpr hLc
        calc
          _ = (c / L) * (2 * Real.sqrt Real.pi) := by ring
          _ ≤ 1 * (2 * Real.sqrt Real.pi) := mul_le_mul_of_nonneg_right hz (by positivity)
          _ = _ := by ring
  have hs := intervalIntegral.integral_interval_add_Ioi (a := 0) (b := L)
    hi.integrableOn hi.integrableOn
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hi.intervalIntegrable (a := 0) (b := 1)) (hi.intervalIntegrable (a := 1) (b := L))
  have hl : Real.log L ≤ Real.log (1 + c) :=
    Real.log_le_log hL (max_le (by linarith) (by linarith))
  linarith

/-- For mesh step in `(0, 1]`, the moment of order `n` is bounded by `kernelScale * ((3 + 4 sqrt
π) / (min 1 b)ⁿ) * (1 + log (1 + c))`. -/
theorem moment_critical (n : ℕ) (b c d h : ℝ) (N : ℕ) (hb : 0 < b) (hc : 0 < c)
    (hh : 0 < h) (hh1 : h ≤ 1) :
    moment n b c d n h N ≤ kernelScale n b c d *
      ((3 + 4 * Real.sqrt Real.pi) / (min 1 b) ^ n) * (1 + Real.log (1 + c)) := by
  have hm := moment_le_capped n b c d n h N hb hc (by positivity)
    (by push_cast; linarith) hh hh1
  have hex : (n : ℝ) - (n + 1 : ℕ) = -1 := by push_cast; ring
  rw [hex] at hm
  have hi := cappedDensity_critical hc
  have hC : 0 ≤ kernelScale n b c d / (min 1 b) ^ n := by unfold kernelScale; positivity
  have hl : 0 ≤ Real.log (1 + c) := Real.log_nonneg (by linarith)
  have hs : 1 + 2 * (1 + Real.log (1 + c) + 2 * Real.sqrt Real.pi) ≤
      (3 + 4 * Real.sqrt Real.pi) * (1 + Real.log (1 + c)) := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg Real.pi) hl]
  have hI : 1 + 2 * ∫ x in Ioi 0, cappedDensity (-1) c x ≤
      1 + 2 * (1 + Real.log (1 + c) + 2 * Real.sqrt Real.pi) := by linarith
  calc
    _ ≤ (kernelScale n b c d / (min 1 b) ^ n) *
        ((3 + 4 * Real.sqrt Real.pi) * (1 + Real.log (1 + c))) :=
      hm.trans (mul_le_mul_of_nonneg_left (hI.trans hs) hC)
    _ = _ := by ring

/-- A positive power times `exp (-3u² / 16)` has a uniform positive upper bound on the real
line. -/
theorem positive_power_peak {β : ℝ} (hβ : 0 < β) :
    ∃ K : ℝ, 0 < K ∧ ∀ u : ℝ, |u| ^ β * Real.exp (-(3 / 16 : ℝ) * u ^ 2) ≤ K := by
  let f : ZeroAtInftyContinuousMap ℝ ℝ :=
    { toFun := fun u => |u| ^ β * Real.exp (-(3 / 16 : ℝ) * u ^ 2)
      continuous_toFun := ((continuous_abs.rpow_const (fun _ => Or.inr hβ.le)).mul (by fun_prop))
      zero_at_infty' := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact (by norm_num) β }
  obtain ⟨K, hK⟩ := f.isBounded_range.bddAbove
  refine ⟨max 1 K, lt_of_lt_of_le (by norm_num) (le_max_left _ _), fun u => ?_⟩
  exact (hK (Set.mem_range_self u)).trans (le_max_right _ _)

/-- The positive-half-line integral of `x^β * exp (-x² / 4)`. -/
def gaussianMoment (β : ℝ) : ℝ :=
  ∫ x in Ioi 0, x ^ β * Real.exp (-x ^ 2 / 4)

/-- Scaling a positive-half-line Gaussian moment by positive `c` multiplies its integral by
`c^(β + 1)`. -/
theorem gaussianMoment_scale (β : ℝ) {c : ℝ} (hc : 0 < c) :
    (∫ x in Ioi 0, x ^ β * Real.exp (-x ^ 2 / (4 * c ^ 2))) =
      c ^ (β + 1) * gaussianMoment β := by
  have he : (∫ x in Ioi 0, (c * x) ^ β * Real.exp (-(c * x) ^ 2 / (4 * c ^ 2))) =
      c ^ β * gaussianMoment β := by
    calc
      _ = ∫ x in Ioi 0, c ^ β * (x ^ β * Real.exp (-x ^ 2 / 4)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        have hx0 : 0 ≤ x := le_of_lt (show 0 < x from hx)
        (try dsimp only)
        rw [Real.mul_rpow hc.le hx0]
        have hs : -(c * x) ^ 2 / (4 * c ^ 2) = -x ^ 2 / 4 := by field_simp
        rw [hs]
        ring
      _ = _ := integral_const_mul _ _
  have hs := integral_comp_mul_left_Ioi
    (fun x : ℝ => x ^ β * Real.exp (-x ^ 2 / (4 * c ^ 2))) 0 hc
  rw [he, mul_zero, smul_eq_mul] at hs
  calc
    _ = c * (c ^ β * gaussianMoment β) := by rw [hs]; field_simp
    _ = _ := by rw [Real.rpow_add hc, Real.rpow_one]; ring

/-- For `-1 < β ≤ 0` and positive `c`, the capped density integral is at most `c^(β + 1) *
|gaussianMoment β|`. -/
theorem cappedDensity_supercritical {β c : ℝ} (hβ : -1 < β) (hβ0 : β ≤ 0) (hc : 0 < c) :
    (∫ x in Ioi 0, cappedDensity β c x) ≤ c ^ (β + 1) * |gaussianMoment β| := by
  have hi := cappedDensity_integrable hβ0 hc
  have hg : IntegrableOn (fun x : ℝ => x ^ β * Real.exp (-x ^ 2 / (4 * c ^ 2))) (Ioi 0) := by
    convert! integrableOn_rpow_mul_exp_neg_mul_sq (by positivity : 0 < 1 / (4 * c ^ 2)) hβ using 1
    ext x
    congr 1
    ring
  calc
    _ ≤ ∫ x in Ioi 0, x ^ β * Real.exp (-x ^ 2 / (4 * c ^ 2)) := by
      apply setIntegral_mono_on hi.integrableOn hg measurableSet_Ioi
      intro x hx
      have hx0 : 0 < x := hx
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact Real.rpow_le_rpow_of_nonpos hx0
        (by simpa only [abs_of_pos hx0] using! (le_max_right 1 x)) hβ0
    _ = c ^ (β + 1) * gaussianMoment β := gaussianMoment_scale β hc
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_abs_self _) (Real.rpow_nonneg hc.le _)

/-- A uniform bound on the weighted narrower Gaussian gives a majorant for the capped density by
`(1 + K c^β)` times the zero-exponent density at scale `2c`. -/
theorem cappedDensity_positive_majorant {β K : ℝ}
    (hK : ∀ u : ℝ, |u| ^ β * Real.exp (-(3 / 16 : ℝ) * u ^ 2) ≤ K)
    {c : ℝ} (hc : 0 < c) (x : ℝ) :
    cappedDensity β c x ≤ (1 + K * c ^ β) * cappedDensity 0 (2 * c) x := by
  have hp : (max 1 |x|) ^ β ≤ 1 + |x| ^ β := by
    by_cases hx : |x| ≤ 1
    · rw [max_eq_left hx, Real.one_rpow]
      linarith [Real.rpow_nonneg (abs_nonneg x) β]
    · rw [max_eq_right (le_of_not_ge hx)]
      linarith
  have hg : Real.exp (-x ^ 2 / (4 * c ^ 2)) ≤ Real.exp (-x ^ 2 / (4 * (2 * c) ^ 2)) := by
    apply Real.exp_le_exp.mpr
    apply (div_le_div_iff₀ (by positivity : 0 < 4 * c ^ 2)
      (by positivity : 0 < 4 * (2 * c) ^ 2)).mpr
    nlinarith [sq_nonneg x, sq_nonneg c, mul_nonneg (sq_nonneg x) (sq_nonneg c)]
  have hw : |x| ^ β * Real.exp (-x ^ 2 / (4 * c ^ 2)) ≤
      (K * c ^ β) * Real.exp (-x ^ 2 / (4 * (2 * c) ^ 2)) := by
    let u := x / c
    have hx : x = c * u := by dsimp [u]; field_simp
    rw [hx, abs_mul, abs_of_pos hc, Real.mul_rpow hc.le (abs_nonneg u)]
    have he : -(c * u) ^ 2 / (4 * c ^ 2) =
        -(3 / 16 : ℝ) * u ^ 2 + -(c * u) ^ 2 / (4 * (2 * c) ^ 2) := by field_simp; ring
    rw [he, Real.exp_add]
    calc
      _ = (c ^ β * (|u| ^ β * Real.exp (-(3 / 16 : ℝ) * u ^ 2))) *
          Real.exp (-(c * u) ^ 2 / (4 * (2 * c) ^ 2)) := by ring
      _ ≤ (c ^ β * K) * Real.exp (-(c * u) ^ 2 / (4 * (2 * c) ^ 2)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hK u) (Real.rpow_nonneg hc.le _))
          (Real.exp_pos _).le
      _ = _ := by ring
  change (max 1 |x|) ^ β * Real.exp (-x ^ 2 / (4 * c ^ 2)) ≤ _
  simp only [cappedDensity, Real.rpow_zero, one_mul]
  calc
    _ ≤ (1 + |x| ^ β) * Real.exp (-x ^ 2 / (4 * c ^ 2)) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = Real.exp (-x ^ 2 / (4 * c ^ 2)) + |x| ^ β * Real.exp (-x ^ 2 / (4 * c ^ 2)) := by ring
    _ ≤ Real.exp (-x ^ 2 / (4 * (2 * c) ^ 2)) +
        (K * c ^ β) * Real.exp (-x ^ 2 / (4 * (2 * c) ^ 2)) := add_le_add hg hw
    _ = _ := by ring

/-- For positive `c` and mesh step in `(0, 1]`, the finite symmetric Gaussian mesh mass is at
most `1 + 4c sqrt π`. -/
theorem gaussian_finite_mass {c h : ℝ} (hc : 0 < c) (hh : 0 < h) (hh1 : h ≤ 1) (N : ℕ) :
    h * (∑ q ∈ Finset.Icc (-(N : ℤ)) N, cappedDensity 0 c (h * (q : ℝ))) ≤
      1 + 4 * c * Real.sqrt Real.pi := by
  have hm := finite_even_mass (cappedDensity 0 c) (cappedDensity_antitone (by norm_num))
    (cappedDensity_nonneg 0 c) (cappedDensity_even 0 c)
    (cappedDensity_integrable (by norm_num) hc) N hh
  have hf0 : cappedDensity 0 c 0 = 1 := by simp [cappedDensity]
  rw [hf0, mul_one] at hm
  have hi : (∫ x in Ioi 0, cappedDensity 0 c x) ≤ 2 * c * Real.sqrt Real.pi := by
    simp only [cappedDensity, Real.rpow_zero, one_mul]
    rw [← gaussian_integral hc]
    exact setIntegral_le_integral (gaussian_integrable hc)
        (ae_of_all _ (fun x => (Real.exp_pos _).le))
  linarith

/-- For positive `β` and `c` and nonnegative `K`, the displayed product is bounded by `(1 + K)
(1 + 8 sqrt π) (1 + c^(β + 1))`. -/
theorem positive_power_growth {β K c : ℝ} (hβ : 0 < β) (hK : 0 ≤ K) (hc : 0 < c) :
    (1 + K * c ^ β) * (1 + 8 * c * Real.sqrt Real.pi) ≤
      ((1 + K) * (1 + 8 * Real.sqrt Real.pi)) * (1 + c ^ (β + 1)) := by
  have hp : 0 ≤ c ^ (β + 1) := Real.rpow_nonneg hc.le _
  have hb : c ^ β ≤ 1 + c ^ (β + 1) := by
    by_cases hc1 : c ≤ 1
    · exact (Real.rpow_le_one hc.le hc1 hβ.le).trans (by linarith)
    · calc
        c ^ β ≤ c ^ (β + 1) := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hc1) (by linarith)
        _ ≤ _ := by linarith
  have hcp : c ≤ 1 + c ^ (β + 1) := by
    by_cases hc1 : c ≤ 1
    · linarith
    · calc
        c = c ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ c ^ (β + 1) := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hc1) (by linarith)
        _ ≤ _ := by linarith
  calc
    _ = 1 + K * c ^ β + (8 * Real.sqrt Real.pi) * c +
        (8 * K * Real.sqrt Real.pi) * c ^ (β + 1) := by
      rw [Real.rpow_add hc, Real.rpow_one]
      ring
    _ ≤ (1 + c ^ (β + 1)) + K * (1 + c ^ (β + 1)) +
        (8 * Real.sqrt Real.pi) * (1 + c ^ (β + 1)) +
        (8 * K * Real.sqrt Real.pi) * (1 + c ^ (β + 1)) := by
      apply add_le_add
      · apply add_le_add
        · exact add_le_add (by linarith) (mul_le_mul_of_nonneg_left hb hK)
        · exact mul_le_mul_of_nonneg_left hcp (by positivity)
      · exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

/-- For `β > -1`, finite symmetric capped-density mesh sums are bounded by a fixed positive
constant times `1 + c^(β + 1)` uniformly in the cutoff and mesh step in `(0, 1]`. -/
theorem capped_finite_supercritical {β : ℝ} (hβ : -1 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c → ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ N : ℕ,
      h * (∑ q ∈ Finset.Icc (-(N : ℤ)) N, cappedDensity β c (h * (q : ℝ))) ≤
        C * (1 + c ^ (β + 1)) := by
  by_cases hβ0 : β ≤ 0
  · refine ⟨1 + 2 * |gaussianMoment β|, by positivity, fun c hc h hh hh1 N => ?_⟩
    have hm := finite_even_mass (cappedDensity β c) (cappedDensity_antitone hβ0)
      (cappedDensity_nonneg β c) (cappedDensity_even β c) (cappedDensity_integrable hβ0 hc) N hh
    have hf0 : cappedDensity β c 0 = 1 := by simp [cappedDensity]
    rw [hf0, mul_one] at hm
    have hi := cappedDensity_supercritical hβ hβ0 hc
    nlinarith [Real.rpow_nonneg hc.le (β + 1), abs_nonneg (gaussianMoment β)]
  · have hβp : 0 < β := lt_of_not_ge hβ0
    obtain ⟨K, hK, hpeak⟩ := positive_power_peak hβp
    refine ⟨(1 + K) * (1 + 8 * Real.sqrt Real.pi), by positivity, fun c hc h hh hh1 N => ?_⟩
    have hC : 0 ≤ 1 + K * c ^ β := by positivity
    calc
      _ ≤ h * (∑ q ∈ Finset.Icc (-(N : ℤ)) N,
          (1 + K * c ^ β) * cappedDensity 0 (2 * c) (h * (q : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ hh.le
        apply Finset.sum_le_sum
        intro q _
        exact cappedDensity_positive_majorant hpeak hc _
      _ = (1 + K * c ^ β) *
          (h * ∑ q ∈ Finset.Icc (-(N : ℤ)) N, cappedDensity 0 (2 * c) (h * (q : ℝ))) := by
        rw [← Finset.mul_sum]
        ring
      _ ≤ (1 + K * c ^ β) * (1 + 8 * c * Real.sqrt Real.pi) := by
        apply mul_le_mul_of_nonneg_left _ hC
        convert! gaussian_finite_mass (by positivity : 0 < 2 * c) hh hh1 N using 1
        ring
      _ ≤ _ := positive_power_growth hβp hK.le hc

/-- The piecewise growth factor equal to one below `ν = n`, `1 + log (1 + c)` at equality, and
`1 + c^(ν - n)` above equality. -/
def momentGrowth (n : ℕ) (ν c : ℝ) : ℝ :=
  if ν < n then 1 else if ν = n then 1 + Real.log (1 + c) else 1 + c ^ (ν - n)

/-- For positive `b` and nonnegative moment order, every finite mesh moment is bounded by
`kernelScale` times a fixed positive constant and `momentGrowth`, uniformly over mesh steps
in `(0, 1]`. -/
theorem moment_three_regimes (n : ℕ) (b ν : ℝ) (hb : 0 < b) (hν : 0 ≤ ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c → ∀ d h : ℝ, 0 < h → h ≤ 1 → ∀ N : ℕ,
      moment n b c d ν h N ≤ kernelScale n b c d * C * momentGrowth n ν c := by
  have hm : 0 < (min 1 b) ^ n := pow_pos (lt_min (by norm_num) hb) _
  by_cases hn : ν < n
  · have hd : 2 / (ν - n) < 0 := div_neg_of_pos_of_neg (by norm_num) (sub_neg.mpr hn)
    refine ⟨(3 - 2 / (ν - n)) / (min 1 b) ^ n, div_pos (by linarith) hm,
      fun c hc d h hh hh1 N => ?_⟩
    simpa only [momentGrowth, if_pos hn, mul_one] using!
      moment_subcritical n b c d ν h N hb hc hν hn hh hh1
  · by_cases he : ν = n
    · subst ν
      refine ⟨(3 + 4 * Real.sqrt Real.pi) / (min 1 b) ^ n, by positivity,
        fun c hc d h hh hh1 N => ?_⟩
      simpa only [momentGrowth, lt_self_iff_false, if_false, if_true] using!
        moment_critical n b c d h N hb hc hh hh1
    · have hnν : (n : ℝ) < ν := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm he)
      let β := ν - (n + 1 : ℕ)
      have hβ : -1 < β := by dsimp [β]; push_cast; linarith
      obtain ⟨C, hC, hfinite⟩ := capped_finite_supercritical hβ
      refine ⟨C / (min 1 b) ^ n, div_pos hC hm, fun c hc d h hh hh1 N => ?_⟩
      have hA : 0 ≤ kernelScale n b c d / (min 1 b) ^ n := by unfold kernelScale; positivity
      have hf := hfinite c hc h hh hh1 N
      calc
        _ ≤ h * ∑ q ∈ Finset.Icc (-(N : ℤ)) N,
            (kernelScale n b c d / (min 1 b) ^ n) * cappedDensity β c (h * (q : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hh.le
          apply Finset.sum_le_sum
          intro q _
          exact weighted_norm_majorant n b c d ν _ hb hν
        _ = (kernelScale n b c d / (min 1 b) ^ n) *
            (h * ∑ q ∈ Finset.Icc (-(N : ℤ)) N, cappedDensity β c (h * (q : ℝ))) := by
          rw [← Finset.mul_sum]
          ring
        _ ≤ (kernelScale n b c d / (min 1 b) ^ n) * (C * (1 + c ^ (β + 1))) :=
          mul_le_mul_of_nonneg_left hf hA
        _ = _ := by
          simp only [momentGrowth, if_neg hn, if_neg he]
          have hex : β + 1 = ν - n := by dsimp [β]; push_cast; ring
          rw [hex]
          ring

/-- The finite quadrature rule's weighted coefficient moments satisfy the three-regime
`kernelScale * C * momentGrowth` bound uniformly in the cutoff radius and mesh step in `(0,
1]`; see [AftabAnTrivisa2026]. -/
theorem finite_rule_moments (n : ℕ) (b ν : ℝ) (hb : 0 < b) (hν : 0 ≤ ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c → ∀ d h : ℝ, 0 < h → h ≤ 1 → ∀ R : ℝ,
      (∑ q ∈ Finset.Icc (-(cutoff R h : ℤ)) (cutoff R h : ℤ),
        ‖(h : ℂ) * coefficient n b c d ((h * (q : ℝ) : ℝ) : ℂ)‖ * |h * (q : ℝ)| ^ ν) ≤
          kernelScale n b c d * C * momentGrowth n ν c := by
  obtain ⟨C, hC, hm⟩ := moment_three_regimes n b ν hb hν
  refine ⟨C, hC, fun c hc d h hh hh1 R => ?_⟩
  rw [← moment_eq_weights n b c d ν h (cutoff R h) hh.le]
  exact hm c hc d h hh hh1 _

/-- The zeroth finite moment equals the sum of the quadrature coefficient norms for a
nonnegative mesh step. -/
theorem moment_zero_eq_norm_mass (n : ℕ) (b c d h : ℝ) (N : ℕ) (hh : 0 ≤ h) :
    moment n b c d 0 h N = ∑ q ∈ Finset.Icc (-(N : ℤ)) N,
      ‖(h : ℂ) * coefficient n b c d ((h * (q : ℝ) : ℝ) : ℂ)‖ := by
  rw [moment_eq_weights n b c d 0 h N hh]
  simp only [Real.rpow_zero, mul_one]

end Qatlib.Papers.CommutLCHS26.QuadratureCmp.Moments
