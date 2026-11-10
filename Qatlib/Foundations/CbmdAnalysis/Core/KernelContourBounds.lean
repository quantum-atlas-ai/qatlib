/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.KernelAuxiliary
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
namespace CBMD
open scoped BigOperators Topology
open Filter MeasureTheory

noncomputable def kernelNormalization (m : ℕ) : ℝ :=
  6 * ∏ j ∈ Finset.range m, (((j : ℝ) + 1) ^ 2 + 4)

theorem kernelNormalization_pos (m : ℕ) : 0 < kernelNormalization m := by
  unfold kernelNormalization
  positivity

noncomputable def integerContourKernel (m : ℕ) (a : ℝ) (z : ℂ) : ℂ :=
  (Real.exp (-2 * Real.pi * a) - 1 : ℝ) /
    ((z + Complex.I) * integerRegulator m z *
      (Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * z) - 1))

theorem integerRegulator_norm_complex (m : ℕ) (z : ℂ) :
    ‖integerRegulator m z‖ =
      (‖z - 2 * Complex.I‖ *
        ∏ r ∈ Finset.Icc (-(m : ℤ)) m, ‖z - (r : ℂ) - Complex.I‖) / kernelNormalization m := by
  simp only [integerRegulator, norm_mul, norm_div, norm_prod, norm_neg,
    Complex.norm_I, mul_one, Finset.prod_div_distrib, integerRegulator_normalization_norm]
  unfold kernelNormalization
  norm_num
  ring

theorem integerContourKernel_norm (m : ℕ) (a : ℝ) (z : ℂ) :
    ‖integerContourKernel m a z‖ =
      ‖latticePoleFactor a z‖ * kernelNormalization m /
        (‖z + Complex.I‖ * ‖z - 2 * Complex.I‖ *
          ∏ r ∈ Finset.Icc (-(m : ℤ)) m, ‖z - (r : ℂ) - Complex.I‖) := by
  simp only [integerContourKernel, latticePoleFactor, norm_div, norm_mul, norm_neg,
    integerRegulator_norm_complex]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

theorem latticePoleFactor_norm_le_lower {a : ℝ} (ha : 0 < a) (z : ℂ) (hz : z.im ≤ -1) :
    ‖latticePoleFactor a z‖ ≤ 1 := by
  let t : ℝ := 2 * Real.pi * a
  have ht : 0 < t := by dsimp [t]; positivity
  have hnorm : ‖Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * z)‖ =
      Real.exp (t * z.im) := by
    rw [Complex.norm_exp]
    congr 1
    simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    dsimp [t]
    ring
  have hden := norm_sub_norm_le 1
    (Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * z))
  rw [norm_one, hnorm, norm_sub_rev] at hden
  have he : Real.exp (t * z.im) ≤ Real.exp (-t) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have he1 : Real.exp (-t) < 1 := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (neg_neg_of_pos ht)
  have hdenpos : 0 < ‖Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * z) - 1‖ := by
    linarith
  rw [latticePoleFactor, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  have ht' : -2 * Real.pi * a = -t := by dsimp [t]; ring
  rw [ht', abs_of_nonpos (by linarith : Real.exp (-t) - 1 ≤ 0)]
  apply (div_le_one hdenpos).mpr
  linarith

theorem lattice_exponential_vertical {a : ℝ} (ha : 0 < a) (n : ℤ) (y : ℝ) :
    Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) *
      ((((n : ℝ) + 1 / 2) / a : ℝ) + (y : ℂ) * Complex.I)) =
      -(Real.exp (2 * Real.pi * a * y) : ℂ) := by
  have he : -2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) *
      ((((n : ℝ) + 1 / 2) / a : ℝ) + (y : ℂ) * Complex.I) =
      ((2 * Real.pi * a * y : ℝ) : ℂ) +
        ((-n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) - (Real.pi : ℂ) * Complex.I := by
    push_cast
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [he, Complex.exp_sub_pi_mul_I, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I, mul_one, ← Complex.ofReal_exp]

theorem latticePoleFactor_norm_vertical_bounds {a : ℝ} (ha : 0 < a) (n : ℤ) (y : ℝ) :
    let z : ℂ := ((((n : ℝ) + 1 / 2) / a : ℝ) : ℂ) + (y : ℂ) * Complex.I
    ‖latticePoleFactor a z‖ ≤ 1 ∧
      ‖latticePoleFactor a z‖ ≤ Real.exp (-2 * Real.pi * a * y) := by
  (try dsimp only)
  have hnum : ‖(-(Real.exp (-2 * Real.pi * a) - 1 : ℝ) : ℂ)‖ ≤ 1 := by
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]
    have h0 := Real.exp_pos (-2 * Real.pi * a)
    have h1 : Real.exp (-2 * Real.pi * a) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hden : ‖Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) *
      ((((n : ℝ) + 1 / 2) / a : ℝ) + (y : ℂ) * Complex.I)) - 1‖ =
      Real.exp (2 * Real.pi * a * y) + 1 := by
    rw [lattice_exponential_vertical ha]
    rw [show -(Real.exp (2 * Real.pi * a * y) : ℂ) - 1 =
      -((Real.exp (2 * Real.pi * a * y) + 1 : ℝ) : ℂ) by push_cast; ring]
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  simp only [latticePoleFactor, norm_div, hden]
  constructor
  · apply (div_le_one (by positivity)).mpr
    exact hnum.trans (by linarith [Real.exp_pos (2 * Real.pi * a * y)])
  · calc
      _ ≤ 1 / (Real.exp (2 * Real.pi * a * y) + 1) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ 1 / Real.exp (2 * Real.pi * a * y) :=
        div_le_div_of_nonneg_left (by norm_num) (Real.exp_pos _) (by linarith)
      _ = _ := by rw [show -2 * Real.pi * a * y = -(2 * Real.pi * a * y) by ring, Real.exp_neg]; exact one_div _

theorem contour_denominator_vertical_lower (m : ℕ) (z : ℂ) (hz : m < |z.re|) :
    (|z.re| - m) ^ (2 * m + 3) ≤
      ‖z + Complex.I‖ * ‖z - 2 * Complex.I‖ *
        ∏ r ∈ Finset.Icc (-(m : ℤ)) m, ‖z - (r : ℂ) - Complex.I‖ := by
  have hd : 0 < |z.re| - m := sub_pos.mpr hz
  have hc : (Finset.Icc (-(m : ℤ)) m).card = 2 * m + 1 := by rw [Int.card_Icc]; omega
  have hp : (|z.re| - m) ^ (2 * m + 1) ≤
      ∏ r ∈ Finset.Icc (-(m : ℤ)) m, ‖z - (r : ℂ) - Complex.I‖ := by
    calc
      _ = ∏ _r ∈ Finset.Icc (-(m : ℤ)) m, (|z.re| - m) := by simp only [Finset.prod_const, hc]
      _ ≤ _ := by
        apply Finset.prod_le_prod₀ (fun _ _ => hd.le)
        intro r hr
        have hr' := Finset.mem_Icc.mp hr
        have hrabs : |(r : ℝ)| ≤ m := by
          apply abs_le.mpr
          constructor
          · exact_mod_cast hr'.1
          · exact_mod_cast hr'.2
        have ht := abs_sub_abs_le_abs_sub z.re (r : ℝ)
        have hn := Complex.abs_re_le_norm (z - (r : ℂ) - Complex.I)
        simp only [Complex.sub_re, Complex.intCast_re, Complex.I_re, sub_zero] at hn
        linarith
  have h₁ : |z.re| - m ≤ ‖z + Complex.I‖ := by
    have h := Complex.abs_re_le_norm (z + Complex.I)
    simp only [Complex.add_re, Complex.I_re, add_zero] at h
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have h₂ : |z.re| - m ≤ ‖z - 2 * Complex.I‖ := by
    have h := Complex.abs_re_le_norm (z - 2 * Complex.I)
    norm_num at h
    linarith [Nat.cast_nonneg (α := ℝ) m]
  calc
    _ = ((|z.re| - m) * (|z.re| - m)) * (|z.re| - m) ^ (2 * m + 1) := by
      rw [show 2 * m + 3 = (2 * m + 1) + 2 by omega, pow_add, pow_two]
      ring
    _ ≤ _ := mul_le_mul (mul_le_mul h₁ h₂ hd.le (norm_nonneg _)) hp
      (by positivity) (by positivity)

theorem contour_denominator_horizontal_lower (m : ℕ) (z : ℂ) (hz : 3 ≤ |z.im|) :
    z.re ^ 2 + (|z.im| - 2) ^ 2 ≤
      ‖z + Complex.I‖ * ‖z - 2 * Complex.I‖ *
        ∏ r ∈ Finset.Icc (-(m : ℤ)) m, ‖z - (r : ℂ) - Complex.I‖ := by
  have hp : 1 ≤ ∏ r ∈ Finset.Icc (-(m : ℤ)) m, ‖z - (r : ℂ) - Complex.I‖ := by
    apply Finset.one_le_prod₀
    intro r _
    have ht := abs_sub_abs_le_abs_sub z.im 1
    have hn := Complex.abs_im_le_norm (z - (r : ℂ) - Complex.I)
    simp only [Complex.sub_im, Complex.intCast_im, Complex.I_im, sub_zero] at hn
    norm_num at ht
    linarith
  have h₁ : ‖z + Complex.I‖ ^ 2 = z.re ^ 2 + (z.im + 1) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have h₂ : ‖z - 2 * Complex.I‖ ^ 2 = z.re ^ 2 + (z.im - 2) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    norm_num
    ring
  have hs₁ : (|z.im| - 2) ^ 2 ≤ (z.im + 1) ^ 2 := by
    nlinarith [sq_abs z.im, neg_le_abs z.im]
  have hs₂ : (|z.im| - 2) ^ 2 ≤ (z.im - 2) ^ 2 := by
    nlinarith [sq_abs z.im, le_abs_self z.im]
  have hb : 0 ≤ z.re ^ 2 + (|z.im| - 2) ^ 2 := by positivity
  have hsq := Real.sq_sqrt hb
  have hsq₀ := Real.sqrt_nonneg (z.re ^ 2 + (|z.im| - 2) ^ 2)
  have hn₁ := norm_nonneg (z + Complex.I)
  have hn₂ := norm_nonneg (z - 2 * Complex.I)
  have hsqrt₁ : Real.sqrt (z.re ^ 2 + (|z.im| - 2) ^ 2) ≤ ‖z + Complex.I‖ := by nlinarith
  have hsqrt₂ : Real.sqrt (z.re ^ 2 + (|z.im| - 2) ^ 2) ≤ ‖z - 2 * Complex.I‖ := by nlinarith
  have ho : z.re ^ 2 + (|z.im| - 2) ^ 2 ≤ ‖z + Complex.I‖ * ‖z - 2 * Complex.I‖ := by
    nlinarith [mul_le_mul hsqrt₁ hsqrt₂ hsq₀ hn₁]
  exact ho.trans (by nlinarith [mul_nonneg hn₁ hn₂])

private theorem lattice_times_growth_le {a ρ y N : ℝ} (hρ : ρ ≤ 2 * Real.pi * a)
    (hN : N ≤ 1) (hNe : N ≤ Real.exp (-2 * Real.pi * a * y)) :
    N * Real.exp (max y 0 * ρ) ≤ 1 := by
  by_cases hy : y ≤ 0
  · simpa only [max_eq_right hy, zero_mul, Real.exp_zero, mul_one] using hN
  · have hy0 : 0 ≤ y := le_of_not_ge hy
    rw [max_eq_left hy0]
    calc
      _ ≤ Real.exp (-2 * Real.pi * a * y) * Real.exp (y * ρ) :=
        mul_le_mul_of_nonneg_right hNe (Real.exp_pos _).le
      _ = Real.exp (-2 * Real.pi * a * y + y * ρ) := (Real.exp_add _ _).symm
      _ ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)

section Integrand
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

noncomputable def integerContourIntegrand (m : ℕ) (a : ℝ) (U : ℂ → E) (z : ℂ) : E :=
  integerContourKernel m a z • U z

private theorem contour_norm_le_of_lattice_growth (m : ℕ) (a : ℝ) (U : ℂ → E) (z : ℂ)
    {d : ℝ} (hd : 0 < d)
    (hden : d ≤ ‖z + Complex.I‖ * ‖z - 2 * Complex.I‖ *
      ∏ r ∈ Finset.Icc (-(m : ℤ)) m, ‖z - (r : ℂ) - Complex.I‖)
    (hLU : ‖latticePoleFactor a z‖ * ‖U z‖ ≤ 1) :
    ‖integerContourIntegrand m a U z‖ ≤ kernelNormalization m / d := by
  rw [integerContourIntegrand, norm_smul, integerContourKernel_norm]
  have hnorm : ‖latticePoleFactor a z‖ * kernelNormalization m /
      (‖z + Complex.I‖ * ‖z - 2 * Complex.I‖ *
        ∏ r ∈ Finset.Icc (-(m : ℤ)) m, ‖z - (r : ℂ) - Complex.I‖) * ‖U z‖ =
      kernelNormalization m * (‖latticePoleFactor a z‖ * ‖U z‖) /
      (‖z + Complex.I‖ * ‖z - 2 * Complex.I‖ *
        ∏ r ∈ Finset.Icc (-(m : ℤ)) m, ‖z - (r : ℂ) - Complex.I‖) := by ring
  rw [hnorm]
  calc
    _ ≤ kernelNormalization m /
      (‖z + Complex.I‖ * ‖z - 2 * Complex.I‖ *
        ∏ r ∈ Finset.Icc (-(m : ℤ)) m, ‖z - (r : ℂ) - Complex.I‖) := by
      apply div_le_div_of_nonneg_right _ (hd.trans_le hden).le
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hLU (kernelNormalization_pos m).le
    _ ≤ _ := div_le_div_of_nonneg_left (kernelNormalization_pos m).le hd hden

theorem integerContourIntegrand_vertical_le (m : ℕ) {a ρ : ℝ} (ha : 0 < a)
    (hρ : ρ ≤ 2 * Real.pi * a) (U : ℂ → E)
    (hU : ∀ z, ‖U z‖ ≤ Real.exp (max z.im 0 * ρ)) (n : ℤ) (y : ℝ)
    (hx : (m : ℝ) < |((n : ℝ) + 1 / 2) / a|) :
    let z : ℂ := ((((n : ℝ) + 1 / 2) / a : ℝ) : ℂ) + (y : ℂ) * Complex.I
    ‖integerContourIntegrand m a U z‖ ≤
      kernelNormalization m / (|((n : ℝ) + 1 / 2) / a| - m) ^ (2 * m + 3) := by
  (try dsimp only)
  let z : ℂ := ((((n : ℝ) + 1 / 2) / a : ℝ) : ℂ) + (y : ℂ) * Complex.I
  have hre : z.re = ((n : ℝ) + 1 / 2) / a := by simp [z]
  have him : z.im = y := by simp [z]
  have hb := latticePoleFactor_norm_vertical_bounds ha n y
  refine contour_norm_le_of_lattice_growth m a U z (pow_pos (sub_pos.mpr hx) _) ?_ ?_
  · simpa only [hre] using contour_denominator_vertical_lower m z (by simpa only [hre] using hx)
  · calc
      _ ≤ ‖latticePoleFactor a z‖ * Real.exp (max y 0 * ρ) := by
        simpa only [him] using mul_le_mul_of_nonneg_left (hU z) (norm_nonneg _)
      _ ≤ 1 := lattice_times_growth_le hρ hb.1 hb.2

theorem integerContourIntegrand_horizontal_le (m : ℕ) {a ρ : ℝ} (ha : 0 < a)
    (hρ : ρ ≤ 2 * Real.pi * a) (U : ℂ → E)
    (hU : ∀ z, ‖U z‖ ≤ Real.exp (max z.im 0 * ρ)) (z : ℂ) (hz : 3 ≤ |z.im|) :
    ‖integerContourIntegrand m a U z‖ ≤
      kernelNormalization m / (z.re ^ 2 + (|z.im| - 2) ^ 2) := by
  have hd : 0 < z.re ^ 2 + (|z.im| - 2) ^ 2 := by nlinarith [sq_nonneg z.re]
  apply contour_norm_le_of_lattice_growth m a U z hd (contour_denominator_horizontal_lower m z hz)
  have ht : 0 < 2 * Real.pi * a := by positivity
  have hb : ‖latticePoleFactor a z‖ ≤ 1 ∧
      ‖latticePoleFactor a z‖ ≤ Real.exp (-2 * Real.pi * a * z.im) := by
    by_cases hy : 0 ≤ z.im
    · have hy1 : 1 ≤ z.im := by rw [abs_of_nonneg hy] at hz; linarith
      have h := latticePoleFactor_norm_le ha z hy1
      refine ⟨h.trans ?_, h⟩
      exact Real.exp_le_one_iff.mpr (by nlinarith)
    · have hy1 : z.im ≤ -1 := by rw [abs_of_neg (lt_of_not_ge hy)] at hz; linarith
      have h := latticePoleFactor_norm_le_lower ha z hy1
      refine ⟨h, h.trans ?_⟩
      exact Real.one_le_exp_iff.mpr (by nlinarith)
  calc
    _ ≤ ‖latticePoleFactor a z‖ * Real.exp (max z.im 0 * ρ) :=
      mul_le_mul_of_nonneg_left (hU z) (norm_nonneg _)
    _ ≤ 1 := lattice_times_growth_le hρ hb.1 hb.2
variable [NormedSpace ℝ E]

theorem integerContour_vertical_integral_le (m : ℕ) {a ρ : ℝ} (ha : 0 < a)
    (hρ : ρ ≤ 2 * Real.pi * a) (U : ℂ → E)
    (hU : ∀ z, ‖U z‖ ≤ Real.exp (max z.im 0 * ρ)) (n : ℤ) (b c : ℝ)
    (hx : (m : ℝ) < |((n : ℝ) + 1 / 2) / a|) :
    ‖∫ y in b..c, Complex.I • integerContourIntegrand m a U
      (((((n : ℝ) + 1 / 2) / a : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      kernelNormalization m / (|((n : ℝ) + 1 / 2) / a| - m) ^ (2 * m + 3) * |c - b| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro y _
  rw [norm_smul, Complex.norm_I, one_mul]
  exact integerContourIntegrand_vertical_le m ha hρ U hU n y hx

theorem integerContour_horizontal_integral_le (m : ℕ) {a ρ : ℝ} (ha : 0 < a)
    (hρ : ρ ≤ 2 * Real.pi * a) (U : ℂ → E)
    (hU : ∀ z, ‖U z‖ ≤ Real.exp (max z.im 0 * ρ)) (y b c : ℝ) (hy : 3 ≤ |y|) :
    ‖∫ x in b..c, integerContourIntegrand m a U ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      kernelNormalization m * Real.pi / (|y| - 2) := by
  have hd : 0 < |y| - 2 := by linarith
  have hcont : Continuous (fun x : ℝ => kernelNormalization m / (x ^ 2 + (|y| - 2) ^ 2)) := by
    apply continuous_const.div ((continuous_id.pow 2).add continuous_const)
    intro x
    change x ^ 2 + (|y| - 2) ^ 2 ≠ 0
    exact ne_of_gt (by nlinarith [sq_nonneg x])
  have hbound : ∀ x : ℝ,
      ‖integerContourIntegrand m a U ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
        kernelNormalization m / (x ^ 2 + (|y| - 2) ^ 2) := by
    intro x
    simpa using integerContourIntegrand_horizontal_le m ha hρ U hU
      ((x : ℂ) + (y : ℂ) * Complex.I) (by simpa using hy)
  have hi := intervalIntegral.norm_integral_le_abs_of_norm_le (μ := volume) (a := b) (b := c)
    (Filter.Eventually.of_forall hbound) (hcont.intervalIntegrable b c)
  have heq : (∫ x in b..c, kernelNormalization m / (x ^ 2 + (|y| - 2) ^ 2)) =
      kernelNormalization m * ((|y| - 2)⁻¹ *
        (Real.arctan (c / (|y| - 2)) - Real.arctan (b / (|y| - 2)))) := by
    have hf : (fun x : ℝ => kernelNormalization m / (x ^ 2 + (|y| - 2) ^ 2)) =
        (fun x => kernelNormalization m * ((|y| - 2) ^ 2 + x ^ 2)⁻¹) := by
      funext x
      rw [add_comm]
      rfl
    rw [hf, intervalIntegral.integral_const_mul, integral_inv_sq_add_sq hd.ne']
  rw [heq, abs_mul, abs_mul, abs_of_pos (kernelNormalization_pos m),
      abs_of_pos (inv_pos.mpr hd)] at hi
  have hat : |Real.arctan (c / (|y| - 2)) - Real.arctan (b / (|y| - 2))| ≤ Real.pi := by
    apply abs_le.mpr
    constructor <;> linarith [Real.arctan_lt_pi_div_two (c / (|y| - 2)),
      Real.neg_pi_div_two_lt_arctan (c / (|y| - 2)),
      Real.arctan_lt_pi_div_two (b / (|y| - 2)),
      Real.neg_pi_div_two_lt_arctan (b / (|y| - 2))]
  apply hi.trans
  have hmul := mul_le_mul_of_nonneg_left hat
    (mul_nonneg (kernelNormalization_pos m).le (inv_nonneg.mpr hd.le))
  convert! hmul using 1 <;> ring

theorem integerContour_horizontal_integrals_tendsto_zero (m : ℕ) {a ρ : ℝ} (ha : 0 < a)
    (hρ : ρ ≤ 2 * Real.pi * a) (U : ℂ → E)
    (hU : ∀ z, ‖U z‖ ≤ Real.exp (max z.im 0 * ρ)) (b c : ℝ → ℝ) :
    Tendsto (fun Y : ℝ => ∫ x in b Y..c Y,
      integerContourIntegrand m a U ((x : ℂ) + (Y : ℂ) * Complex.I)) atTop (𝓝 0) ∧
    Tendsto (fun Y : ℝ => ∫ x in b Y..c Y,
      integerContourIntegrand m a U ((x : ℂ) + (-Y : ℂ) * Complex.I)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun Y : ℝ => kernelNormalization m * Real.pi / (Y - 2)) atTop (𝓝 0) := by
    apply tendsto_const_nhds.div_atTop
    simpa only [sub_eq_add_neg] using! tendsto_atTop_add_const_right atTop (-2 : ℝ) tendsto_id
  constructor
  · apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_ge_atTop (3 : ℝ)] with Y hY
    have h := integerContour_horizontal_integral_le m ha hρ U hU Y (b Y) (c Y)
      (by rw [abs_of_nonneg (by linarith : 0 ≤ Y)]; exact hY)
    simpa only [abs_of_nonneg (by linarith : 0 ≤ Y)] using h
  · apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_ge_atTop (3 : ℝ)] with Y hY
    have h := integerContour_horizontal_integral_le m ha hρ U hU (-Y) (b Y) (c Y)
      (by rw [abs_neg, abs_of_nonneg (by linarith : 0 ≤ Y)]; exact hY)
    simpa only [Complex.ofReal_neg, abs_neg, abs_of_nonneg (by linarith : 0 ≤ Y)] using h

theorem integerContour_vertical_integrals_tendsto_zero (m : ℕ) {a ρ : ℝ} (ha : 0 < a)
    (hρ : ρ ≤ 2 * Real.pi * a) (U : ℂ → E)
    (hU : ∀ z, ‖U z‖ ≤ Real.exp (max z.im 0 * ρ)) (b c : ℝ) :
    Tendsto (fun n : ℕ => ∫ y in b..c, Complex.I • integerContourIntegrand m a U
      (((((n : ℝ) + 1 / 2) / a : ℝ) : ℂ) + (y : ℂ) * Complex.I)) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => ∫ y in b..c, Complex.I • integerContourIntegrand m a U
      ((-(((n : ℝ) + 1 / 2) / a) : ℝ) + (y : ℂ) * Complex.I)) atTop (𝓝 0) := by
  let R : ℕ → ℝ := fun n => ((n : ℝ) + 1 / 2) / a
  have hR : Tendsto R atTop atTop :=
    (tendsto_atTop_add_const_right atTop (1 / 2 : ℝ)
      (tendsto_natCast_atTop_atTop (R := ℝ))).atTop_div_const ha
  have hRpos (n : ℕ) : 0 ≤ R n := by dsimp [R]; positivity
  have hd : Tendsto (fun n => R n - m) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-(m : ℝ)) hR
  have hp : Tendsto (fun n => (R n - m) ^ (2 * m + 3)) atTop atTop :=
    (tendsto_pow_atTop (by omega : 2 * m + 3 ≠ 0)).comp hd
  have hlim : Tendsto (fun n => kernelNormalization m / (R n - m) ^ (2 * m + 3) * |c - b|)
      atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_const_nhds.div_atTop hp).mul_const |c - b|
  constructor
  · apply squeeze_zero_norm' _ hlim
    filter_upwards [hR.eventually_gt_atTop m] with n hn
    have hRn : 0 ≤ ((n : ℝ) + 1 / 2) / a := hRpos n
    have h := integerContour_vertical_integral_le m ha hρ U hU (n : ℤ) b c
      (by simpa only [Int.cast_natCast, abs_of_nonneg hRn] using hn)
    simpa only [Int.cast_natCast, abs_of_nonneg hRn] using h
  · apply squeeze_zero_norm' _ hlim
    filter_upwards [hR.eventually_gt_atTop m] with n hn
    have he : (((-(n : ℤ) - 1 : ℤ) : ℝ) + 1 / 2) / a = -R n := by
      dsimp [R]
      push_cast
      ring
    have h := integerContour_vertical_integral_le m ha hρ U hU (-(n : ℤ) - 1) b c
      (by rw [he, abs_neg, abs_of_nonneg (hRpos n)]; exact hn)
    simpa only [he, abs_neg, abs_of_nonneg (hRpos n)] using h
end Integrand

end CBMD

end Qatlib.Foundations.CbmdAnalysis.Core
