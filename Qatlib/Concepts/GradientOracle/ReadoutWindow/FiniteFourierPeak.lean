/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Concepts.GradientOracle.ReadoutWindow

lemma natCast_ne_zero {N : ℕ} (hN : 1 ≤ N) : (N : ℂ) ≠ 0 := by
  have h : N ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hN)
  exact_mod_cast h

def zeta (N : ℕ) (y : ℝ) : ℂ :=
  Complex.exp (Complex.I * (((2 * Real.pi * y) / (N : ℝ) : ℝ) : ℂ))

def fourierAmp (N : ℕ) (y : ℝ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ j ∈ Finset.range N, zeta N y ^ j

lemma norm_two_mul_sin (t : ℝ) : ‖2 * Real.sin t‖ = 2 * |Real.sin t| := by
  rw [Real.norm_eq_abs, abs_mul]
  norm_num

theorem zeta_pow (N : ℕ) (y : ℝ) (hN : 1 ≤ N) :
    zeta N y ^ N = Complex.exp (Complex.I * (((2 * Real.pi * y : ℝ) : ℂ))) := by
  unfold zeta
  rw [← Complex.exp_nat_mul]
  apply congrArg Complex.exp
  have hNc : (N : ℂ) ≠ 0 := natCast_ne_zero hN
  have hNa : (N : ℂ) * (((2 * Real.pi * y) / (N : ℝ) : ℝ) : ℂ)
      = (((2 * Real.pi * y : ℝ)) : ℂ) := by
    push_cast
    field_simp
  calc (N : ℂ) * (Complex.I * (((2 * Real.pi * y) / (N : ℝ) : ℝ) : ℂ))
      = Complex.I * ((N : ℂ) * (((2 * Real.pi * y) / (N : ℝ) : ℝ) : ℂ)) := by ring
    _ = Complex.I * (((2 * Real.pi * y : ℝ)) : ℂ) := by rw [hNa]

theorem norm_zeta_pow_sub_one (N : ℕ) (y : ℝ) (hN : 1 ≤ N) :
    ‖zeta N y ^ N - 1‖ = 2 * |Real.sin (Real.pi * y)| := by
  rw [zeta_pow N y hN]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [norm_two_mul_sin]
  congr 2
  ring

theorem norm_zeta_sub_one (N : ℕ) (y : ℝ) :
    ‖zeta N y - 1‖ = 2 * |Real.sin (Real.pi * y / (N : ℝ))| := by
  unfold zeta
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [norm_two_mul_sin]
  congr 2
  ring

theorem sin_div_ne_zero (N : ℕ) (y : ℝ) (hN : 1 ≤ N) (hy : y ≠ 0) (hy2 : |y| ≤ 1 / 2) :
    Real.sin (Real.pi * y / (N : ℝ)) ≠ 0 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hxabs : |Real.pi * y / (N : ℝ)| ≤ Real.pi / 2 := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hNpos]
    rw [div_le_iff₀ hNpos]
    nlinarith [Real.pi_pos, abs_nonneg y, hy2,
      show (1 : ℝ) ≤ (N : ℝ) by exact_mod_cast hN]
  have hx_lt : -Real.pi < Real.pi * y / (N : ℝ) := by
    have := (abs_le.mp hxabs).1; linarith [Real.pi_pos]
  have hx_gt : Real.pi * y / (N : ℝ) < Real.pi := by
    have := (abs_le.mp hxabs).2; linarith [Real.pi_pos]
  intro hz
  rw [Real.sin_eq_zero_iff_of_lt_of_lt hx_lt hx_gt] at hz
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hmul : Real.pi * y = 0 := by
    field_simp at hz
    linarith [hz]
  exact hy ((mul_eq_zero.mp hmul).resolve_left Real.pi_ne_zero)

theorem fourierAmp_norm_eq (N : ℕ) (y : ℝ) (hN : 1 ≤ N) (hy : y ≠ 0) (hy2 : |y| ≤ 1 / 2) :
    ‖fourierAmp N y‖
      = |Real.sin (Real.pi * y)| / ((N : ℝ) * |Real.sin (Real.pi * y / (N : ℝ))|) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hsin_ne := sin_div_ne_zero N y hN hy hy2
  have hbne : |Real.sin (Real.pi * y / (N : ℝ))| ≠ 0 := abs_ne_zero.mpr hsin_ne
  have hden_pos : 0 < ‖zeta N y - 1‖ := by
    rw [norm_zeta_sub_one]
    exact mul_pos (by norm_num) (abs_pos.mpr hsin_ne)
  have hmul : (zeta N y - 1) * (∑ j ∈ Finset.range N, zeta N y ^ j) = zeta N y ^ N - 1 :=
    mul_geom_sum (zeta N y) N
  have hsum_norm : ‖∑ j ∈ Finset.range N, zeta N y ^ j‖
      = ‖zeta N y ^ N - 1‖ / ‖zeta N y - 1‖ := by
    have hfac : ‖(zeta N y - 1) * (∑ j ∈ Finset.range N, zeta N y ^ j)‖
        = ‖zeta N y - 1‖ * ‖∑ j ∈ Finset.range N, zeta N y ^ j‖ := norm_mul _ _
    have hval : ‖(zeta N y - 1) * (∑ j ∈ Finset.range N, zeta N y ^ j)‖
        = ‖zeta N y ^ N - 1‖ := by rw [hmul]
    have hne : ‖zeta N y - 1‖ ≠ 0 := ne_of_gt hden_pos
    have hkey : ‖zeta N y ^ N - 1‖
        = ‖zeta N y - 1‖ * ‖∑ j ∈ Finset.range N, zeta N y ^ j‖ :=
      hval.symm.trans hfac
    rw [hkey]
    field_simp
  have hNr : ‖(N : ℂ)‖ = (N : ℝ) := by
    rw [← Complex.ofReal_natCast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg N)]
  unfold fourierAmp
  rw [norm_mul, norm_inv, hNr, hsum_norm, norm_zeta_pow_sub_one N y hN,
    norm_zeta_sub_one, inv_eq_one_div]
  field_simp [hNne, hbne]

theorem fourierAmp_norm_ge_two_div_pi (N : ℕ) (y : ℝ) (hN : 1 ≤ N)
    (hy : y ≠ 0) (hy2 : |y| ≤ 1 / 2) :
    2 / Real.pi ≤ ‖fourierAmp N y‖ := by
  rw [fourierAmp_norm_eq N y hN hy hy2]
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hypos : 0 < |y| := abs_pos.mpr hy
  have hsin_ne := sin_div_ne_zero N y hN hy hy2
  have hden_pos : 0 < (N : ℝ) * |Real.sin (Real.pi * y / (N : ℝ))| :=
    mul_pos hNpos (abs_pos.mpr hsin_ne)
  have hnum_ge : 2 * |y| ≤ |Real.sin (Real.pi * y)| := by
    have hxabs : |Real.pi * y| ≤ Real.pi / 2 := by
      rw [abs_mul, abs_of_pos Real.pi_pos]; nlinarith [Real.pi_pos, hy2]
    have hsin := Real.mul_abs_le_abs_sin hxabs
    rw [abs_mul, abs_of_pos Real.pi_pos] at hsin
    have heq : 2 / Real.pi * (Real.pi * |y|) = 2 * |y| := by field_simp
    rwa [heq] at hsin
  have hden_le : (N : ℝ) * |Real.sin (Real.pi * y / (N : ℝ))| ≤ Real.pi * |y| := by
    have h := Real.abs_sin_le_abs (x := Real.pi * y / (N : ℝ))
    have habs : |Real.pi * y / (N : ℝ)| = Real.pi * |y| / (N : ℝ) := by
      rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hNpos]
    rw [habs] at h
    have heq : (N : ℝ) * (Real.pi * |y| / (N : ℝ)) = Real.pi * |y| := by field_simp
    nlinarith [h, heq, hNpos, abs_nonneg y, Real.pi_pos]
  rw [show 2 / Real.pi = (2 * |y|) / (Real.pi * |y|) by
    field_simp]
  rw [div_le_div_iff₀ (by positivity : 0 < Real.pi * |y|) hden_pos]
  nlinarith [hnum_ge, hden_le, abs_nonneg (Real.sin (Real.pi * y)),
    abs_nonneg y, Real.pi_pos, hypos]

theorem prob_ge_four_div_pi_sq (N : ℕ) (y : ℝ) (hN : 1 ≤ N)
    (hy : y ≠ 0) (hy2 : |y| ≤ 1 / 2) :
    4 / Real.pi ^ 2 ≤ ‖fourierAmp N y‖ ^ 2 := by
  have h := fourierAmp_norm_ge_two_div_pi N y hN hy hy2
  have hnon : 0 ≤ 2 / Real.pi := by positivity
  have h2 : (2 / Real.pi) ^ 2 ≤ ‖fourierAmp N y‖ ^ 2 :=
    pow_le_pow_left₀ hnon h 2
  calc 4 / Real.pi ^ 2 = (2 / Real.pi) ^ 2 := by field_simp; ring
    _ ≤ ‖fourierAmp N y‖ ^ 2 := h2

theorem fourierAmp_zero (N : ℕ) (hN : 1 ≤ N) : fourierAmp N 0 = 1 := by
  unfold fourierAmp
  have hz : zeta N 0 = 1 := by unfold zeta; simp
  rw [hz]
  simp only [one_pow]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hNne : (N : ℂ) ≠ 0 := natCast_ne_zero hN
  rw [mul_one]
  field_simp

lemma exp_two_pi_I : Complex.exp (Complex.I * (((2 * Real.pi : ℝ) : ℂ))) = 1 := by
  have h : Complex.I * (((2 * Real.pi : ℝ) : ℂ)) = 2 * (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_two_pi_mul_I]

theorem zeta_add_N (N : ℕ) (y : ℝ) (hN : 1 ≤ N) : zeta N (y + N) = zeta N y := by
  unfold zeta
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hargR : (2 * Real.pi * (y + N)) / (N : ℝ)
      = (2 * Real.pi * y) / (N : ℝ) + 2 * Real.pi := by
    field_simp
  have harg : Complex.I * (((2 * Real.pi * (y + N)) / (N : ℝ) : ℝ) : ℂ)
      = Complex.I * (((2 * Real.pi * y) / (N : ℝ) : ℝ) : ℂ)
        + Complex.I * (((2 * Real.pi : ℝ)) : ℂ) := by
    rw [hargR]
    push_cast
    ring
  rw [harg, Complex.exp_add, exp_two_pi_I, mul_one]

theorem fourierAmp_period (N : ℕ) (y : ℝ) (hN : 1 ≤ N) :
    fourierAmp N (y + N) = fourierAmp N y := by
  unfold fourierAmp
  rw [zeta_add_N N y hN]

def jointAmp {d : ℕ} (N : Fin d → ℕ) (y : Fin d → ℝ) : ℂ :=
  ∏ i, fourierAmp (N i) (y i)

theorem joint_prob_eq_prod {d : ℕ} (N : Fin d → ℕ) (y : Fin d → ℝ) :
    ‖jointAmp N y‖ ^ 2 = ∏ i, ‖fourierAmp (N i) (y i)‖ ^ 2 := by
  unfold jointAmp
  rw [norm_prod, ← Finset.prod_pow]

end Qatlib.Concepts.GradientOracle.ReadoutWindow
