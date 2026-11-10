/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.KernelBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false

namespace CBMD

open Filter
open scoped BigOperators Topology

noncomputable def kernelNormalizedProduct (c : ℝ) (m : ℕ) : ℝ :=
  ∏ j ∈ Finset.range m, (1 + c ^ 2 / ((j : ℝ) + 1) ^ 2)

theorem kernelNormalizedProduct_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (kernelNormalizedProduct c) atTop
      (𝓝 (Real.sinh (Real.pi * c) / (Real.pi * c))) := by
  have hfactor (j : ℕ) :
      (1 : ℂ) - ((c : ℂ) * Complex.I) ^ 2 / ((j : ℂ) + 1) ^ 2 =
        ((1 + c ^ 2 / ((j : ℝ) + 1) ^ 2 : ℝ) : ℂ) := by
    push_cast
    simp only [mul_pow, Complex.I_sq, mul_neg_one, neg_div, sub_neg_eq_add]
  have hprod (n : ℕ) :
      (∏ j ∈ Finset.range n,
        ((1 : ℂ) - ((c : ℂ) * Complex.I) ^ 2 / ((j : ℂ) + 1) ^ 2)) =
        (kernelNormalizedProduct c n : ℂ) := by
    simp_rw [hfactor]
    simp only [kernelNormalizedProduct, Complex.ofReal_prod]
  have ht := (Complex.continuous_im.tendsto _).comp
    (Complex.tendsto_euler_sin_prod ((c : ℂ) * Complex.I))
  have hlim : Tendsto (fun n => (Real.pi * c) * kernelNormalizedProduct c n)
      atTop (𝓝 (Real.sinh (Real.pi * c))) := by
    convert ht using 1
    · funext n
      rw [Function.comp_apply, hprod]
      simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
    · rw [← mul_assoc, ← Complex.ofReal_mul, Complex.sin_mul_I]
      simp only [Complex.mul_im, Complex.I_im, Complex.I_re, mul_one, mul_zero,
        add_zero, Complex.sinh_ofReal_re]
  have hpc : Real.pi * c ≠ 0 := mul_ne_zero Real.pi_ne_zero hc.ne'
  convert hlim.div_const (Real.pi * c) using 1
  funext n
  field_simp

theorem kernelNormalizedProduct_le {c : ℝ} (hc : 0 < c) (m : ℕ) :
    kernelNormalizedProduct c m ≤ Real.sinh (Real.pi * c) / (Real.pi * c) := by
  apply ge_of_tendsto (kernelNormalizedProduct_tendsto hc)
  filter_upwards [eventually_ge_atTop m] with n hn
  apply Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.range_mono hn)
  · intro j _; positivity
  · intro j _ _; exact le_add_of_nonneg_right (by positivity)

theorem kernel_product_factorial (m : ℕ) (c : ℝ) :
    (∏ j ∈ Finset.range m, (((j : ℝ) + 1) ^ 2 + c ^ 2)) =
      (m.factorial : ℝ) ^ 2 * kernelNormalizedProduct c m := by
  have hfac : (∏ j ∈ Finset.range m, ((j : ℝ) + 1)) = (m.factorial : ℝ) := by
    exact_mod_cast Finset.prod_range_add_one_eq_factorial m
  rw [← hfac, ← Finset.prod_pow, kernelNormalizedProduct, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  have hj : ((j : ℝ) + 1) ≠ 0 := by positivity
  field_simp

theorem finite_euler_product_upper (m : ℕ) {c : ℝ} (hc : 0 < c) :
    (∏ j ∈ Finset.range m, (((j : ℝ) + 1) ^ 2 + c ^ 2)) ≤
      (m.factorial : ℝ) ^ 2 * (Real.sinh (Real.pi * c) / (Real.pi * c)) := by
  rw [kernel_product_factorial]
  exact mul_le_mul_of_nonneg_left (kernelNormalizedProduct_le hc m) (sq_nonneg _)

theorem regulator_numerator_ratio_upper (m : ℕ) (x : ℝ) :
    (∏ j ∈ Finset.range m, (((j : ℝ) + 1) ^ 2 + 4)) /
        (∏ r ∈ Finset.Icc (-(m : ℤ)) m, ‖(x : ℂ) - (r : ℂ) - Complex.I‖) ≤
      Real.sinh (Real.pi * 2) / (Real.pi * 2) := by
  have hn := finite_euler_product_upper m (c := 2) (by norm_num)
  norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num] at hn
  have hd := integer_regulator_product_lower m x
  have hf : 0 < (m.factorial : ℝ) ^ 2 :=
    pow_pos (Nat.cast_pos.mpr (Nat.factorial_pos m)) 2
  have hden := hf.trans_le hd
  have hC : 0 ≤ Real.sinh (Real.pi * 2) / (Real.pi * 2) := by
    have h := kernelNormalizedProduct_le (c := 2) (by norm_num) 0
    simp only [kernelNormalizedProduct, Finset.range_zero, Finset.prod_empty] at h
    exact (by norm_num : (0 : ℝ) ≤ 1).trans h
  apply (div_le_iff₀ hden).mpr
  exact hn.trans (by nlinarith [mul_le_mul_of_nonneg_right hd hC])

end CBMD

end Qatlib.Foundations.CbmdAnalysis.Core
