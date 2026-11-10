/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.KernelUpper
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false

namespace CBMD

open scoped BigOperators

noncomputable def integerRegulator (m : ℕ) (z : ℂ) : ℂ :=
  (z - 2 * Complex.I) / (-3 * Complex.I) *
    ∏ r ∈ Finset.Icc (-(m : ℤ)) m,
      (z - (r : ℂ) - Complex.I) / (-(r : ℂ) - 2 * Complex.I)

theorem integerRegulator_at_neg_I (m : ℕ) : integerRegulator m (-Complex.I) = 1 := by
  have hd (r : ℤ) : -(r : ℂ) - 2 * Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  have h₀ : (-Complex.I - 2 * Complex.I) / (-3 * Complex.I) = 1 := by
    rw [show -Complex.I - 2 * Complex.I = -3 * Complex.I by ring]
    apply div_self
    simp
  rw [integerRegulator, h₀, one_mul]
  apply Finset.prod_eq_one
  intro r _
  rw [show -Complex.I - (r : ℂ) - Complex.I = -(r : ℂ) - 2 * Complex.I by ring]
  exact div_self (hd r)

noncomputable def integerWeight (m : ℕ) (a x : ℝ) : ℂ :=
  (Real.exp (-2 * Real.pi * a) - 1 : ℝ) /
    (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) *
      ((x : ℂ) + Complex.I) * integerRegulator m x)

private theorem normalization_pair (r : ℝ) :
    ‖(r : ℂ) - 2 * Complex.I‖ * ‖-(r : ℂ) - 2 * Complex.I‖ = r ^ 2 + 4 := by
  rw [← norm_mul]
  have he : ((r : ℂ) - 2 * Complex.I) * (-(r : ℂ) - 2 * Complex.I) =
      (-(r ^ 2 + 4 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    simp [Complex.I_sq]
    ring
  rw [he, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

theorem integerRegulator_normalization_norm (m : ℕ) :
    (∏ r ∈ Finset.Icc (-(m : ℤ)) m, ‖-(r : ℂ) - 2 * Complex.I‖) =
      2 * ∏ j ∈ Finset.range m, (((j : ℝ) + 1) ^ 2 + 4) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.cast_add, Nat.cast_one, Finset.Icc_succ_succ, Finset.prod_union (by simp)]
    rw [Finset.prod_pair (by omega), ih, Finset.prod_range_succ]
    simp only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, neg_neg]
    rw [show (m : ℂ) + 1 = ((m : ℝ) + 1 : ℝ) by push_cast; rfl]
    rw [normalization_pair]
    ring

private theorem norm_plus_I_sq (x : ℝ) : ‖(x : ℂ) + Complex.I‖ ^ 2 = x ^ 2 + 1 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

private theorem norm_sub_two_I_sq (x : ℝ) : ‖(x : ℂ) - 2 * Complex.I‖ ^ 2 = x ^ 2 + 4 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

theorem integerRegulator_norm (m : ℕ) (x : ℝ) :
    ‖integerRegulator m x‖ =
      (‖(x : ℂ) - 2 * Complex.I‖ / 3) *
        ((∏ r ∈ Finset.Icc (-(m : ℤ)) m, ‖(x : ℂ) - (r : ℂ) - Complex.I‖) /
          (2 * ∏ j ∈ Finset.range m, (((j : ℝ) + 1) ^ 2 + 4))) := by
  simp only [integerRegulator, norm_mul, norm_div, norm_prod, norm_neg,
    Complex.norm_I, mul_one, Finset.prod_div_distrib]
  rw [integerRegulator_normalization_norm]
  norm_num

theorem integerWeight_outer_product_lower (x : ℝ) :
    1 + x ^ 2 ≤ ‖(x : ℂ) + Complex.I‖ * ‖(x : ℂ) - 2 * Complex.I‖ := by
  have h₁ := norm_plus_I_sq x
  have h₂ := norm_sub_two_I_sq x
  have h₁₀ := norm_nonneg ((x : ℂ) + Complex.I)
  have h₂₀ := norm_nonneg ((x : ℂ) - 2 * Complex.I)
  have hle : ‖(x : ℂ) + Complex.I‖ ≤ ‖(x : ℂ) - 2 * Complex.I‖ := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hle h₁₀]

theorem integerWeight_norm (m : ℕ) {a : ℝ} (ha : 0 < a) (x : ℝ) :
    ‖integerWeight m a x‖ =
      (1 - Real.exp (-2 * Real.pi * a)) * (3 / Real.pi) *
        ((∏ j ∈ Finset.range m, (((j : ℝ) + 1) ^ 2 + 4)) /
          (∏ r ∈ Finset.Icc (-(m : ℤ)) m, ‖(x : ℂ) - (r : ℂ) - Complex.I‖)) /
        (a * (‖(x : ℂ) + Complex.I‖ * ‖(x : ℂ) - 2 * Complex.I‖)) := by
  have he : Real.exp (-2 * Real.pi * a) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith [Real.pi_pos]
  have hA : 0 < ∏ j ∈ Finset.range m, (((j : ℝ) + 1) ^ 2 + 4) :=
    Finset.prod_pos fun _ _ => by positivity
  have hD : 0 < ∏ r ∈ Finset.Icc (-(m : ℤ)) m, ‖(x : ℂ) - (r : ℂ) - Complex.I‖ :=
    (pow_pos (Nat.cast_pos.mpr (Nat.factorial_pos m)) 2).trans_le
      (integer_regulator_product_lower m x)
  have hp : 0 < ‖(x : ℂ) + Complex.I‖ := by
    have := norm_plus_I_sq x
    have := norm_nonneg ((x : ℂ) + Complex.I)
    nlinarith [sq_nonneg x]
  have hm : 0 < ‖(x : ℂ) - 2 * Complex.I‖ := by
    have := norm_sub_two_I_sq x
    have := norm_nonneg ((x : ℂ) - 2 * Complex.I)
    nlinarith [sq_nonneg x]
  rw [integerWeight, norm_div]
  simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, abs_of_pos ha, integerRegulator_norm]
  rw [abs_of_nonpos (sub_nonpos.mpr he)]
  norm_num
  field_simp

noncomputable def integerWeightConstant : ℝ :=
  (3 / Real.pi) * (Real.sinh (Real.pi * 2) / (Real.pi * 2))

theorem integerWeightConstant_nonneg : 0 ≤ integerWeightConstant := by
  have h := kernelNormalizedProduct_le (c := 2) (by norm_num) 0
  simp only [kernelNormalizedProduct, Finset.range_zero, Finset.prod_empty] at h
  dsimp [integerWeightConstant]
  exact mul_nonneg (by positivity) (le_trans (by norm_num) h)

theorem integerWeight_norm_le (m : ℕ) {a : ℝ} (ha : 0 < a) (x : ℝ) :
    ‖integerWeight m a x‖ ≤ integerWeightConstant / (a * (1 + x ^ 2)) := by
  rw [integerWeight_norm m ha x]
  have he1 : 1 - Real.exp (-2 * Real.pi * a) ≤ 1 := by
    linarith [Real.exp_pos (-2 * Real.pi * a)]
  have hR₀ : 0 ≤ (∏ j ∈ Finset.range m, (((j : ℝ) + 1) ^ 2 + 4)) /
      (∏ r ∈ Finset.Icc (-(m : ℤ)) m, ‖(x : ℂ) - (r : ℂ) - Complex.I‖) := by
    positivity
  have hnum := mul_le_mul
    (mul_le_mul_of_nonneg_right he1 (show 0 ≤ 3 / Real.pi by positivity))
    (regulator_numerator_ratio_upper m x) hR₀ (show 0 ≤ 1 * (3 / Real.pi) by positivity)
  simp only [one_mul] at hnum
  calc
    _ ≤ integerWeightConstant /
        (a * (‖(x : ℂ) + Complex.I‖ * ‖(x : ℂ) - 2 * Complex.I‖)) := by
      apply div_le_div_of_nonneg_right hnum
      positivity
    _ ≤ integerWeightConstant / (a * (1 + x ^ 2)) := by
      apply div_le_div_of_nonneg_left integerWeightConstant_nonneg (by positivity)
      exact mul_le_mul_of_nonneg_left (integerWeight_outer_product_lower x) ha.le

end CBMD

end Qatlib.Foundations.CbmdAnalysis.Core
