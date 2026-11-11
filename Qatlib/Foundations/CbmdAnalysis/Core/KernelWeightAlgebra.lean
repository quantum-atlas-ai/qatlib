/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.KernelUpper
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Algebra and norm bounds for integer weights

`integerRegulator` is normalized to one at `-i` and has its prescribed top and row zeros.
`integerWeight` combines this regulator with the target factor and the exponential normalization
needed for real lattice residues.

Exact product formulas for their norms lead to a uniform bound by `integerWeightConstant / (a *
(1 + x²))` at positive spacing. This supplies the integrable coefficient envelope used in
[WangEtAl2026].

## Main statements

* `integerRegulator_at_neg_I`: states the target normalization.
* `integerWeight_norm_le`: bounds the weights by a scaled Cauchy profile.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false

namespace CBMD

open scoped BigOperators

/-- The normalized polynomial regulator with top factor `(z - 2i) / (-3i)` and row factors `(z -
r - i) / (-r - 2i)` for `-m ≤ r ≤ m`. -/
noncomputable def integerRegulator (m : ℕ) (z : ℂ) : ℂ :=
  (z - 2 * Complex.I) / (-3 * Complex.I) *
    ∏ r ∈ Finset.Icc (-(m : ℤ)) m,
      (z - (r : ℂ) - Complex.I) / (-(r : ℂ) - 2 * Complex.I)

/-- The integer regulator takes the value one at the target `-i`. -/
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

/-- The scalar weight `(exp (-2πa) - 1) / (2πia * (x + i) * integerRegulator m x)` at a real
point `x`. -/
noncomputable def integerWeight (m : ℕ) (a x : ℝ) : ℂ :=
  (Real.exp (-2 * Real.pi * a) - 1 : ℝ) /
    (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) *
      ((x : ℂ) + Complex.I) * integerRegulator m x)

/-- The product of the norms of `r - 2i` and `-r - 2i` equals `r² + 4` for real `r`. -/
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

/-- The product of row normalization norms over `[-m, m]` equals twice the product of `(j + 1)²
+ 4` over `j < m`. -/
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

/-- For real `x`, the squared norm of `x + i` is `x² + 1`. -/
private theorem norm_plus_I_sq (x : ℝ) : ‖(x : ℂ) + Complex.I‖ ^ 2 = x ^ 2 + 1 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

/-- For real `x`, the squared norm of `x - 2i` is `x² + 4`. -/
private theorem norm_sub_two_I_sq (x : ℝ) : ‖(x : ℂ) - 2 * Complex.I‖ ^ 2 = x ^ 2 + 4 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

/-- At a real point, the regulator norm equals the top distance divided by three times the ratio
of row distances to their normalization product. -/
theorem integerRegulator_norm (m : ℕ) (x : ℝ) :
    ‖integerRegulator m x‖ =
      (‖(x : ℂ) - 2 * Complex.I‖ / 3) *
        ((∏ r ∈ Finset.Icc (-(m : ℤ)) m, ‖(x : ℂ) - (r : ℂ) - Complex.I‖) /
          (2 * ∏ j ∈ Finset.range m, (((j : ℝ) + 1) ^ 2 + 4))) := by
  simp only [integerRegulator, norm_mul, norm_div, norm_prod, norm_neg,
    Complex.norm_I, mul_one, Finset.prod_div_distrib]
  rw [integerRegulator_normalization_norm]
  norm_num

/-- For real `x`, the product `‖x + i‖ * ‖x - 2i‖` is at least `1 + x²`. -/
theorem integerWeight_outer_product_lower (x : ℝ) :
    1 + x ^ 2 ≤ ‖(x : ℂ) + Complex.I‖ * ‖(x : ℂ) - 2 * Complex.I‖ := by
  have h₁ := norm_plus_I_sq x
  have h₂ := norm_sub_two_I_sq x
  have h₁₀ := norm_nonneg ((x : ℂ) + Complex.I)
  have h₂₀ := norm_nonneg ((x : ℂ) - 2 * Complex.I)
  have hle : ‖(x : ℂ) + Complex.I‖ ≤ ‖(x : ℂ) - 2 * Complex.I‖ := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hle h₁₀]

/-- For positive spacing, the weight norm equals the stated product ratio with factor `(1 - exp
(-2πa)) * (3 / π)` and denominator `a * ‖x + i‖ * ‖x - 2i‖`. -/
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

/-- The universal weight bound constant `(3 / π) * (sinh (2π) / (2π))`. -/
noncomputable def integerWeightConstant : ℝ :=
  (3 / Real.pi) * (Real.sinh (Real.pi * 2) / (Real.pi * 2))

/-- The universal integer weight constant is nonnegative. -/
theorem integerWeightConstant_nonneg : 0 ≤ integerWeightConstant := by
  have h := kernelNormalizedProduct_le (c := 2) (by norm_num) 0
  simp only [kernelNormalizedProduct, Finset.range_zero, Finset.prod_empty] at h
  dsimp [integerWeightConstant]
  exact mul_nonneg (by positivity) (le_trans (by norm_num) h)

/-- For positive spacing, the integer weight norm is at most `integerWeightConstant / (a * (1 +
x²))`. -/
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
