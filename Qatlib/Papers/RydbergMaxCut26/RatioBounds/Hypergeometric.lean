/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Rational bounds for the rounding hypergeometric function

`coeff` specializes the ordinary hypergeometric coefficients to parameters (1/2, 1/2; 5/2).
Positivity, recurrence, and inverse-square coefficient bounds prove convergence on [0, 1] and
explicit lower and upper estimates; these yield polynomial bounds for the signed factor and
rational bounds on the normalization constant.

These results support the development of [CrostaSaubanereHuber2026].

## Main statements

* `series_summable`: proves summability up to parameter one.
* `hyper_lower` and `hyper_upper_81_80`: bound the hypergeometric factor.
* `rounding_constant_bounds`: encloses 8/(3π) between rational constants.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option autoImplicit false
noncomputable section
open Polynomial
namespace Qatlib.Papers.RydbergMaxCut26.RatioBounds.Hypergeom
/-- The coefficient of degree `n` for the ordinary hypergeometric parameters (1/2, 1/2; 5/2). -/
abbrev coeff (n : ℕ) : ℝ := ordinaryHypergeometricCoefficient (1/2 : ℝ) (1/2) (5/2) n

/-- The hypergeometric function with parameters (1/2, 1/2; 5/2) equals the infinite sum of
`coeff n * z^n`. -/
lemma true_series (z : ℝ) :
    ₂F₁ (1/2 : ℝ) (1/2) (5/2) z = ∑' n : ℕ, coeff n * z ^ n := by
  rw [ordinaryHypergeometric_eq_tsum]
  rfl

/-- The constant hypergeometric coefficient is one. -/
lemma coeff_zero : coeff 0 = 1 := by norm_num [coeff, ordinaryHypergeometricCoefficient]

/-- The degree-one hypergeometric coefficient is 1/10. -/
lemma coeff_one : coeff 1 = 1/10 := by norm_num [coeff, ordinaryHypergeometricCoefficient]

/-- Every specialized hypergeometric coefficient is strictly positive. -/
lemma coeff_pos (n : ℕ) : 0 < coeff n := by
  unfold coeff ordinaryHypergeometricCoefficient
  exact mul_pos (mul_pos (mul_pos (inv_pos.mpr (by positivity))
    (ascPochhammer_pos _ _ (by norm_num))) (ascPochhammer_pos _ _ (by norm_num)))
    (inv_pos.mpr (ascPochhammer_pos _ _ (by norm_num)))

/-- The coefficient recurrence multiplies `coeff n` by `(n+1/2)^2 / ((n+5/2)*(n+1))`. -/
lemma coeff_succ (n : ℕ) : coeff (n+1) = coeff n *
    (((n : ℝ)+1/2)^2 / (((n : ℝ)+5/2)*((n : ℝ)+1))) := by
  unfold coeff ordinaryHypergeometricCoefficient
  rw [Nat.factorial_succ]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, ascPochhammer_succ_eval]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The specialized hypergeometric coefficients are nonincreasing. -/
lemma coeff_le_prev (n : ℕ) : coeff (n+1) ≤ coeff n := by
  rw [coeff_succ]
  apply mul_le_of_le_one_right (coeff_pos n).le
  apply (div_le_one (by positivity : 0 < ((n:ℝ)+5/2)*((n:ℝ)+1))).2
  nlinarith [show (0:ℝ) ≤ n by positivity]

/-- Every specialized hypergeometric coefficient of positive degree is at most 1/10. -/
lemma coeff_le_tenth (n : ℕ) : coeff (n+1) ≤ 1/10 := by
  induction n with
  | zero => simpa using coeff_one.le
  | succ n ih => exact (coeff_le_prev (n+1)).trans ih

/-- The coefficient `coeff n` is at most `1/(n+1)^2`. -/
lemma coeff_le_square (n : ℕ) : coeff n ≤ 1 / ((n : ℝ)+1)^2 := by
  induction n with
  | zero => norm_num [coeff_zero]
  | succ n ih =>
    rw [coeff_succ]
    have hn : (0 : ℝ) ≤ n := by positivity
    have hr : 0 ≤ ((n : ℝ)+1/2)^2 / (((n : ℝ)+5/2)*((n : ℝ)+1)) := by positivity
    calc
      _ ≤ (1 / ((n : ℝ)+1)^2) *
          (((n : ℝ)+1/2)^2 / (((n : ℝ)+5/2)*((n : ℝ)+1))) := mul_le_mul_of_nonneg_right ih hr
      _ ≤ 1 / (((n+1 : ℕ) : ℝ)+1)^2 := by
        push_cast
        rw [show 1 / ((n:ℝ)+1)^2 * (((n:ℝ)+1/2)^2 / (((n:ℝ)+5/2)*((n:ℝ)+1))) =
          ((n:ℝ)+1/2)^2 / (((n:ℝ)+1)^2 * (((n:ℝ)+5/2)*((n:ℝ)+1))) by
            simp only [div_eq_mul_inv, mul_inv_rev]; ring]
        apply (div_le_div_iff₀ (by positivity : 0 < ((n:ℝ)+1)^2 * (((n:ℝ)+5/2)*((n:ℝ)+1))) (by positivity : 0 < ((n:ℝ)+1+1)^2)).2
        nlinarith [pow_nonneg hn 3]

/-- For `z ∈ [0, 1]`, the series with terms `coeff n * z^n` is summable. -/
lemma series_summable {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    Summable (fun n : ℕ => coeff n * z^n) := by
  have hp : Summable (fun n : ℕ => 1 / ((n:ℝ)+1)^2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2:ℕ)))
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (coeff_pos n).le (pow_nonneg hz0 n))
      (fun n => ?_) hp
  exact (mul_le_of_le_one_right (coeff_pos n).le (pow_le_one₀ hz0 hz1)).trans (coeff_le_square n)

/-- For `z ∈ [0, 1]`, the hypergeometric value is at least `1 + z/10`. -/
lemma hyper_lower {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    1+z/10 ≤ ₂F₁ (1/2 : ℝ) (1/2) (5/2) z := by
  rw [true_series]
  have h := (series_summable hz0 hz1).sum_le_tsum (Finset.range 2)
    (fun n _ => mul_nonneg (coeff_pos n).le (pow_nonneg hz0 n))
  simpa [Finset.sum_range_succ, coeff_zero, coeff_one, div_eq_mul_inv, mul_comm] using h

/-- For `z ∈ [0, 1/9]`, the hypergeometric value is at most `1 + z/(10*(1-z))`. -/
lemma hyper_upper {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1/9) :
    ₂F₁ (1/2 : ℝ) (1/2) (5/2) z ≤ 1+z/(10*(1-z)) := by
  have hzlt : z < 1 := by linarith
  have hzle : z ≤ 1 := hzlt.le
  rw [true_series, (series_summable hz0 hzle).tsum_eq_zero_add]
  simp only [coeff_zero, pow_zero, mul_one]
  have hge : Summable (fun n : ℕ => (1/10:ℝ)*z^(n+1)) := by
    convert! (hasSum_geometric_of_lt_one hz0 hzlt).summable.mul_left (z/10) using 1
    ext n
    ring
  have hle : (∑' n : ℕ, coeff (n+1)*z^(n+1)) ≤ ∑' n : ℕ, (1/10:ℝ)*z^(n+1) := Summable.tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_right (coeff_le_tenth n) (pow_nonneg hz0 (n+1)))
    ((summable_nat_add_iff (f := fun n : ℕ => coeff n*z^n) 1).2 (series_summable hz0 hzle)) hge
  have heq : (∑' n : ℕ, (1/10:ℝ)*z^(n+1)) = z/(10*(1-z)) := by
    calc
      _ = ∑' n : ℕ, (z/10)*z^n := tsum_congr (fun n => by ring)
      _ = (z/10)*(1-z)⁻¹ := ((hasSum_geometric_of_lt_one hz0 hzlt).mul_left (z/10)).tsum_eq
      _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
  simpa only [add_comm] using add_le_add_left (hle.trans_eq heq) 1

/-- For `z ∈ [0, 1/9]`, the hypergeometric value is at most 81/80. -/
lemma hyper_upper_81_80 {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1/9) :
    ₂F₁ (1/2 : ℝ) (1/2) (5/2) z ≤ 81/80 := by
  apply (hyper_upper hz0 hz1).trans
  have hd : 0 < 10*(1-z) := by linarith
  have hf : z/(10*(1-z)) ≤ 1/80 := (div_le_iff₀ hd).2 (by linarith)
  linarith

/-- For `t ∈ [-1, 0]`, the signed factor `t * ₂F₁(1/2, 1/2; 5/2; t^2)` is at most
`t*(1+t^2/10)`. -/
lemma fhat_negative {t : ℝ} (htlo : -1 ≤ t) (ht0 : t ≤ 0) :
    t * ₂F₁ (1/2 : ℝ) (1/2) (5/2) (t^2) ≤ t*(1+t^2/10) := by
  exact mul_le_mul_of_nonpos_left (hyper_lower (sq_nonneg t) (by nlinarith)) ht0

/-- For `t ∈ [0, 1/3]`, the signed factor `t * ₂F₁(1/2, 1/2; 5/2; t^2)` is at most `(81/80)*t`. -/
lemma fhat_positive {t : ℝ} (ht0 : 0 ≤ t) (hthi : t ≤ 1/3) :
    t * ₂F₁ (1/2 : ℝ) (1/2) (5/2) (t^2) ≤ (81/80)*t := by
  have h := mul_le_mul_of_nonneg_left (hyper_upper_81_80 (sq_nonneg t) (by nlinarith)) ht0
  simpa only [mul_comm] using h

/-- The rank-three normalization constant `8/(3*π)` lies between 28/33 and 400/471. -/
lemma rounding_constant_bounds :
    (28/33:ℝ) ≤ 8/(3*Real.pi) ∧ 8/(3*Real.pi) ≤ 400/471 := by
  constructor
  · apply (le_div_iff₀ (by positivity : 0 < 3*Real.pi)).2
    nlinarith [Real.pi_lt_d4]
  · apply (div_le_iff₀ (by positivity : 0 < 3*Real.pi)).2
    nlinarith [Real.pi_gt_d2]
end Qatlib.Papers.RydbergMaxCut26.RatioBounds.Hypergeom
