/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.KernelWeights
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Exponential tails of integer sampling weights

Stirling bounds compare factorials with the products appearing in the integer regulator far from
the row poles. Outside `|x| ≥ 2m`, `integerWeight_norm_le_far` improves the Cauchy weight bound
by the factor `exp (-2m)`.

Summing this estimate gives an exponentially small discarded weight mass for cutoffs at least
`2am`. These estimates control finite-sampling errors in [WangEtAl2026].

## Main statements

* `integerWeight_norm_le_far`: gives exponential suppression of distant weights.
* `integerWeight_tail_tsum_le`: bounds the discarded lattice mass.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
namespace CBMD
open scoped BigOperators

/-- For `m ≥ 1`, the factorial is at most `exp 1 * sqrt m * (m / exp 1) ^ m`. -/
theorem factorial_stirling_upper (m : ℕ) (hm : 1 ≤ m) :
    (m.factorial : ℝ) ≤ Real.exp 1 * Real.sqrt m * ((m : ℝ) / Real.exp 1) ^ m := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hs : Stirling.stirlingSeq m ≤ Real.exp 1 / Real.sqrt 2 := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    simpa only [Function.comp_apply, Nat.succ_eq_add_one, Nat.zero_add,
      Stirling.stirlingSeq_one] using Stirling.stirlingSeq'_antitone (Nat.zero_le n)
  unfold Stirling.stirlingSeq at hs
  have hd : 0 < Real.sqrt (2 * (m : ℝ)) * ((m : ℝ) / Real.exp 1) ^ m := by positivity
  have hf := (div_le_iff₀ hd).mp hs
  convert! hf using 1
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp

/-- For `m ≥ 1`, the squared factorial is at most `exp 2 * m ^ (2 * m + 1) * exp (-2m)`. -/
theorem factorial_square_cutoff_bound (m : ℕ) (hm : 1 ≤ m) :
    (m.factorial : ℝ) ^ 2 ≤
      Real.exp 2 * (m : ℝ) ^ (2 * m + 1) * Real.exp (-2 * (m : ℝ)) := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hu := factorial_stirling_upper m hm
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ (m.factorial : ℝ)) hu 2
  calc
    (m.factorial : ℝ) ^ 2 ≤
        (Real.exp 1 * Real.sqrt m * ((m : ℝ) / Real.exp 1) ^ m) ^ 2 := hs
    _ = Real.exp 2 * (m : ℝ) ^ (2 * m + 1) * Real.exp (-2 * (m : ℝ)) := by
      simp only [mul_pow, Real.sq_sqrt hm0.le, ← pow_mul, div_pow,
        ← Real.exp_nat_mul, Nat.cast_ofNat, mul_one]
      rw [show -2 * (m : ℝ) = -(2 * (m : ℝ)) by ring, Real.exp_neg]
      rw [pow_succ, Nat.mul_comm m 2]
      ring

/-- If `|x| ≥ 2m`, the product of distances to the row poles is at least `m ^ (2 * m + 1)`. -/
theorem integer_regulator_product_lower_far (m : ℕ) (x : ℝ) (hx : 2 * m ≤ |x|) :
    (m : ℝ) ^ (2 * m + 1) ≤
      ∏ r ∈ Finset.Icc (-(m : ℤ)) m, ‖(x : ℂ) - (r : ℂ) - Complex.I‖ := by
  have hcard : (Finset.Icc (-(m : ℤ)) m).card = 2 * m + 1 := by
    rw [Int.card_Icc]
    omega
  calc
    (m : ℝ) ^ (2 * m + 1) = ∏ _r ∈ Finset.Icc (-(m : ℤ)) m, (m : ℝ) := by
      simp only [Finset.prod_const, hcard]
    _ ≤ _ := by
      apply Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
      intro r hr
      have hr' := Finset.mem_Icc.mp hr
      have hrabs : |(r : ℝ)| ≤ m := by
        apply abs_le.mpr
        constructor
        · exact_mod_cast hr'.1
        · exact_mod_cast hr'.2
      have htri := abs_sub_abs_le_abs_sub x (r : ℝ)
      have hnorm := Complex.abs_re_le_norm ((x : ℂ) - (r : ℂ) - Complex.I)
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.intCast_re, Complex.I_re,
        sub_zero] at hnorm
      linarith

/-- For `m ≥ 1`, positive spacing, and `|x| ≥ 2m`, the weight norm is at most
`integerWeightConstant * exp 2 * exp (-2m) / (a * (1 + x²))`. -/
theorem integerWeight_norm_le_far (m : ℕ) (hm : 1 ≤ m) {a : ℝ} (ha : 0 < a)
    (x : ℝ) (hx : 2 * m ≤ |x|) :
    ‖integerWeight m a x‖ ≤
      (integerWeightConstant * Real.exp 2 * Real.exp (-2 * (m : ℝ))) /
        (a * (1 + x ^ 2)) := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hC : 0 ≤ Real.sinh (Real.pi * 2) / (Real.pi * 2) := by
    have h := kernelNormalizedProduct_le (c := 2) (by norm_num) 0
    simp only [kernelNormalizedProduct, Finset.range_zero, Finset.prod_empty] at h
    exact (by norm_num : (0 : ℝ) ≤ 1).trans h
  have hA := finite_euler_product_upper m (c := 2) (by norm_num)
  norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num] at hA
  have hD := integer_regulator_product_lower_far m x hx
  have hDpos := (pow_pos hm0 (2 * m + 1)).trans_le hD
  have hR : (∏ j ∈ Finset.range m, (((j : ℝ) + 1) ^ 2 + 4)) /
      (∏ r ∈ Finset.Icc (-(m : ℤ)) m, ‖(x : ℂ) - (r : ℂ) - Complex.I‖) ≤
      (Real.sinh (Real.pi * 2) / (Real.pi * 2)) *
        Real.exp 2 * Real.exp (-2 * (m : ℝ)) := by
    apply (div_le_iff₀ hDpos).mpr
    calc
      _ ≤ (m.factorial : ℝ) ^ 2 * (Real.sinh (Real.pi * 2) / (Real.pi * 2)) := hA
      _ ≤ (Real.exp 2 * (m : ℝ) ^ (2 * m + 1) * Real.exp (-2 * (m : ℝ))) *
          (Real.sinh (Real.pi * 2) / (Real.pi * 2)) :=
        mul_le_mul_of_nonneg_right (factorial_square_cutoff_bound m hm) hC
      _ = ((Real.sinh (Real.pi * 2) / (Real.pi * 2)) *
          Real.exp 2 * Real.exp (-2 * (m : ℝ))) * (m : ℝ) ^ (2 * m + 1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hD (by positivity)
  rw [integerWeight_norm m ha x]
  have he1 : 1 - Real.exp (-2 * Real.pi * a) ≤ 1 := by
    linarith [Real.exp_pos (-2 * Real.pi * a)]
  have hR₀ : 0 ≤ (∏ j ∈ Finset.range m, (((j : ℝ) + 1) ^ 2 + 4)) /
      (∏ r ∈ Finset.Icc (-(m : ℤ)) m, ‖(x : ℂ) - (r : ℂ) - Complex.I‖) := by positivity
  have hnum := mul_le_mul
    (mul_le_mul_of_nonneg_right he1 (show 0 ≤ 3 / Real.pi by positivity)) hR hR₀
    (show 0 ≤ 1 * (3 / Real.pi) by positivity)
  simp only [one_mul] at hnum
  have hnum' : (1 - Real.exp (-2 * Real.pi * a)) * (3 / Real.pi) *
      ((∏ j ∈ Finset.range m, (((j : ℝ) + 1) ^ 2 + 4)) /
        (∏ r ∈ Finset.Icc (-(m : ℤ)) m, ‖(x : ℂ) - (r : ℂ) - Complex.I‖)) ≤
      integerWeightConstant * Real.exp 2 * Real.exp (-2 * (m : ℝ)) := by
    convert! hnum using 1
    unfold integerWeightConstant
    ring
  calc
    _ ≤ (integerWeightConstant * Real.exp 2 * Real.exp (-2 * (m : ℝ))) /
        (a * (‖(x : ℂ) + Complex.I‖ * ‖(x : ℂ) - 2 * Complex.I‖)) :=
      div_le_div_of_nonneg_right hnum' (by positivity)
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left
        (mul_nonneg (mul_nonneg integerWeightConstant_nonneg (Real.exp_pos _).le)
          (Real.exp_pos _).le) (by positivity)
      exact mul_le_mul_of_nonneg_left (integerWeight_outer_product_lower x) ha.le

/-- For `m ≥ 1`, `a ≥ 1`, and cutoff `K ≥ 2am`, the total weight norm beyond `K` is at most `5 *
integerWeightConstant * exp 2 * exp (-2m)`. -/
theorem integerWeight_tail_tsum_le (m : ℕ) (hm : 1 ≤ m) {a : ℝ} (ha : 1 ≤ a)
    (K : ℕ) (hK : 2 * a * m ≤ K) :
    (∑' k : {k : ℤ // (K : ℤ) < |k|},
      ‖integerWeight m a ((k.val : ℝ) / a)‖) ≤
        5 * integerWeightConstant * Real.exp 2 * Real.exp (-2 * (m : ℝ)) := by
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  let D : ℝ := integerWeightConstant * Real.exp 2 * Real.exp (-2 * (m : ℝ))
  have hD : 0 ≤ D := mul_nonneg
    (mul_nonneg integerWeightConstant_nonneg (Real.exp_pos _).le) (Real.exp_pos _).le
  have hb (k : {k : ℤ // (K : ℤ) < |k|}) :
      ‖integerWeight m a ((k.val : ℝ) / a)‖ ≤ D * latticeCauchy a k.val := by
    have hk : (K : ℝ) < |(k.val : ℝ)| := by exact_mod_cast k.property
    have hx : 2 * (m : ℝ) ≤ |(k.val : ℝ) / a| := by
      rw [abs_div, abs_of_pos ha0]
      apply (le_div_iff₀ ha0).mpr
      nlinarith
    calc
      _ ≤ D / (a * (1 + ((k.val : ℝ) / a) ^ 2)) := integerWeight_norm_le_far m hm ha0 _ hx
      _ = D * latticeCauchy a k.val := by
        rw [latticeCauchy_eq_scaled ha0]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
  have hs := (integerWeight_lattice_norm_summable m ha).subtype (fun k => (K : ℤ) < |k|)
  have hg := ((latticeCauchy_summable ha).mul_left D).subtype (fun k => (K : ℤ) < |k|)
  calc
    _ ≤ ∑' k : {k : ℤ // (K : ℤ) < |k|}, D * latticeCauchy a k.val :=
      Summable.tsum_le_tsum hb hs hg
    _ ≤ ∑' k : ℤ, D * latticeCauchy a k :=
      Summable.tsum_subtype_le _ _ (fun _ => mul_nonneg hD (by unfold latticeCauchy; positivity))
        ((latticeCauchy_summable ha).mul_left D)
    _ = D * (∑' k : ℤ, latticeCauchy a k) := tsum_mul_left
    _ ≤ D * 5 := mul_le_mul_of_nonneg_left (latticeCauchy_tsum_le_five ha) hD
    _ = _ := by dsimp [D]; ring

end CBMD

end Qatlib.Foundations.CbmdAnalysis.Core
