/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AdiabClass08.MainResults.Eq11BitPrecision
public import Qatlib.Papers.AdiabClass08.MainResults.RegionCountBound

@[expose] public section

/-!
# The direction of the region-count precision bound

The binomial sum is bounded above by the exponential estimate.
Covering the sum gives a logarithmic bound in terms of that sum.
The larger exponential estimate may instead be used to choose
a sufficient capacity for the counting inequality.
-/

set_option autoImplicit false

open scoped BigOperators
open Qatlib.Papers.AdiabClass08.MainResults

namespace Qatlib.Papers.AdiabClass08.MainResults

/-- Taking logarithms of the exact binomial region-count comparison
gives its exact condition on the bit parameter. -/
theorem region_count_capacity_iff {S N : ℕ} (hN : 0 < N) (bits : ℝ) :
    (∑ k ∈ Finset.range (N + 1), (S.choose k : ℝ)) ≤
        (2 : ℝ) ^ ((bits + 1) * (N : ℝ)) ↔
      Real.logb 2 (∑ k ∈ Finset.range (N + 1), (S.choose k : ℝ)) /
            (N : ℝ) - 1 ≤ bits := by
  let regions : ℝ := ∑ k ∈ Finset.range (N + 1), (S.choose k : ℝ)
  change regions ≤ _ ↔ Real.logb 2 regions / (N : ℝ) - 1 ≤ bits
  have hregions : 0 < regions := by
    have h := Finset.single_le_sum (f := fun k => (S.choose k : ℝ))
      (fun k _ => Nat.cast_nonneg (S.choose k)) (Finset.mem_range.2 (Nat.succ_pos N) : 0 ∈ _)
    simp only [Nat.choose_zero_right, Nat.cast_one] at h
    exact zero_lt_one.trans_le h
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hregions,
    sub_le_iff_le_add, div_le_iff₀ hNreal]

/-- The exponential replacement used in the source gives sufficient
capacity in the counting model when its logarithmic threshold is met. -/
theorem eq11_suffices_for_count {S N : ℕ} (hN : 1 ≤ N) (hSN : N ≤ S) {bits : ℝ}
    (hbits : Real.logb 2 ((S : ℝ) / (N : ℝ)) + Real.logb 2 (Real.exp 1) - 1 ≤ bits) :
    (∑ k ∈ Finset.range (N + 1), (S.choose k : ℝ)) ≤
      (2 : ℝ) ^ ((bits + 1) * (N : ℝ)) := by
  have hNp : 0 < N := by omega
  have hSp : 0 < S := hNp.trans_le hSN
  rw [eq11_log_form hSp hNp, sub_le_iff_le_add] at hbits
  have hX : 0 < Real.exp 1 * ((S : ℝ) / (N : ℝ)) := by positivity
  have hpow := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hX).1 hbits
  calc
    _ ≤ (Real.exp 1 * (S : ℝ) / (N : ℝ)) ^ N := region_sum_le_exp hN hSN
    _ = (Real.exp 1 * ((S : ℝ) / (N : ℝ))) ^ N := by rw [mul_div_assoc]
    _ ≤ ((2 : ℝ) ^ (bits + 1)) ^ N := pow_le_pow_left₀ hX.le hpow N
    _ = _ := by rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]

/-- For one variable and one sample the exact comparison holds at zero
bits, below the exponential replacement's logarithmic threshold. -/
theorem count_bound_counterexample :
    (∑ k ∈ Finset.range 2, ((1 : ℕ).choose k : ℝ)) ≤
      (2 : ℝ) ^ ((0 + 1 : ℝ) * (1 : ℝ)) ∧
      0 < Real.logb 2 ((1 : ℝ) / 1) + Real.logb 2 (Real.exp 1) - 1 := by
  constructor
  · norm_num [Finset.sum_range_succ]
  · have he : (2 : ℝ) < Real.exp 1 := by
      have h := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
      linarith
    have hlog : (1 : ℝ) < Real.logb 2 (Real.exp 1) := by
      calc
        _ = Real.logb 2 2 := (Real.logb_self_eq_one (by norm_num)).symm
        _ < _ := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
          (by norm_num : (0 : ℝ) < 2) he
    simp
    linarith

end Qatlib.Papers.AdiabClass08.MainResults
