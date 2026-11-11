/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Exponential bound for region counts

This module bounds a partial binomial sum by `(exp(1) * S / N) ^ N` when `1 ≤ N ≤ S`. The
weighted binomial estimate and the exponential bound in `one_add_div_pow_le_exp` provide the
region-count estimate used in [NevenEtAl2008].

## Main statements

* `sum_choose_mul_pow_le`: a nonnegative weighted partial binomial sum is bounded by the full
  expansion.
* `one_add_div_pow_le_exp`: the estimate `(1 + N/S) ^ S ≤ exp(N)`.
* `region_sum_le_exp`: the resulting upper bound on the unweighted partial sum.

## References

* [Neven et al., 2008][NevenEtAl2008]
-/

set_option autoImplicit false
noncomputable section

open Finset

namespace Qatlib.Papers.AdiabClass08.MainResults

/-- For `N ≤ S` and nonnegative `x`, the sum of `choose S k * x ^ k` over `k ≤ N` is at most `(1
+ x) ^ S`. See [NevenEtAl2008]. -/
theorem sum_choose_mul_pow_le {S N : ℕ} (hSN : N ≤ S) {x : ℝ} (hx : 0 ≤ x) :
    (∑ k ∈ Finset.range (N + 1), (S.choose k : ℝ) * x ^ k) ≤ (1 + x) ^ S := by
  have hfull : (1 + x) ^ S = ∑ k ∈ Finset.range (S + 1), (S.choose k : ℝ) * x ^ k := by
    rw [show (1 + x : ℝ) = x + 1 by ring, add_pow x 1 S]
    apply Finset.sum_congr rfl
    intro k _hk
    rw [one_pow, mul_one, mul_comm]
  rw [hfull]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ hSN)) ?_
  intro k _hkS _hkN
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx k)

/-- If `0 < N ≤ S`, then `(1 + N/S) ^ S ≤ exp(N)`. See [NevenEtAl2008]. -/
theorem one_add_div_pow_le_exp {S N : ℕ} (hN : 0 < N) (hSN : N ≤ S) :
    (1 + (N : ℝ) / (S : ℝ)) ^ S ≤ Real.exp (N : ℝ) := by
  have hSpos : (0 : ℝ) < (S : ℝ) := by
    have : 0 < S := lt_of_lt_of_le hN hSN
    exact_mod_cast this
  have hu : (0 : ℝ) < 1 + (N : ℝ) / (S : ℝ) := by
    have hq : (0 : ℝ) ≤ (N : ℝ) / (S : ℝ) := div_nonneg (by positivity) hSpos.le
    linarith
  apply (Real.log_le_log_iff (pow_pos hu S) (Real.exp_pos (N : ℝ))).mp
  rw [Real.log_pow, Real.log_exp]
  have hlog : Real.log (1 + (N : ℝ) / (S : ℝ)) ≤ (N : ℝ) / (S : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hu
    linarith
  calc (S : ℝ) * Real.log (1 + (N : ℝ) / (S : ℝ))
        ≤ (S : ℝ) * ((N : ℝ) / (S : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hlog hSpos.le
    _ = (N : ℝ) := mul_div_cancel₀ (N : ℝ) hSpos.ne'

/-- If `1 ≤ N ≤ S`, the sum of `choose S k` over `k ≤ N` is at most `(exp(1) * S/N) ^ N`. See
[NevenEtAl2008]. -/
theorem region_sum_le_exp {S N : ℕ} (hN : 1 ≤ N) (hSN : N ≤ S) :
    (∑ k ∈ Finset.range (N + 1), (S.choose k : ℝ))
      ≤ (Real.exp 1 * (S : ℝ) / (N : ℝ)) ^ N := by
  have hNpos_nat : 0 < N := hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos_nat
  have hSpos : (0 : ℝ) < (S : ℝ) := by
    have : 0 < S := lt_of_lt_of_le hNpos_nat hSN
    exact_mod_cast this

  set x : ℝ := (N : ℝ) / (S : ℝ) with hxdef
  have hxpos : 0 < x := by rw [hxdef]; exact div_pos hNpos hSpos
  have hx0 : 0 ≤ x := hxpos.le
  have hx1 : x ≤ 1 := by
    rw [hxdef, div_le_one hSpos]
    exact_mod_cast hSN

  have hxA : x ^ N * (∑ k ∈ Finset.range (N + 1), (S.choose k : ℝ))
      ≤ (∑ k ∈ Finset.range (N + 1), (S.choose k : ℝ) * x ^ k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun k hk => ?_)
    have hk_le : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hC : (0 : ℝ) ≤ (S.choose k : ℝ) := Nat.cast_nonneg _
    have hxpow : x ^ N ≤ x ^ k := by
      have hsplit : x ^ N = x ^ k * x ^ (N - k) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hsplit]
      have hxNk : x ^ (N - k) ≤ 1 := pow_le_one₀ hx0 hx1
      exact mul_le_of_le_one_right (pow_nonneg hx0 k) hxNk
    calc x ^ N * (S.choose k : ℝ) ≤ x ^ k * (S.choose k : ℝ) :=
          mul_le_mul_of_nonneg_right hxpow hC
      _ = (S.choose k : ℝ) * x ^ k := by ring

  have hT : (∑ k ∈ Finset.range (N + 1), (S.choose k : ℝ) * x ^ k) ≤ (1 + x) ^ S :=
    sum_choose_mul_pow_le hSN hx0

  have hexp : (1 + x) ^ S ≤ Real.exp (N : ℝ) := by
    rw [hxdef]
    exact one_add_div_pow_le_exp hNpos_nat hSN

  have hcomb : x ^ N * (∑ k ∈ Finset.range (N + 1), (S.choose k : ℝ)) ≤ (Real.exp 1) ^ N := by
    refine le_trans (le_trans hxA (le_trans hT hexp)) ?_
    rw [← Real.exp_nat_mul]
    simp
  have hxNpos : (0 : ℝ) < x ^ N := pow_pos hxpos N

  have hfinal : (∑ k ∈ Finset.range (N + 1), (S.choose k : ℝ))
      ≤ (Real.exp 1) ^ N / x ^ N := by
    rw [le_div_iff₀ hxNpos, mul_comm]
    exact hcomb
  refine le_trans hfinal ?_
  rw [← div_pow]
  have hbase : Real.exp 1 / x = Real.exp 1 * (S : ℝ) / (N : ℝ) := by
    rw [hxdef, div_div_eq_mul_div]
  rw [hbase]

end Qatlib.Papers.AdiabClass08.MainResults
