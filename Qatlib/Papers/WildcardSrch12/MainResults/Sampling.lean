/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.WildcardSrch12.MainResults.Model.GramOverlap

@[expose] public section


/-! Preserved closed mathematical components; no credit for deferred source algorithms. -/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators


namespace Qatlib.Papers.WildcardSrch12.MainResults.GroupTesting

open Qatlib.Papers.WildcardSrch12.MainResults

/-- The paper's sampling estimate (§4, p. 9): if each of the other `k − 1` marked
indices is included in the sampled set `S` independently with probability `1/k`, the
probability that `S` contains exactly one marked index is at least
`(1 − 1/k)^{k−1} ≥ 1/e`.  This file proves the second inequality. -/
theorem one_sub_inv_pow_ge_exp_neg_one {k : ℕ} (hk : 2 ≤ k) :
    Real.exp (-1) ≤ (1 - (k : ℝ)⁻¹) ^ (k - 1) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hk1 : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 1 < k)
  have hkm1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hbase : 0 < 1 - (k : ℝ)⁻¹ := by
    have hinv : (k : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hk1
    linarith
  -- `log (1 - 1/k) = -log (k/(k-1))`
  have hsub : (1 : ℝ) - (k : ℝ)⁻¹ = ((k : ℝ) - 1) / (k : ℝ) := by
    field_simp
  have hlog_eq : Real.log (1 - (k : ℝ)⁻¹)
      = -Real.log ((k : ℝ) / ((k : ℝ) - 1)) := by
    rw [hsub, Real.log_div (by linarith : ((k : ℝ) - 1) ≠ 0) (ne_of_gt hkR),
      Real.log_div (ne_of_gt hkR) (ne_of_gt hkm1)]
    ring
  -- `log (k/(k-1)) ≤ k/(k-1) - 1 = 1/(k-1)`
  have hlog_ub : Real.log ((k : ℝ) / ((k : ℝ) - 1)) ≤ ((k : ℝ) - 1)⁻¹ := by
    have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (k : ℝ) / ((k : ℝ) - 1))
    have hsimp : (k : ℝ) / ((k : ℝ) - 1) - 1 = ((k : ℝ) - 1)⁻¹ := by
      field_simp
      ring
    linarith
  have hlog_lb : -((k : ℝ) - 1)⁻¹ ≤ Real.log (1 - (k : ℝ)⁻¹) := by
    rw [hlog_eq]
    linarith
  have hprod : (-1 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) * Real.log (1 - (k : ℝ)⁻¹) := by
    have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k)]
      norm_num
    have hmul := mul_le_mul_of_nonneg_left hlog_lb (le_of_lt hkm1)
    rw [hcast]
    have : ((k : ℝ) - 1) * -((k : ℝ) - 1)⁻¹ = -1 := by
      field_simp
    linarith
  calc Real.exp (-1) ≤ Real.exp (((k - 1 : ℕ) : ℝ) * Real.log (1 - (k : ℝ)⁻¹)) :=
        Real.exp_le_exp.mpr hprod
    _ = (Real.exp (Real.log (1 - (k : ℝ)⁻¹))) ^ (k - 1) := Real.exp_nat_mul _ _
    _ = (1 - (k : ℝ)⁻¹) ^ (k - 1) := by rw [Real.exp_log hbase]


end Qatlib.Papers.WildcardSrch12.MainResults.GroupTesting
