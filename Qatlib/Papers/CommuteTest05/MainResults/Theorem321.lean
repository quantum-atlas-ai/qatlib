/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A scalar comparison for powered-update costs

This module verifies that multiplying the two-level cost scale by `u ^ (1 / 5) * v ^ (1 / 5)`
cannot decrease it when all size and batching parameters are at least one. This is the algebraic
comparison used in the charged cost model for Theorem 3.2.1 of [Itakura2005].

## Main statements

* `theorem321_powering_no_improvement`: Bounds the base power-law expression by its batch-factor
  multiple.

## References

* [Itakura, 2005][Itakura2005]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommuteTest05.MainResults.Theorem321

/-- For `k, n, u, v ≥ 1`, the expression `k ^ (4 / 5) * n ^ (9 / 5)` is at most its product with
`u ^ (1 / 5) * v ^ (1 / 5)`. This is the scalar cost comparison associated with [Itakura,
Theorem 3.2.1][Itakura2005]. -/
theorem theorem321_powering_no_improvement
    (k n u v : ℝ) (hk : 1 ≤ k) (hn : 1 ≤ n) (hu : 1 ≤ u) (hv : 1 ≤ v) :
    k ^ ((4 : ℝ) / 5) * n ^ ((9 : ℝ) / 5) ≤
      k ^ ((4 : ℝ) / 5) * n ^ ((9 : ℝ) / 5) *
        u ^ ((1 : ℝ) / 5) * v ^ ((1 : ℝ) / 5) := by
  have hk0 : (0 : ℝ) ≤ k := le_trans zero_le_one hk
  have hn0 : (0 : ℝ) ≤ n := le_trans zero_le_one hn
  have hu1 : (1 : ℝ) ≤ u ^ ((1 : ℝ) / 5) :=
    Real.one_le_rpow hu (by norm_num)
  have hv1 : (1 : ℝ) ≤ v ^ ((1 : ℝ) / 5) :=
    Real.one_le_rpow hv (by norm_num)
  have hu0 : (0 : ℝ) ≤ u ^ ((1 : ℝ) / 5) := le_trans zero_le_one hu1
  have hfac : (1 : ℝ) ≤ u ^ ((1 : ℝ) / 5) * v ^ ((1 : ℝ) / 5) := by
    have h := mul_le_mul hu1 hv1 (by norm_num : (0 : ℝ) ≤ 1) hu0
    simpa using h
  have hbase : (0 : ℝ) ≤ k ^ ((4 : ℝ) / 5) * n ^ ((9 : ℝ) / 5) :=
    mul_nonneg (Real.rpow_nonneg hk0 _) (Real.rpow_nonneg hn0 _)
  calc k ^ ((4 : ℝ) / 5) * n ^ ((9 : ℝ) / 5)
      = (k ^ ((4 : ℝ) / 5) * n ^ ((9 : ℝ) / 5)) * 1 := by ring
    _ ≤ (k ^ ((4 : ℝ) / 5) * n ^ ((9 : ℝ) / 5)) *
          (u ^ ((1 : ℝ) / 5) * v ^ ((1 : ℝ) / 5)) :=
        mul_le_mul_of_nonneg_left hfac hbase
    _ = k ^ ((4 : ℝ) / 5) * n ^ ((9 : ℝ) / 5) *
          u ^ ((1 : ℝ) / 5) * v ^ ((1 : ℝ) / 5) := by ring

end Qatlib.Papers.CommuteTest05.MainResults.Theorem321
