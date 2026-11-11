/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# The ordered-search recurrence size

This module defines `nextSize`, the integer reduction size in the ordered-search recurrence of
Lemma 12 in [HoyerNeerbekShi2001]. It proves positivity for positive inputs and a lower bound by
natural-number division by three.

## Main statements

* `nextSize_pos`: The next recurrence size is positive whenever `N ≥ 1`.
* `nextSize_ge`: For `N ≥ 1`, the next recurrence size is at least the natural-number quotient
  `N / 3`.

## References

* [Hoyer et al., 2001][HoyerNeerbekShi2001]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SortDistinct01.MainResults.Recurrence

/-- The natural-number floor of `N / 3 + log₂ N + 1`, used as the next size in the
ordered-search recurrence. -/
def nextSize (N : ℕ) : ℕ :=
  Nat.floor ((N : ℝ) / 3 + Real.logb 2 (N : ℝ) + 1)

/-- The next recurrence size is positive whenever `N ≥ 1`. See [HoyerNeerbekShi2001]. -/
theorem nextSize_pos (N : ℕ) (hN : 1 ≤ N) : 0 < nextSize N := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog : 0 ≤ Real.logb 2 (N : ℝ) :=
    Real.logb_nonneg (by norm_num) hN1
  have hnonneg : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have h1 : (1 : ℝ) ≤ (N : ℝ) / 3 + Real.logb 2 (N : ℝ) + 1 := by
    nlinarith [hlog, hnonneg]
  rw [nextSize, Nat.floor_pos]
  exact h1

/-- For `N ≥ 1`, the next recurrence size is at least the natural-number quotient `N / 3`. See
[HoyerNeerbekShi2001]. -/
theorem nextSize_ge (N : ℕ) (hN : 1 ≤ N) : N / 3 ≤ nextSize N := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog : 0 ≤ Real.logb 2 (N : ℝ) :=
    Real.logb_nonneg (by norm_num) hN1
  have hx : ((N / 3 : ℕ) : ℝ) ≤ (N : ℝ) / 3 + Real.logb 2 (N : ℝ) + 1 := by
    have : ((N / 3 : ℕ) : ℝ) ≤ (N : ℝ) / 3 := by
      have := Nat.div_mul_le_self N 3
      have h3 : (0:ℝ) < 3 := by norm_num
      have : ((N / 3 : ℕ) : ℝ) * 3 ≤ (N : ℝ) := by
        exact_mod_cast Nat.div_mul_le_self N 3
      nlinarith
    nlinarith [hlog]
  exact Nat.le_floor hx

end Qatlib.Papers.SortDistinct01.MainResults.Recurrence
