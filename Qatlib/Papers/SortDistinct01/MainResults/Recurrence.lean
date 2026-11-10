/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Semiring

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SortDistinct01.MainResults.Recurrence

def nextSize (N : ℕ) : ℕ :=
  Nat.floor ((N : ℝ) / 3 + Real.logb 2 (N : ℝ) + 1)

theorem nextSize_pos (N : ℕ) (hN : 1 ≤ N) : 0 < nextSize N := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog : 0 ≤ Real.logb 2 (N : ℝ) :=
    Real.logb_nonneg (by norm_num) hN1
  have hnonneg : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have h1 : (1 : ℝ) ≤ (N : ℝ) / 3 + Real.logb 2 (N : ℝ) + 1 := by
    nlinarith [hlog, hnonneg]
  rw [nextSize, Nat.floor_pos]
  exact h1

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
