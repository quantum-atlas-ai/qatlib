/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace Qatlib.Papers.AdiabHypergph12.SymmetrySector

noncomputable section

open scoped BigOperators

def cutWeight (n n₁ : ℕ) : ℝ := (1 / 2 : ℝ)^n * (n.choose n₁ : ℝ)

theorem cutWeight_nonneg (n n₁ : ℕ) : 0 ≤ cutWeight n n₁ := by
  unfold cutWeight
  positivity

theorem sum_cutWeight (n : ℕ) :
    (∑ n₁ ∈ Finset.range (n + 1), cutWeight n n₁) = 1 := by
  unfold cutWeight
  rw [← Finset.mul_sum]
  have hchoose : (∑ n₁ ∈ Finset.range (n + 1), ((n.choose n₁ : ℕ) : ℝ)) =
      (2 : ℝ)^n := by
    rw [← Nat.cast_sum, Nat.sum_range_choose]
    norm_num
  rw [hchoose, ← mul_pow]
  norm_num

end

end Qatlib.Papers.AdiabHypergph12.SymmetrySector
