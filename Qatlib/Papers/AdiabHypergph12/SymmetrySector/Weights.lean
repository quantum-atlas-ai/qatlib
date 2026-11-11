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

/-!
# Binomial weights of symmetry cuts

Defines `cutWeight n n₁` as the binomial weight `2⁻ⁿ * n.choose n₁`. These weights are
nonnegative and sum to one over the possible cut sizes. See [FarhiEtAl2012].

## Main statements

* `cutWeight_nonneg`: Every cut weight is nonnegative.
* `sum_cutWeight`: The cut weights over sizes zero through `n` sum to one.

## References

* [Farhi et al., 2012][FarhiEtAl2012]
-/

set_option autoImplicit false

namespace Qatlib.Papers.AdiabHypergph12.SymmetrySector

noncomputable section

open scoped BigOperators

/-- The binomial weight `(1 / 2) ^ n * n.choose n₁` of cut size `n₁`. -/
def cutWeight (n n₁ : ℕ) : ℝ := (1 / 2 : ℝ)^n * (n.choose n₁ : ℝ)

/-- Every binomial cut weight is nonnegative [FarhiEtAl2012]. -/
theorem cutWeight_nonneg (n n₁ : ℕ) : 0 ≤ cutWeight n n₁ := by
  unfold cutWeight
  positivity

/-- The binomial cut weights summed over sizes zero through `n` equal one [FarhiEtAl2012]. -/
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
