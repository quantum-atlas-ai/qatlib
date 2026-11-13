/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option backward.isDefEq.respectTransparency false

/-!
# Divided Product Telescoping Identity

This module proves the divided-form product telescoping identity used in the analysis
of inverse-free quantum state estimation: for every `k : ℕ` and real numbers `a, b`,
`(a + b + k + 1) ∏_{j=1}^k (a + j)(b + j)` equals `(1 / (k + 1))` times the difference
between `∏_{j=1}^{k+1} (a + j)(b + j)` and `∏_{j=1}^{k+1} (a - 1 + j)(b - 1 + j)`.

## Main statements

* `fact53_divided_product_telescoping`: divided-form finite product telescoping identity.

## References

* [Chen, 2025][Chen2025HeisenbergEst], Fact 5.3, p. 12.
-/

set_option autoImplicit false

namespace Qatlib.Papers.HeisenbergEst25.MainResults.Facts

open scoped BigOperators

/-- **Fact 5.3**: for every `k : ℕ` and `a, b : ℝ`,
`(a + b + k + 1) ∏_{j < k} (a + j + 1)(b + j + 1)` equals `(1 / (k + 1))` times the
difference `∏_{j < k + 1} (a + j + 1)(b + j + 1) - ∏_{j < k + 1} (a - 1 + j + 1)(b - 1 + j + 1)`. -/
theorem fact53_divided_product_telescoping (k : ℕ) (a b : ℝ) :
    (a + b + (k : ℝ) + 1) *
        (∏ j ∈ Finset.range k, (a + (j : ℝ) + 1) * (b + (j : ℝ) + 1)) =
      (1 / ((k : ℝ) + 1)) *
        ((∏ j ∈ Finset.range (k + 1), (a + (j : ℝ) + 1) * (b + (j : ℝ) + 1)) -
          (∏ j ∈ Finset.range (k + 1),
            (a - 1 + (j : ℝ) + 1) * (b - 1 + (j : ℝ) + 1))) := by
  have htop :
      (∏ j ∈ Finset.range (k + 1), (a + (j : ℝ) + 1) * (b + (j : ℝ) + 1)) =
        (∏ j ∈ Finset.range k, (a + (j : ℝ) + 1) * (b + (j : ℝ) + 1)) *
          ((a + (k : ℝ) + 1) * (b + (k : ℝ) + 1)) :=
    Finset.prod_range_succ (fun j => (a + (j : ℝ) + 1) * (b + (j : ℝ) + 1)) k
  have hbot :
      (∏ j ∈ Finset.range (k + 1),
          (a - 1 + (j : ℝ) + 1) * (b - 1 + (j : ℝ) + 1)) =
        (∏ j ∈ Finset.range k, (a + (j : ℝ) + 1) * (b + (j : ℝ) + 1)) *
          (a * b) := by
    rw [Finset.prod_range_succ']
    congr 1
    · apply Finset.prod_congr rfl
      intro j _
      push_cast
      ring
    · push_cast
      ring
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  rw [htop, hbot]
  field_simp [hk]
  ring

end Qatlib.Papers.HeisenbergEst25.MainResults.Facts
