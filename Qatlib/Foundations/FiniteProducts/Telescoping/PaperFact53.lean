/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

set_option autoImplicit false

namespace Qatlib.Foundations.FiniteProducts.Telescoping

open scoped BigOperators

/-- Expresses the difference of the two shifted finite products by the stated telescoping
product identity. -/
theorem fact53_product_telescoping (k : ℕ) (a b : ℝ) :
    ((k : ℝ) + 1) * (a + b + (k : ℝ) + 1) *
      (∏ j ∈ Finset.range k, (a + (j : ℝ) + 1) * (b + (j : ℝ) + 1)) =
    (∏ j ∈ Finset.range (k + 1), (a + (j : ℝ) + 1) * (b + (j : ℝ) + 1)) -
    (∏ j ∈ Finset.range (k + 1), (a + (j : ℝ)) * (b + (j : ℝ))) := by
  rw [Finset.prod_range_succ,
    Finset.prod_range_succ' (fun j => (a + (j : ℝ)) * (b + (j : ℝ)))]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
  simp only [← add_assoc]
  ring

end Qatlib.Foundations.FiniteProducts.Telescoping
