/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ManifoldInv07.MainResults.SixJCompile

@[expose] public section

/-!
# The budget of a duality transformation

Section 3.2 decomposes the transformation into `2n - 3` elementary
transformations. A common block budget bounds the finite sum.
-/

set_option autoImplicit false

namespace Qatlib.Papers.ManifoldInv07.MainResults

open scoped BigOperators

/-- A sequence with the source block count and per-block budget `B` costs at most
`(2 * n - 3) * B`. -/
theorem duality_cost {Word : Type*} (cost : Word → ℕ) (n B : ℕ)
    (block : Fin (2 * n - 3) → Word) (hblock : ∀ i, cost (block i) ≤ B) :
    (∑ i, cost (block i)) ≤ (2 * n - 3) * B := by
  calc
    (∑ i, cost (block i)) ≤ ∑ _i : Fin (2 * n - 3), B :=
      Finset.sum_le_sum fun i _ => hblock i
    _ = (2 * n - 3) * B := by simp

end Qatlib.Papers.ManifoldInv07.MainResults
