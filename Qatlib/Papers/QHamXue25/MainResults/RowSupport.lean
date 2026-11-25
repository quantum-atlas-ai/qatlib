/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

/-!
# Row support in the finite homotopy lift

The number of generated positions is a sum of triangular numbers. Each
order individually is bounded by the total order in the row, so the sum is
bounded by the triangular number of the total.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.QHamXue25.MainResults

/-- The generated-support count of a row is controlled by its order slack. -/
theorem row_support_le (m i : ℕ) (a : Fin (i + 1) → ℕ)
    (ha : (∑ k, a k) ≤ m - i) :
    (∑ k, a k * (a k + 1) / 2) ≤ (m - i) * (m - i + 1) / 2 := by
  let S := ∑ k, a k
  have hsum : (∑ k, a k * (a k + 1)) ≤ S * (S + 1) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro k _
    have hk : a k ≤ S := Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ k)
    exact Nat.mul_le_mul_left _ (Nat.add_le_add_right hk 1)
  apply (Nat.le_div_iff_mul_le (by decide)).2
  calc
    _ = ∑ k, a k * (a k + 1) / 2 * 2 := Finset.sum_mul _ _ _
    _ ≤ ∑ k, a k * (a k + 1) :=
      Finset.sum_le_sum (fun k _ => Nat.div_mul_le_self _ _)
    _ ≤ S * (S + 1) := hsum
    _ ≤ _ := Nat.mul_le_mul ha (Nat.add_le_add_right ha 1)

/-- Expanding each generated position by at most `s` entries yields the
numerical sparsity budget of Eq. (53). -/
theorem row_sparse_entries_le (m i s : ℕ) (a : Fin (i + 1) → ℕ)
    (ha : (∑ k, a k) ≤ m - i) :
    s * (∑ k, a k * (a k + 1) / 2) ≤ s * m * (m + 1) / 2 := by
  have h₁ := row_support_le m i a ha
  have h₂ : (∑ k, a k * (a k + 1) / 2) * 2 ≤ m * (m + 1) :=
    ((Nat.le_div_iff_mul_le (by decide)).1 h₁).trans
      (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.add_le_add_right (Nat.sub_le _ _) 1))
  apply (Nat.le_div_iff_mul_le (by decide)).2
  simpa only [mul_assoc] using Nat.mul_le_mul_left s h₂

end Qatlib.Papers.QHamXue25.MainResults
