/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp

@[expose] public section


/-! # Conditional quadratic error bound

The recurrence is an explicit hypothesis. This does not identify the sequence
with a QSP Newton run or provide floating-point convergence in all regimes.
-/

set_option autoImplicit false

namespace Qatlib.Papers.IterativeQSP23.MainResults.NewtonBounds

/-- A nonnegative sequence with a quadratic recurrence satisfies the corresponding power bound. -/
theorem quadratic_bound (C e0 : ℝ) (e : ℕ → ℝ)
    (hC : 0 < C) (hnonneg : ∀ k, 0 ≤ e k) (h0 : e 0 = e0)
    (hrec : ∀ k, e (k + 1) ≤ C * (e k) ^ 2) :
    ∀ k, e k ≤ (C * e0) ^ (2 ^ k) / C := by
  intro k
  induction k with
  | zero =>
      rw [h0]
      simp only [pow_zero, pow_one]
      rw [mul_div_cancel_left₀ e0 (ne_of_gt hC)]
  | succ k ih =>
      calc e (k + 1) ≤ C * (e k) ^ 2 := hrec k
        _ ≤ C * ((C * e0) ^ (2 ^ k) / C) ^ 2 := by
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (hnonneg k) ih 2) (le_of_lt hC)
        _ = (C * e0) ^ (2 ^ (k + 1)) / C := by
            rw [pow_succ (2 : ℕ) k, pow_mul]
            field_simp [ne_of_gt hC]

end Qatlib.Papers.IterativeQSP23.MainResults.NewtonBounds
