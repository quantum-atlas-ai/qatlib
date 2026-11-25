/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AdiabaticFail05.DriverBounds.StructuredDecoupled

@[expose] public section

/-!
# An explicit runtime for the independent-bit budget

The source uses a single-bit error bounded by a constant times the
inverse square runtime. At a runtime proportional to the square
root of the bit count, this bound is in the probability range and
the product success is at least one minus the requested tolerance.
-/

set_option autoImplicit false

open Qatlib.Papers.AdiabaticFail05.DriverBounds

namespace Qatlib.Papers.AdiabaticFail05.DriverBounds

/-- An explicit square-root runtime suffices for the scalar
independent-bit lower bound, with its failure bound in the unit interval. -/
theorem quadratic_gap_constant_success_bigO (n : ℕ) (hn : 1 ≤ n)
    (C c : ℝ) (hC : 0 < C) (hc : 0 < c) (hc1 : c ≤ 1) :
    ∃ T : ℝ, 0 < T ∧ T ≤ Real.sqrt (C / c) * Real.sqrt (n : ℝ) ∧
      C / T ^ 2 ≤ 1 ∧ 1 - c ≤ (1 - C / T ^ 2) ^ n := by
  let T := Real.sqrt ((n : ℝ) * C / c)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hT : 0 < T := Real.sqrt_pos.2 (by positivity)
  have hT2 : T ^ 2 = (n : ℝ) * C / c := Real.sq_sqrt (by positivity)
  have hratio : C / T ^ 2 = c / (n : ℝ) := by
    rw [hT2]
    field_simp [hC.ne', hc.ne', ne_of_gt (zero_lt_one.trans_le hnR)]
  have hvalid : C / T ^ 2 ≤ 1 := by
    rw [hratio]
    exact (div_le_one (zero_lt_one.trans_le hnR)).2 (hc1.trans hnR)
  refine ⟨T, hT, ?_, hvalid, quadratic_gap_constant_success n C c T hC hc hc1 hT hvalid le_rfl⟩
  dsimp [T]
  rw [mul_div_assoc, Real.sqrt_mul (Nat.cast_nonneg n), mul_comm]

end Qatlib.Papers.AdiabaticFail05.DriverBounds
