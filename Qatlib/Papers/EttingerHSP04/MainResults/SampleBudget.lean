/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Qatlib.Papers.EttingerHSP04.MainResults.SubgroupCounting

@[expose] public section

/-!
# Ceiling-logarithm sample budget in exact subgroup testing

Section 2.2 chooses the ceiling of twice the logarithm of four times
the cube of the subgroup count. Section 3 uses one amplification
round for the decision version. The subgroup count bound controls
the sample length that appears before circuit-level accounting.
-/

set_option autoImplicit false

open Qatlib.Papers.EttingerHSP04.MainResults

namespace Qatlib.Papers.EttingerHSP04.MainResults

/-- The sample count with the ceiling used in Section 2.2 is bounded
by a fixed quadratic polynomial in the integer logarithm of group order. -/
theorem exact_decision_sample_count_le {G : Type*} [Group G] [Fintype G] :
    ⌈2 * Real.logb 2 (4 * (Fintype.card (Subgroup G) : ℝ) ^ 3)⌉₊ ≤
      16 * ((Fintype.card G).log2 + 1) ^ 2 := by
  let m := (Fintype.card G).log2
  let r := Fintype.card (Subgroup G)
  let B := (m + 1) * (m + 2)
  have hr : r ≤ 2 ^ B := card_subgroups_le_two_pow
  have hrpos : 0 < r := Fintype.card_pos
  have hx : 4 * r ^ 3 ≤ 2 ^ (3 * B + 2) := calc
    _ ≤ 4 * (2 ^ B) ^ 3 := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hr 3)
    _ = _ := by
      rw [← pow_mul, show 3 * B + 2 = 2 + B * 3 by omega, pow_add]
      norm_num
  have hxR : (4 : ℝ) * (r : ℝ) ^ 3 ≤ (2 : ℝ) ^ (3 * B + 2) := by exact_mod_cast hx
  have hxpos : 0 < (4 : ℝ) * (r : ℝ) ^ 3 := by positivity
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hxpos hxR
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hlog
  have hceil : ⌈2 * Real.logb 2 (4 * (r : ℝ) ^ 3)⌉₊ ≤ 2 * (3 * B + 2) := by
    apply Nat.ceil_le.mpr
    push_cast at hlog ⊢
    linarith
  have hB : B ≤ 2 * (m + 1) ^ 2 := by
    dsimp [B]
    nlinarith
  have hm : 1 ≤ (m + 1) ^ 2 := one_le_pow₀ (by omega : 1 ≤ m + 1)
  exact hceil.trans (by nlinarith)

end Qatlib.Papers.EttingerHSP04.MainResults
