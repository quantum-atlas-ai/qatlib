/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommuteTest05.MatrixSubset

theorem choose_marked_mul (k r : ℕ) (hr2 : 2 ≤ r) :
    (Nat.choose k r : ℝ) * ((r : ℝ) * ((r : ℝ) - 1)) =
      ((k : ℝ) * ((k : ℝ) - 1)) * (Nat.choose (k - 2) (r - 2) : ℝ) := by
  have h := Nat.choose_mul (n := k) (k := r) (s := 2) hr2
  have hcast : (Nat.choose k r : ℝ) * (Nat.choose r 2 : ℝ) =
      (Nat.choose k 2 : ℝ) * (Nat.choose (k - 2) (r - 2) : ℝ) := by
    exact_mod_cast h
  rw [Nat.cast_choose_two, Nat.cast_choose_two] at hcast
  nlinarith [hcast]

theorem choose_marked_fraction (k r : ℕ) (hr2 : 2 ≤ r) (hrk : r ≤ k) :
    (Nat.choose (k - 2) (r - 2) : ℝ) / (Nat.choose k r : ℝ) =
      ((r : ℝ) * ((r : ℝ) - 1)) / ((k : ℝ) * ((k : ℝ) - 1)) := by
  have hmul := choose_marked_mul k r hr2
  have hk2 : 2 ≤ k := le_trans hr2 hrk
  have hkr : (Nat.choose k r : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hrk).ne'
  have hkpos : (0 : ℝ) < k := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hk2).trans_le (le_refl (k : ℕ))
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (1 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hk2)
    linarith
  have hk : ((k : ℝ) * ((k : ℝ) - 1)) ≠ 0 := by
    exact (mul_pos hkpos hk1).ne'
  field_simp [hkr, hk]
  linarith [hmul]

theorem choose_marked_le_one (k r : ℕ) (hr2 : 2 ≤ r) (hrk : r ≤ k) :
    ((r : ℝ) * ((r : ℝ) - 1)) / ((k : ℝ) * ((k : ℝ) - 1)) ≤ 1 := by
  have hk2 : 2 ≤ k := le_trans hr2 hrk
  have hkpos : (0 : ℝ) < k := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hk2).trans_le (le_refl (k : ℕ))
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (1 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hk2)
    linarith
  have hden : (0 : ℝ) < (k : ℝ) * ((k : ℝ) - 1) := mul_pos hkpos hk1
  have hrle : (r : ℝ) ≤ k := by exact_mod_cast hrk
  have hr1le : (r : ℝ) - 1 ≤ (k : ℝ) - 1 := by linarith
  have hr1 : (0 : ℝ) ≤ (r : ℝ) - 1 := by
    have : (1 : ℝ) ≤ r := by
      exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hr2)
    linarith
  have hnum : (r : ℝ) * ((r : ℝ) - 1) ≤ (k : ℝ) * ((k : ℝ) - 1) :=
    mul_le_mul hrle hr1le hr1 hkpos.le
  rw [div_le_one hden]
  exact hnum

end Qatlib.Papers.CommuteTest05.MatrixSubset
