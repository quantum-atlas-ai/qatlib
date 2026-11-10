/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Nat.Choose.Basic

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.CommuteTest05.ChainHitting

theorem johnson_marked_fraction (n r : ℕ) (hr2 : 2 ≤ r) (hrn : r ≤ n) :
    ((n.choose (r - 2) : ℝ) / (n.choose r : ℝ)) =
      ((r : ℝ) * ((r : ℝ) - 1)) /
        (((n : ℝ) - (r : ℝ) + 1) * ((n : ℝ) - (r : ℝ) + 2)) := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr2
  have hrm2 : r - 2 ≤ n := le_trans (Nat.sub_le _ _) hrn
  have hrm1 : r - 1 ≤ n := le_trans (Nat.sub_le _ _) hrn

  have hA : ((n.choose r : ℕ) : ℝ) * (r : ℝ) =
      ((n.choose (r - 1) : ℕ) : ℝ) * ((n : ℝ) - ((r - 1 : ℕ) : ℝ)) := by
    have h := Nat.choose_succ_right_eq n (r - 1)
    have h1 : r - 1 + 1 = r := by omega
    rw [h1] at h
    have hcast : ((n.choose r * r : ℕ) : ℝ) =
        ((n.choose (r - 1) * (n - (r - 1)) : ℕ) : ℝ) := by rw [h]
    push_cast at hcast
    rw [Nat.cast_sub hrm1] at hcast
    simpa using hcast
  have hB : ((n.choose (r - 1) : ℕ) : ℝ) * (((r - 1 : ℕ)) : ℝ) =
      ((n.choose (r - 2) : ℕ) : ℝ) * ((n : ℝ) - ((r - 2 : ℕ) : ℝ)) := by
    have h := Nat.choose_succ_right_eq n (r - 2)
    have h1 : r - 2 + 1 = r - 1 := by omega
    rw [h1] at h
    have hcast : ((n.choose (r - 1) * (r - 1) : ℕ) : ℝ) =
        ((n.choose (r - 2) * (n - (r - 2)) : ℕ) : ℝ) := by rw [h]
    push_cast at hcast
    rw [Nat.cast_sub hrm2] at hcast
    simpa using hcast
  have hr1c : (((r - 1 : ℕ)) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub hr1]; norm_num
  have hr2c : (((r - 2 : ℕ)) : ℝ) = (r : ℝ) - 2 := by
    rw [Nat.cast_sub hr2]; norm_num
  rw [hr1c] at hA
  rw [hr1c, hr2c] at hB

  have hA2 : ((n.choose r : ℕ) : ℝ) * (r : ℝ) * ((r : ℝ) - 1) =
      ((n.choose (r - 1) : ℕ) : ℝ) * ((n : ℝ) - ((r : ℝ) - 1)) * ((r : ℝ) - 1) := by
    exact congrArg (fun x : ℝ => x * ((r : ℝ) - 1)) hA
  have hB2 : ((n.choose (r - 1) : ℕ) : ℝ) * ((r : ℝ) - 1) *
        ((n : ℝ) - ((r : ℝ) - 1)) =
      ((n.choose (r - 2) : ℕ) : ℝ) * ((n : ℝ) - ((r : ℝ) - 2)) *
        ((n : ℝ) - ((r : ℝ) - 1)) := by
    exact congrArg (fun x : ℝ => x * ((n : ℝ) - ((r : ℝ) - 1))) hB
  have hden : (((n : ℝ) - (r : ℝ) + 1) * ((n : ℝ) - (r : ℝ) + 2)) ≠ 0 := by
    have h1 : 0 < (n : ℝ) - (r : ℝ) + 1 := by
      have : (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast hrn
      linarith
    have h2 : 0 < (n : ℝ) - (r : ℝ) + 2 := by
      have : (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast hrn
      linarith
    positivity
  have hnum : (n.choose r : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hrn).ne'
  rw [div_eq_div_iff hnum hden]
  nlinarith [hA2, hB2]

theorem johnson_marked_frac_lower (n r : ℕ) (hr2 : 2 ≤ r) (hrn : 2 * r ≤ n) :
    (r : ℝ) ^ 2 / (4 * (n : ℝ) ^ 2) ≤
      ((n.choose (r - 2) : ℝ) / (n.choose r : ℝ)) := by
  have hrle : r ≤ n := le_trans (Nat.le_mul_of_pos_left r (by norm_num : 0 < 2)) hrn
  rw [johnson_marked_fraction n r hr2 hrle]
  have hr0 : (0 : ℝ) < r := by exact_mod_cast lt_of_lt_of_le (by norm_num) hr2
  have hr1R : (1 : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hr2)
  have hr2R : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
  have hn0 : (0 : ℝ) < n := by
    have : 0 < r := lt_of_lt_of_le (by norm_num) hr2
    exact_mod_cast lt_of_lt_of_le this hrle
  have hrleR : (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast hrle
  have hDpos : 0 < ((n : ℝ) - (r : ℝ) + 1) * ((n : ℝ) - (r : ℝ) + 2) := by
    have h1 : 0 < (n : ℝ) - (r : ℝ) + 1 := by linarith
    have h2 : 0 < (n : ℝ) - (r : ℝ) + 2 := by linarith
    positivity
  have h4pos : (0 : ℝ) < 4 * (n : ℝ) ^ 2 := by positivity
  have hDle : ((n : ℝ) - (r : ℝ) + 1) * ((n : ℝ) - (r : ℝ) + 2) ≤ (n : ℝ) ^ 2 := by
    have h1 : (n : ℝ) - (r : ℝ) + 1 ≤ (n : ℝ) := by linarith
    have h2 : (n : ℝ) - (r : ℝ) + 2 ≤ (n : ℝ) := by linarith
    have h2n : (0 : ℝ) ≤ (n : ℝ) - (r : ℝ) + 2 := by linarith
    have hnn : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hn0
    have := mul_le_mul h1 h2 h2n hnn
    simpa [pow_two] using this
  rw [div_le_div_iff₀ h4pos hDpos]

  have hrr : (0 : ℝ) ≤ (r : ℝ) := le_of_lt hr0
  have hr4 : (r : ℝ) ≤ 4 * ((r : ℝ) - 1) := by nlinarith
  have hstep : (r : ℝ) ^ 2 * ((n : ℝ) - (r : ℝ) + 1) * ((n : ℝ) - (r : ℝ) + 2) ≤
      (r : ℝ) * ((r : ℝ) - 1) * (4 * (n : ℝ) ^ 2) := by
    have h1 : (r : ℝ) ^ 2 * ((n : ℝ) - (r : ℝ) + 1) * ((n : ℝ) - (r : ℝ) + 2)
        ≤ (r : ℝ) ^ 2 * (n : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hDle (sq_nonneg (r : ℝ))
      nlinarith [this]
    have h2 : (r : ℝ) ^ 2 * (n : ℝ) ^ 2 ≤ (r : ℝ) * ((r : ℝ) - 1) * (4 * (n : ℝ) ^ 2) := by
      nlinarith [hr4, sq_nonneg (n : ℝ), hrr, hn0]
    linarith
  linarith [hstep]

theorem johnson_pm_bound (r n pm : ℝ) (hr : 0 < r) (hn : 0 < n)
    (h : pm ≤ 1 - (1 / r) * (r ^ 2 / (4 * n ^ 2)) / 2) :
    pm ≤ 1 - r / (8 * n ^ 2) := by
  have e : (1 / r) * (r ^ 2 / (4 * n ^ 2)) / 2 = r / (8 * n ^ 2) := by
    field_simp
    ring
  rwa [e] at h

theorem johnson_hitting_bound (r n pm : ℝ) (hr : 0 < r) (hn : 0 < n)
    (hpm : pm ≤ 1 - r / (8 * n ^ 2)) :
    1 / (1 - pm) ≤ 8 * n ^ 2 / r := by
  have hpos : 0 < r / (8 * n ^ 2) := by positivity
  have hden : r / (8 * n ^ 2) ≤ 1 - pm := by linarith
  calc
    1 / (1 - pm) ≤ 1 / (r / (8 * n ^ 2)) :=
      div_le_div_of_nonneg_left (by norm_num) hpos hden
    _ = 8 * n ^ 2 / r := by
      field_simp

def johnsonQueryCost (r n : ℝ) : ℝ := r + 8 * n ^ 2 / r

theorem johnson_query_bound (r n pm : ℝ) (hr : 0 < r) (hn : 0 < n)
    (hpm : pm ≤ 1 - r / (8 * n ^ 2)) :
    r + 1 / (1 - pm) ≤ johnsonQueryCost r n := by
  have := johnson_hitting_bound r n pm hr hn hpm
  unfold johnsonQueryCost
  linarith

theorem johnson_query_at_unit (n : ℝ) (hn : 0 < n) :
    johnsonQueryCost n n = 9 * n := by
  unfold johnsonQueryCost
  field_simp
  ring

theorem johnson_query_le_nine_n (r n : ℝ) (hn : 0 < n) (hrn : n ≤ r)
    (hr8 : r ≤ 8 * n) :
    johnsonQueryCost r n ≤ 9 * n := by
  have hr : 0 < r := lt_of_lt_of_le hn hrn
  unfold johnsonQueryCost
  have hrmul : (r - n) * (r - 8 * n) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hkey : (r - n) * (r - 8 * n) = r ^ 2 - 9 * r * n + 8 * n ^ 2 := by ring
  have h2 : 8 * n ^ 2 / r ≤ 9 * n - r := by
    rw [div_le_iff₀ (lt_of_lt_of_le hn hrn)]
    nlinarith [hrmul, hkey]
  linarith

end Qatlib.Papers.CommuteTest05.ChainHitting
