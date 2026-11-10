/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace Qatlib.Papers.QCryptanal15.MainResults.Complexity

noncomputable def pow2 (x : ℝ) : ℝ := (2 : ℝ) ^ x

theorem pow2_pos (x : ℝ) : 0 < pow2 x := by
  unfold pow2
  exact Real.rpow_pos_of_pos (by norm_num) x

theorem pow2_nonneg (x : ℝ) : 0 ≤ pow2 x := (pow2_pos x).le

theorem pow2_ne_zero (x : ℝ) : pow2 x ≠ 0 := (pow2_pos x).ne'

theorem pow2_le_pow2 {x y : ℝ} (h : x ≤ y) : pow2 x ≤ pow2 y := by
  unfold pow2
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h

theorem pow2_add (x y : ℝ) : pow2 (x + y) = pow2 x * pow2 y := by
  unfold pow2
  exact Real.rpow_add (by norm_num) x y

theorem pow2_neg (x : ℝ) : pow2 (-x) = (pow2 x)⁻¹ := by
  unfold pow2
  exact Real.rpow_neg (by norm_num) x

theorem pow2_sub (x y : ℝ) : pow2 (x - y) = pow2 x / pow2 y := by
  rw [sub_eq_add_neg, pow2_add, pow2_neg, div_eq_mul_inv]

theorem pow2_mul (x y : ℝ) : pow2 (x * y) = (pow2 x) ^ y := by
  unfold pow2
  exact Real.rpow_mul (by norm_num) x y

@[simp] theorem pow2_zero : pow2 0 = 1 := by
  unfold pow2
  simp

theorem pow2_one : pow2 1 = 2 := by
  unfold pow2
  norm_num

theorem pow2_half_sq (x : ℝ) : pow2 (x / 2) ^ 2 = pow2 x := by
  have h : pow2 x = (pow2 (x / 2)) ^ (2 : ℝ) := by
    rw [← pow2_mul]
    ring_nf
  rw [h, Real.rpow_two]

theorem sqrt_pow2 (x : ℝ) : Real.sqrt (pow2 x) = pow2 (x / 2) := by
  rw [Real.sqrt_eq_rpow]
  have h : (pow2 x) ^ (1 / 2 : ℝ) = pow2 (x * (1 / 2)) := by
    rw [← pow2_mul]
  rw [h]
  ring_nf

theorem inv_sqrt_pow2_neg (h : ℝ) : (Real.sqrt (pow2 (-h)))⁻¹ = pow2 (h / 2) := by
  rw [sqrt_pow2]
  have h' : -h / 2 = -(h / 2) := by ring
  rw [h', pow2_neg, inv_inv]

theorem subset_cost_eq (n k : ℝ) (hn : 0 < n) (hk : 0 < k) :
    (n / Real.sqrt k) ^ (2 / 3 : ℝ) = n ^ (2 / 3 : ℝ) * k ^ (-(1 / 3) : ℝ) := by
  have hk' : Real.sqrt k = k ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow k
  have hkpos : 0 < k ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hk _
  rw [hk', Real.div_rpow (le_of_lt hn) hkpos.le (2 / 3 : ℝ)]
  have hk13 : (k ^ (1 / 2 : ℝ)) ^ (2 / 3 : ℝ) = k ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_mul (le_of_lt hk)]
    congr 1
    norm_num
  rw [hk13, div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hk) (1 / 3)]

end Qatlib.Papers.QCryptanal15.MainResults.Complexity
