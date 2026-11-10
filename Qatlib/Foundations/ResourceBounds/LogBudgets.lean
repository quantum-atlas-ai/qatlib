/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Real.Pi.Bounds

namespace Qatlib.Foundations.ResourceBounds.LogBudgets
set_option autoImplicit false
noncomputable section

def log2 (x : ℝ) : ℝ := Real.logb 2 x

theorem log2_two_rpow (a : ℝ) : log2 ((2 : ℝ) ^ a) = a := by
  unfold log2 Real.logb
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2), mul_div_assoc,
      div_self (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne', mul_one]

theorem log2_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : log2 x ≤ log2 y := by
  unfold log2 Real.logb
  exact div_le_div_of_nonneg_right (Real.log_le_log hx hxy)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

theorem exponential_budget_iff (k : ℕ) (hk : 0 < k) (v C : ℝ) :
    ((k : ℝ) ^ v * (2 : ℝ) ^ ((k : ℝ) / 2) ≤ (2 : ℝ) ^ C) ↔
      (k : ℝ) / 2 + v * log2 (k : ℝ) ≤ C := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hbase : (2 : ℝ) ^ log2 (k : ℝ) = (k : ℝ) := by
    unfold log2
    exact Real.rpow_logb (by norm_num) (by norm_num) hkpos
  have step1 : (k : ℝ) ^ v = (2 : ℝ) ^ (v * log2 (k : ℝ)) := by
    have h1 : ((2 : ℝ) ^ log2 (k : ℝ)) ^ v = (2 : ℝ) ^ (log2 (k : ℝ) * v) := by
      rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hbase] at h1
    rw [h1, mul_comm (log2 (k : ℝ)) v]
  have key :
      (k : ℝ) ^ v * (2 : ℝ) ^ ((k : ℝ) / 2) =
        (2 : ℝ) ^ (v * log2 (k : ℝ) + (k : ℝ) / 2) := by
    rw [step1, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  rw [key, Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)]
  constructor <;> intro h <;> linarith

end
end Qatlib.Foundations.ResourceBounds.LogBudgets
