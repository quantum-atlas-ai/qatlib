/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommuteTest05.BatchCost

theorem powered_gap_bernoulli (r : ℝ) (u : ℕ) (hr : 1 ≤ r) :
    1 - (1 - 1 / r) ^ u ≤ (u : ℝ) * (1 / r) := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have ha : -2 ≤ -1 / r := by
    have h1 : (1 : ℝ) / r ≤ 1 := by
      rw [div_le_one hrpos]
      linarith
    have h2 : -1 / r ≥ -1 := by
      have : -1 / r = -(1 / r) := by ring
      rw [this]
      linarith
    linarith
  have h := one_add_mul_le_pow (a := -1 / r) ha u
  have h' : 1 - (u : ℝ) * (1 / r) ≤ (1 - 1 / r) ^ u := by
    simpa [neg_div, mul_neg, sub_eq_add_neg] using h
  linarith

theorem powered_survival_lower (r : ℝ) (u : ℕ) (hr : 1 ≤ r) :
    1 - (u : ℝ) / r ≤ (1 - 1 / r) ^ u := by
  have h := powered_gap_bernoulli r u hr
  have hmul : (u : ℝ) * (1 / r) = (u : ℝ) / r := by ring
  rw [hmul] at h
  linarith

end Qatlib.Papers.CommuteTest05.BatchCost
