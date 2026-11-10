/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Sqrt

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.GroundState08.MainResults.QmaWitness

theorem general_scratchpad_squared_time (n h : ℕ) (C p : ℝ) :
    (C * Real.sqrt ((2 : ℝ) ^ (n + h)) * p) ^ 2 =
      C ^ 2 * (2 : ℝ) ^ (n + h) * p ^ 2 := by
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]

theorem log_scratchpad_same_time (n h c : ℕ)
    (hc : h ≤ c * Nat.log 2 (n + 2)) :
    (2 : ℝ) ^ (n + h) ≤ (2 : ℝ) ^ n * ((n + 2 : ℝ)) ^ c := by
  rw [pow_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    (2 : ℝ) ^ h ≤ (2 : ℝ) ^ (c * Nat.log 2 (n + 2)) :=
      pow_le_pow_right₀ (by norm_num) hc
    _ = ((2 : ℝ) ^ Nat.log 2 (n + 2)) ^ c := by
      rw [mul_comm, pow_mul]
    _ ≤ ((n + 2 : ℝ)) ^ c := by
      apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : n + 2 ≠ 0)

theorem qma_witness_preparation_log_scratchpad
    (n h c : ℕ) (hc : h ≤ c * Nat.log 2 (n + 2)) (C p : ℝ) :
    (C * Real.sqrt ((2 : ℝ) ^ (n + h)) * p) ^ 2 ≤
      C ^ 2 * (2 : ℝ) ^ n * ((n + 2 : ℝ)) ^ c * p ^ 2 := by
  rw [general_scratchpad_squared_time]
  have hC2 : (0 : ℝ) ≤ C ^ 2 := sq_nonneg C
  have hp2 : (0 : ℝ) ≤ p ^ 2 := sq_nonneg p
  have hdim := log_scratchpad_same_time n h c hc
  nlinarith [mul_nonneg hC2 hp2, mul_le_mul_of_nonneg_left hdim (mul_nonneg hC2 hp2)]

theorem linear_scratchpad_quadratic (n : ℕ) :
    (2 : ℝ) ^ (n + n) = ((2 : ℝ) ^ n) ^ 2 := by
  rw [pow_add, pow_two]

end Qatlib.Papers.GroundState08.MainResults.QmaWitness
