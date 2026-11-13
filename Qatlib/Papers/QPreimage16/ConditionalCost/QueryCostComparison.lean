/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPreimage16.ConditionalCost.Defs

/-!
# Conditional attack-cost comparisons with Grover query counts

This module compares the resource expressions for SHA-256 and SHA3-256 preimage attacks with the
baseline `groverQueryCount = 2 ^ 128` [AmyEtAl2017]. Under the respective lower bounds on cycle
count, `sha256_attack_vs_query_analysis` and `sha3_256_attack_vs_query_analysis` prove a ratio
of at least 275 billion.

## Main statements

* `sha256_attack_vs_query_analysis`: If the cycle count is at least `2 ^ 153.8`, the modeled
  SHA-256 total cost divided by the baseline Grover query count is at least 275 billion. This is
  a conditional comparison for the estimates of [AmyEtAl2017].
* `sha3_256_attack_vs_query_analysis`: If the cycle count is at least `2 ^ 146.5`, the modeled
  SHA3-256 total cost divided by the baseline Grover query count is at least 275 billion. This
  is a conditional comparison for the estimates of [AmyEtAl2017].

## References

* [Amy et al., 2017][AmyEtAl2017]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QPreimage16.ConditionalCost

open Qatlib.Foundations.ResourceBounds.LogBudgets

/-- The baseline real-valued Grover query count `2 ^ 128`. -/
noncomputable def groverQueryCount : ℝ := (2 : ℝ) ^ (128 : ℝ)

/-- The baseline Grover query count is strictly positive. -/
theorem groverQueryCount_pos : 0 < groverQueryCount :=
  Real.rpow_pos_of_pos (by norm_num) _

/-- The quantity `6002 * 2 ^ 25.8` is at least 275 billion. -/
lemma sixK_two_pow_25_8 : (275000000000 : ℝ) ≤ 6002 * (2 : ℝ) ^ (25.8 : ℝ) := by
  have hsplit : (2 : ℝ) ^ (25.8 : ℝ) = (2 : ℝ) ^ (25 : ℝ) * (2 : ℝ) ^ (0.8 : ℝ) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    norm_num
  have h23 : (3 / 2 : ℝ) ≤ (2 : ℝ) ^ (0.8 : ℝ) := by
    have h5 : ((2 : ℝ) ^ (0.8 : ℝ)) ^ (5 : ℝ) = 16 := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have : (0.8 : ℝ) * 5 = 4 := by norm_num
      rw [this, show (4 : ℝ) = ((4 : ℕ) : ℝ) from rfl, Real.rpow_natCast]
      norm_num
    have h3 : ((3 / 2 : ℝ)) ^ (5 : ℝ) = 243 / 32 := by
      rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) from rfl, Real.rpow_natCast]
      norm_num
    have hcmp : ((3 / 2 : ℝ)) ^ (5 : ℝ) ≤ ((2 : ℝ) ^ (0.8 : ℝ)) ^ (5 : ℝ) := by
      rw [h5, h3]
      norm_num
    exact (Real.rpow_le_rpow_iff (by positivity) (by positivity)
      (by norm_num : (0 : ℝ) < 5)).mp hcmp
  have h25 : (2 : ℝ) ^ (25 : ℝ) = 33554432 := by
    rw [show (25 : ℝ) = ((25 : ℕ) : ℝ) from rfl, Real.rpow_natCast]
    norm_num
  rw [hsplit, h25]
  have h1 : (6002 : ℝ) * 33554432 * (3 / 2) ≤ 6002 * 33554432 * (2 : ℝ) ^ (0.8 : ℝ) := by
    have := mul_le_mul_of_nonneg_left h23
      (by norm_num : (0 : ℝ) ≤ 6002 * 33554432)
    linarith [this]
  have h2 : (275000000000 : ℝ) ≤ (6002 : ℝ) * 33554432 * (3 / 2) := by norm_num
  linarith [h1, h2]

/-- The quantity `1061600 * 2 ^ 18.5` is at least 275 billion. -/
lemma tenK_two_pow_18_5 : (275000000000 : ℝ) ≤ 1061600 * (2 : ℝ) ^ (18.5 : ℝ) := by
  have hsplit : (2 : ℝ) ^ (18.5 : ℝ) = (2 : ℝ) ^ (18 : ℝ) * (2 : ℝ) ^ (0.5 : ℝ) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    norm_num
  have hhalf : (1 : ℝ) ≤ (2 : ℝ) ^ (0.5 : ℝ) := by
    have := (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr
      (by norm_num : (0 : ℝ) ≤ 0.5)
    simpa using this
  have h18 : (2 : ℝ) ^ (18 : ℝ) = 262144 := by
    rw [show (18 : ℝ) = ((18 : ℕ) : ℝ) from rfl, Real.rpow_natCast]
    norm_num
  rw [hsplit, h18]
  have hb : (275000000000 : ℝ) ≤ (1061600 : ℝ) * (262144 * 1) := by norm_num
  have hm : (1061600 : ℝ) * (262144 * 1) ≤ (1061600 : ℝ) * (262144 * (2 : ℝ) ^ (0.5 : ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1061600)
    exact mul_le_mul_of_nonneg_left hhalf (by norm_num : (0 : ℝ) ≤ 262144)
  linarith [hb, hm]

/-- If the cycle count is at least `2 ^ 153.8`, the modeled SHA-256 total cost divided by the
baseline Grover query count is at least 275 billion. This is a conditional comparison for
the estimates of [AmyEtAl2017]. -/
theorem sha256_attack_vs_query_analysis (σ : ℝ)
    (hσ : (2 : ℝ) ^ (153.8 : ℝ) ≤ σ) :
    (275000000000 : ℝ) ≤ totalCost 2402 1 3600 σ / groverQueryCount := by
  have hq : (0 : ℝ) < groverQueryCount := groverQueryCount_pos
  have htot : totalCost 2402 1 3600 σ = 6002 * σ := by
    unfold totalCost
    norm_num
  have hdiv : (2 : ℝ) ^ (153.8 : ℝ) / groverQueryCount = (2 : ℝ) ^ (25.8 : ℝ) := by
    unfold groverQueryCount
    rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
    congr 1
    norm_num
  have heq : 6002 * (2 : ℝ) ^ (153.8 : ℝ) / groverQueryCount = 6002 * (2 : ℝ) ^ (25.8 : ℝ) := by
    rw [mul_div_assoc, hdiv]
  have hmono : 6002 * (2 : ℝ) ^ (153.8 : ℝ) / groverQueryCount ≤ 6002 * σ / groverQueryCount := by
    apply div_le_div_of_nonneg_right _ hq.le
    exact mul_le_mul_of_nonneg_left hσ (by norm_num)
  rw [htot]
  calc (275000000000 : ℝ) ≤ 6002 * (2 : ℝ) ^ (25.8 : ℝ) := sixK_two_pow_25_8
    _ = 6002 * (2 : ℝ) ^ (153.8 : ℝ) / groverQueryCount := heq.symm
    _ ≤ 6002 * σ / groverQueryCount := hmono

/-- If the cycle count is at least `2 ^ 146.5`, the modeled SHA3-256 total cost divided by the
baseline Grover query count is at least 275 billion. This is a conditional comparison for
the estimates of [AmyEtAl2017]. -/
theorem sha3_256_attack_vs_query_analysis (σ : ℝ)
    (hσ : (2 : ℝ) ^ (146.5 : ℝ) ≤ σ) :
    (275000000000 : ℝ) ≤ totalCost 3200 294 3600 σ / groverQueryCount := by
  have hq : (0 : ℝ) < groverQueryCount := groverQueryCount_pos
  have htot : totalCost 3200 294 3600 σ = 1061600 * σ := by
    unfold totalCost
    norm_num
  have hdiv : (2 : ℝ) ^ (146.5 : ℝ) / groverQueryCount = (2 : ℝ) ^ (18.5 : ℝ) := by
    unfold groverQueryCount
    rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
    congr 1
    norm_num
  have heq : 1061600 * (2 : ℝ) ^ (146.5 : ℝ) / groverQueryCount = 1061600 * (2 : ℝ) ^ (18.5 : ℝ) := by
    rw [mul_div_assoc, hdiv]
  have hmono : 1061600 * (2 : ℝ) ^ (146.5 : ℝ) / groverQueryCount ≤ 1061600 * σ / groverQueryCount := by
    apply div_le_div_of_nonneg_right _ hq.le
    exact mul_le_mul_of_nonneg_left hσ (by norm_num)
  rw [htot]
  calc (275000000000 : ℝ) ≤ 1061600 * (2 : ℝ) ^ (18.5 : ℝ) := tenK_two_pow_18_5
    _ = 1061600 * (2 : ℝ) ^ (146.5 : ℝ) / groverQueryCount := heq.symm
    _ ≤ 1061600 * σ / groverQueryCount := hmono

end Qatlib.Papers.QPreimage16.ConditionalCost
