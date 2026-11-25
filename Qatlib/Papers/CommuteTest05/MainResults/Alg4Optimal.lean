/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.CommuteTest05.MainResults.CostBounds

@[expose] public section

/-!
# Optimality of the Algorithm 4 parameter choice

Section 3.2.1 of [Itakura2005] optimizes the Algorithm 4 cost `r * n ^ 2 + (k / sqrt r) * n ^ 2`
at `r = k ^ (2 / 3)` and concludes `O(k ^ (2 / 3) * n ^ 2)`. The paper's choice is not the exact
minimizer of the published expression: differentiating gives `r = (k / 2) ^ (2 / 3)`, where the
cost is `3 * k ^ (2 / 3) * n ^ 2 / 2 ^ (2 / 3)`, strictly below the printed value
`2 * k ^ (2 / 3) * n ^ 2`.

This module records what is true in either direction. The lower bound
`k ^ (2 / 3) * n ^ 2 ≤ alg4Cost k n r` holds for every positive `r`, so the paper's value is
within a factor of two of any other choice, which is enough for the stated asymptotic claim. The
literal statement that `k ^ (2 / 3)` minimizes the expression is false; a counterexample at
`k = n = 1` is recorded below.

## Main statements

* `alg4Cost_ge_rpow`: `k ^ (2 / 3) * n ^ 2 ≤ alg4Cost k n r` for `r > 0`.
* `alg4Cost_at_k_two_thirds_le_two_mul`: the value at `r = k ^ (2 / 3)` is at most twice the
  value at any other positive `r`.
* `alg4Cost_at_k_two_thirds_not_min`: the value at `r = k ^ (2 / 3)` is not minimal.

## References

* [Itakura, 2005][Itakura2005]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.CommuteTest05.MainResults

open Qatlib.Papers.CommuteTest05.MainResults.CostBounds

/-- For positive `k` and `r`, the Algorithm 4 cost is at least `k ^ (2 / 3) * n ^ 2`. The bound
splits on whether `r` exceeds `k ^ (2 / 3)`: above it the first summand already suffices, and
below it the second summand `k / sqrt r` exceeds `k ^ (2 / 3)`. -/
theorem alg4Cost_ge_rpow (k n r : ℝ) (hk : 0 < k) (hn : 0 ≤ n) (hr : 0 < r) :
    k ^ ((2 : ℝ) / 3) * n ^ 2 ≤ alg4Cost k n r := by
  unfold alg4Cost
  have hn2 : 0 ≤ n ^ 2 := pow_nonneg hn 2
  by_cases hcase : k ^ ((2 : ℝ) / 3) ≤ r
  · have h1 : k ^ ((2 : ℝ) / 3) * n ^ 2 ≤ r * n ^ 2 :=
      mul_le_mul_of_nonneg_right hcase hn2
    have h2 : 0 ≤ k / Real.sqrt r * n ^ 2 := by positivity
    linarith
  · push Not at hcase
    have hsqrt_lt : Real.sqrt r < k ^ ((1 : ℝ) / 3) := by
      rw [← sqrt_rpow_two_thirds k hk]
      exact Real.sqrt_lt_sqrt hr.le hcase
    have hmul : k ^ ((2 : ℝ) / 3) * Real.sqrt r ≤ k := by
      calc k ^ ((2 : ℝ) / 3) * Real.sqrt r
          ≤ k ^ ((2 : ℝ) / 3) * k ^ ((1 : ℝ) / 3) :=
            mul_le_mul_of_nonneg_left hsqrt_lt.le (Real.rpow_nonneg hk.le _)
        _ = k := by
            rw [← Real.rpow_add hk, show (2 : ℝ) / 3 + 1 / 3 = 1 by norm_num,
              Real.rpow_one]
    have hdiv : k ^ ((2 : ℝ) / 3) ≤ k / Real.sqrt r := by
      rw [le_div_iff₀ (Real.sqrt_pos.mpr hr)]
      exact hmul
    have h1 : k ^ ((2 : ℝ) / 3) * n ^ 2 ≤ k / Real.sqrt r * n ^ 2 :=
      mul_le_mul_of_nonneg_right hdiv hn2
    have h2 : 0 ≤ r * n ^ 2 := mul_nonneg hr.le hn2
    linarith

/-- The Algorithm 4 cost at the paper's choice `r = k ^ (2 / 3)` is at most twice the cost at any
other positive `r`. -/
theorem alg4Cost_at_k_two_thirds_le_two_mul (k n r : ℝ) (hk : 0 < k) (hn : 0 ≤ n) (hr : 0 < r) :
    alg4Cost k n (k ^ ((2 : ℝ) / 3)) ≤ 2 * alg4Cost k n r := by
  rw [alg4Cost_at_optimal k n hk]
  have h := alg4Cost_ge_rpow k n r hk hn hr
  nlinarith

/-- The paper's parameter `r = k ^ (2 / 3)` does not minimize `alg4Cost`. At `k = n = 1` the value
at `r = 9 / 16` is `91 / 48`, strictly below the value `2` at `r = 1`. -/
theorem alg4Cost_at_k_two_thirds_not_min :
    ¬ ∀ r : ℝ, 0 < r → alg4Cost 1 1 (1 ^ ((2 : ℝ) / 3)) ≤ alg4Cost 1 1 r := by
  intro h
  have hw := h (9 / 16) (by norm_num)
  have hsqrt : Real.sqrt (9 / 16 : ℝ) = 3 / 4 := by
    rw [show (9 / 16 : ℝ) = (3 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h1 : alg4Cost 1 1 (9 / 16 : ℝ) = 91 / 48 := by
    unfold alg4Cost
    rw [hsqrt]
    norm_num
  have h2 : alg4Cost 1 1 (1 ^ ((2 : ℝ) / 3)) = 2 := by
    rw [Real.one_rpow]
    unfold alg4Cost
    norm_num
  rw [h1, h2] at hw
  norm_num at hw

end Qatlib.Papers.CommuteTest05.MainResults
