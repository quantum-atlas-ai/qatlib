/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Linear accumulation of errors in contraction powers

This module proves linear error bounds for powers in a normed ring. The theorem
`norm_pow_sub_pow_le_of_norm_le_one` controls two contraction powers by their single-step error,
and `norm_pow_sub_pow_le_same` controls the difference between two powers of one contraction.
The mathematical context is [AharonovTaShma2007].

## Main statements

* `norm_pow_sub_pow_le_of_norm_le_one`: For contractions `a` and `b`, the error between their
  `n`th powers is at most `n` times the error between `a` and `b`.
* `norm_pow_sub_pow_le_same`: For a contraction `U` and `m ≤ n`, the error between `U ^ n` and
  `U ^ m` is at most `(n - m) * ‖U - 1‖`.

## References

* [Aharonov and Ta‐Shma, 2007][AharonovTaShma2007]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AdiabStateGen03.MainResults.TrotterCorollaries

variable {R : Type*} [SeminormedRing R] [NormOneClass R]

/-- For contractions `a` and `b`, the error between their `n`th powers is at most `n` times the
error between `a` and `b` [AharonovTaShma2007]. -/
theorem norm_pow_sub_pow_le_of_norm_le_one (a b : R) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (n : ℕ) : ‖a ^ n - b ^ n‖ ≤ (n : ℝ) * ‖a - b‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n := by
        rw [pow_succ', pow_succ']
        noncomm_ring
      rw [hstep]
      have hbn : ‖b ^ n‖ ≤ 1 :=
        (norm_pow_le b n).trans (pow_le_one₀ (norm_nonneg b) hb)
      calc ‖a * (a ^ n - b ^ n) + (a - b) * b ^ n‖
          ≤ ‖a * (a ^ n - b ^ n)‖ + ‖(a - b) * b ^ n‖ := norm_add_le _ _
        _ ≤ ‖a‖ * ‖a ^ n - b ^ n‖ + ‖a - b‖ * ‖b ^ n‖ := by
            exact add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ 1 * ((n : ℝ) * ‖a - b‖) + ‖a - b‖ * 1 := by
            refine add_le_add ?_ ?_
            · exact mul_le_mul ha ih (norm_nonneg _) zero_le_one
            · exact mul_le_mul_of_nonneg_left hbn (norm_nonneg _)
        _ = ((n + 1 : ℕ) : ℝ) * ‖a - b‖ := by push_cast; ring

/-- For a contraction `U` and `m ≤ n`, the error between `U ^ n` and `U ^ m` is at most `(n - m)
* ‖U - 1‖`. -/
theorem norm_pow_sub_pow_le_same (U : R) (hU : ‖U‖ ≤ 1) {m n : ℕ} (hmn : m ≤ n) :
    ‖U ^ n - U ^ m‖ ≤ ((n - m : ℕ) : ℝ) * ‖U - 1‖ := by
  have hpow : U ^ n = U ^ (n - m) * U ^ m := by
    rw [← pow_add, Nat.sub_add_cancel hmn]
  rw [hpow]
  have hsplit : U ^ (n - m) * U ^ m - U ^ m = (U ^ (n - m) - 1) * U ^ m := by
    noncomm_ring
  rw [hsplit]
  have hum : ‖U ^ m‖ ≤ 1 :=
    (norm_pow_le U m).trans (pow_le_one₀ (norm_nonneg U) hU)
  calc ‖(U ^ (n - m) - 1) * U ^ m‖
      ≤ ‖U ^ (n - m) - 1‖ * ‖U ^ m‖ := norm_mul_le _ _
    _ ≤ (((n - m : ℕ) : ℝ) * ‖U - 1‖) * 1 := by
        refine mul_le_mul ?_ hum (norm_nonneg _) (by positivity)
        simpa using norm_pow_sub_pow_le_of_norm_le_one U 1 hU (by simp) (n - m)
    _ = ((n - m : ℕ) : ℝ) * ‖U - 1‖ := by ring

end Qatlib.Papers.AdiabStateGen03.MainResults.TrotterCorollaries
