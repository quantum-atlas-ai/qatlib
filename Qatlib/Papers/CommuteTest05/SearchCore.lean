/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Repetition bounds for bounded-error search

This module defines the scalar failure and success expressions for repeated trials and proves
their exponential and constant-probability bounds. For success parameter `ε ∈ [0, 1]`, a
repetition count satisfying `k * ε ≥ 1` gives success at least one half, as used in
[Itakura2005].

## Main statements

* `failProb_le_exp`: Bounds repeated failure by `exp(-k * ε)`.
* `repetition_success_half`: Gives success at least one half when `k * ε ≥ 1`.
* `failProb_succ_le`: Failure is nonincreasing in the repetition count.

## References

* [Itakura, 2005][Itakura2005]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommuteTest05.SearchCore

/-- The failure expression `(1 - ε) ^ k` for `k` repetitions with per-trial success parameter
`ε`. -/
def failProb (ε : ℝ) (k : ℕ) : ℝ := (1 - ε) ^ k

/-- The success expression `1 - failProb ε k` for `k` repetitions. -/
def successProb (ε : ℝ) (k : ℕ) : ℝ := 1 - failProb ε k

/-- For `0 ≤ ε ≤ 1`, `failProb ε k ≤ exp(-k * ε)`, giving the exponential repetition estimate
used in [Itakura2005]. -/
theorem failProb_le_exp (ε : ℝ) (k : ℕ) (_hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    failProb ε k ≤ Real.exp (-(k : ℝ) * ε) := by
  have h1 : 1 - ε ≤ Real.exp (-ε) := by
    simpa [add_comm] using Real.add_one_le_exp (-ε)
  have h2 : (0 : ℝ) ≤ 1 - ε := by linarith
  calc failProb ε k = (1 - ε) ^ k := rfl
    _ ≤ (Real.exp (-ε)) ^ k := pow_le_pow_left₀ h2 h1 k
    _ = Real.exp ((k : ℝ) * (-ε)) := (Real.exp_nat_mul (-ε) k).symm
    _ = Real.exp (-(k : ℝ) * ε) := by ring_nf

/-- For `0 ≤ ε ≤ 1` and `k * ε ≥ 1`, the repeated failure probability is at most `1 / 2`, as
used for error reduction in [Itakura2005]. -/
theorem repetition_failure_half (ε : ℝ) (k : ℕ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hk : 1 ≤ (k : ℝ) * ε) : failProb ε k ≤ 1 / 2 := by
  have hexp : failProb ε k ≤ Real.exp (-(k : ℝ) * ε) := failProb_le_exp ε k hε hε1
  have hmono : Real.exp (-(k : ℝ) * ε) ≤ Real.exp (-1) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hhalf : Real.exp (-1) ≤ 1 / 2 := by
    have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ hpos]
    nlinarith [Real.exp_one_gt_two]
  linarith

/-- For `0 ≤ ε ≤ 1` and `k * ε ≥ 1`, the repeated success probability is at least `1 / 2`, as
used in [Itakura2005]. -/
theorem repetition_success_half (ε : ℝ) (k : ℕ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hk : 1 ≤ (k : ℝ) * ε) : 1 / 2 ≤ successProb ε k := by
  have h := repetition_failure_half ε k hε hε1 hk
  unfold successProb
  linarith

/-- For `0 ≤ ε ≤ 1`, adding one repetition cannot increase `failProb`, as used in [Itakura2005]. -/
theorem failProb_succ_le (ε : ℝ) (k : ℕ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    failProb ε (k + 1) ≤ failProb ε k := by
  have h0 : (0 : ℝ) ≤ 1 - ε := by linarith
  have h1 : 1 - ε ≤ 1 := by linarith
  unfold failProb
  calc (1 - ε) ^ (k + 1) = (1 - ε) ^ k * (1 - ε) := pow_succ _ _
    _ ≤ (1 - ε) ^ k * 1 := by
        exact mul_le_mul_of_nonneg_left h1 (pow_nonneg h0 k)
    _ = (1 - ε) ^ k := mul_one _

end Qatlib.Papers.CommuteTest05.SearchCore
