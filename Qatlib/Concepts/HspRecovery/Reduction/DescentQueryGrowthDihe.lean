/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.DescentQueryGrowthStat
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Subexponential descent query bounds

This module bounds `sourcePowerTwoQueryBudget` by an explicit expression involving the ceiling
of a square root. The resulting `sourceDescentQueryGrowth` establishes a bound of the form `C *
2^(c * sqrt n)` for the descent query budget, in the setting of [Kuperberg2005].

## Main statements

* `sourceQueryBudget_polynomial`: gives an explicit bound using `rootCeil`.
* `sourceDescentQueryGrowth`: proves the existential subexponential query bound.

## References

* [Kuperberg, 2005][Kuperberg2005]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.ReductionCore

/-- The natural ceiling of the real square root of `n`. -/
private noncomputable def rootCeil (n : ℕ) : ℕ := Nat.ceil (Real.sqrt (n : ℝ))

/-- The ceiling of the square root is monotone on natural numbers. -/
private theorem rootCeil_mono : Monotone rootCeil := by
  intro n m hnm
  exact Nat.ceil_mono (Real.sqrt_le_sqrt (Nat.cast_le.mpr hnm))

/-- The power-of-two descent query budget is at most `24000 * (n + 1)^2 * 2^(3 * rootCeil n)`. -/
theorem sourceQueryBudget_polynomial (n : ℕ) :
    sourcePowerTwoQueryBudget n ≤ 24000 * (n + 1) ^ 2 * 2 ^ (3 * rootCeil n) := by
  induction n with
  | zero => simp [sourcePowerTwoQueryBudget]
  | succ n ih =>
    have hm : 2 ^ (3 * rootCeil n) ≤ 2 ^ (3 * rootCeil (n + 1)) :=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 3 (rootCeil_mono (by omega)))
    have hs : (n + 2) + (n + 1) ^ 2 ≤ (n + 2) ^ 2 := by nlinarith
    calc
      sourcePowerTwoQueryBudget (n + 1) =
          24000 * (n + 2) * 2 ^ (3 * rootCeil n) + sourcePowerTwoQueryBudget n := by
        simp only [sourcePowerTwoQueryBudget, sourceParityTrials, rootCeil]
        ring
      _ ≤ 24000 * ((n + 2) + (n + 1) ^ 2) * 2 ^ (3 * rootCeil n) := by
        nlinarith [ih]
      _ ≤ 24000 * (n + 2) ^ 2 * 2 ^ (3 * rootCeil n) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hs)
      _ ≤ _ := Nat.mul_le_mul_left _ hm

/-- Every natural number `n` is at most the square of `rootCeil n`. -/
private theorem rootCeil_square (n : ℕ) : n ≤ rootCeil n ^ 2 := by
  have hs : Real.sqrt (n : ℝ) ≤ (rootCeil n : ℝ) := Nat.le_ceil _
  have hsq := Real.sq_sqrt (Nat.cast_nonneg n)
  have hm : (0 : ℝ) ≤ rootCeil n := Nat.cast_nonneg _
  have hnn : (n : ℝ) ≤ (rootCeil n : ℝ) ^ 2 := by nlinarith [Real.sqrt_nonneg (n : ℝ)]
  exact_mod_cast hnn

/-- The descent query budget is bounded by `C * 2^(c * sqrt n)` for positive real constants `C`
and `c`. See [Kuperberg2005] for the dihedral sieve setting. -/
theorem sourceDescentQueryGrowth : SourceDescentQueryGrowth := by
  refine ⟨3072000, 7, by norm_num, by norm_num, ?_⟩
  intro n
  have hnp : n + 1 ≤ 2 ^ (2 * rootCeil n) :=
    (show n + 1 ≤ 2 * rootCeil n ^ 2 + 1 by nlinarith [rootCeil_square n]).trans
      (Nat.two_mul_sq_add_one_le_two_pow_two_mul _)
  have hbudget : sourcePowerTwoQueryBudget n ≤ 24000 * 2 ^ (7 * rootCeil n) := by
    calc
      sourcePowerTwoQueryBudget n ≤ 24000 * (n + 1) ^ 2 * 2 ^ (3 * rootCeil n) :=
        sourceQueryBudget_polynomial n
      _ ≤ 24000 * (2 ^ (2 * rootCeil n)) ^ 2 * 2 ^ (3 * rootCeil n) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hnp 2))
      _ = _ := by
        rw [← pow_mul, mul_assoc, ← pow_add]
        congr 2
        omega
  have hceil : (rootCeil n : ℝ) ≤ Real.sqrt (n : ℝ) + 1 :=
    (Nat.ceil_lt_add_one (Real.sqrt_nonneg _)).le
  have hexp : ((7 * rootCeil n : ℕ) : ℝ) ≤ 7 * Real.sqrt (n : ℝ) + 7 := by
    push_cast
    linarith
  calc
    (sourcePowerTwoQueryBudget n : ℝ) ≤ 24000 * (2 : ℝ) ^ (7 * rootCeil n : ℕ) := by
      exact_mod_cast hbudget
    _ = 24000 * (2 : ℝ) ^ ((7 * rootCeil n : ℕ) : ℝ) := by rw [Real.rpow_natCast]
    _ ≤ 24000 * (2 : ℝ) ^ (7 * Real.sqrt (n : ℝ) + 7) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
        (by norm_num)
    _ = 3072000 * (2 : ℝ) ^ (7 * Real.sqrt (n : ℝ)) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      norm_num
      ring

end Qatlib.Concepts.HspRecovery.ReductionCore
