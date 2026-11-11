/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# Solovay–Kitaev length and time recurrences

This module defines the level-length factor `levelLength n = 5^n` and proves its fivefold
recurrence. It also solves an upper recurrence `t (n+1) ≤ 3*t n + K`, supplying explicit
exponential-in-level bounds for the length and runtime analysis in [DawsonNielsen2006].

## Main statements

* `levelLength_succ`: Advancing one recursion level multiplies the length growth factor by five,
  as in the word-length recurrence of [DawsonNielsen2006].
* `time_le_three_pow`: A recurrence bounded by `t (n+1) ≤ 3*t n + K` satisfies `t n ≤ 3^n*t 0 +
  K*(3^n - 1)/2`.

## References

* [Dawson and Nielsen, 2006][DawsonNielsen2006]
-/

set_option autoImplicit false

namespace Qatlib.Papers.SolovayKitaev05.MainResults.CostRecurrence

noncomputable section

/-- The length growth factor `5^n` at recursion level `n`. -/
def levelLength (n : ℕ) : ℕ := 5 ^ n

/-- Advancing one recursion level multiplies the length growth factor by five, as in the
word-length recurrence of [DawsonNielsen2006]. -/
theorem levelLength_succ (n : ℕ) : levelLength (n + 1) = 5 * levelLength n := by
  simp [levelLength, pow_succ, Nat.mul_comm]

/-- The real-valued level-length factor equals `(5 : ℝ)^n`. -/
theorem levelLength_eq_pow (n : ℕ) : (levelLength n : ℝ) = (5 : ℝ) ^ n := by
  simp [levelLength]

/-- A recurrence bounded by `t (n+1) ≤ 3*t n + K` satisfies `t n ≤ 3^n*t 0 + K*(3^n - 1)/2`. -/
theorem time_le_three_pow (t : ℕ → ℝ) (K : ℝ)
    (hrec : ∀ n, t (n + 1) ≤ 3 * t n + K) (n : ℕ) :
    t n ≤ 3 ^ n * t 0 + K * ((3 : ℝ) ^ n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h3 : (0 : ℝ) < 3 ^ n := by positivity
      calc t (n + 1) ≤ 3 * t n + K := hrec n
        _ ≤ 3 * (3 ^ n * t 0 + K * ((3 : ℝ) ^ n - 1) / 2) + K := by
            linarith [ih]
        _ = 3 ^ (n + 1) * t 0 + K * ((3 : ℝ) ^ (n + 1) - 1) / 2 := by
            rw [pow_succ]; ring

/-- For nonnegative overhead `K`, the recurrence `t (n+1) ≤ 3*t n + K` gives `t n ≤ (t 0 +
K/2)*3^n`. -/
theorem time_le_const_mul_three_pow (t : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hrec : ∀ n, t (n + 1) ≤ 3 * t n + K) (n : ℕ) :
    t n ≤ (t 0 + K / 2) * 3 ^ n := by
  have h3 : (0 : ℝ) ≤ 3 ^ n := by positivity
  refine (time_le_three_pow t K hrec n).trans ?_
  nlinarith [h3]

end

end Qatlib.Papers.SolovayKitaev05.MainResults.CostRecurrence
