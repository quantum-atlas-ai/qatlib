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

set_option autoImplicit false

namespace Qatlib.Papers.SolovayKitaev05.MainResults.CostRecurrence

noncomputable section

def levelLength (n : ℕ) : ℕ := 5 ^ n

theorem levelLength_succ (n : ℕ) : levelLength (n + 1) = 5 * levelLength n := by
  simp [levelLength, pow_succ, Nat.mul_comm]

theorem levelLength_eq_pow (n : ℕ) : (levelLength n : ℝ) = (5 : ℝ) ^ n := by
  simp [levelLength]

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

theorem time_le_const_mul_three_pow (t : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hrec : ∀ n, t (n + 1) ≤ 3 * t n + K) (n : ℕ) :
    t n ≤ (t 0 + K / 2) * 3 ^ n := by
  have h3 : (0 : ℝ) ≤ 3 ^ n := by positivity
  refine (time_le_three_pow t K hrec n).trans ?_
  nlinarith [h3]

end

end Qatlib.Papers.SolovayKitaev05.MainResults.CostRecurrence
