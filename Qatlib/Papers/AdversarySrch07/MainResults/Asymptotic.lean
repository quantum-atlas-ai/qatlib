/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdversarySrch07.MainResults.OptimalBound.OptimalAdversary
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators ENNReal
open Finset

namespace Qatlib.Papers.AdversarySrch07.MainResults.Asymptotic

open Qatlib.Papers.AdversarySrch07.MainResults
open Qatlib.Papers.AdversarySrch07.MainResults.XiSequence
open Qatlib.Papers.AdversarySrch07.MainResults.OptimalBound

theorem AM_succ_zero (m : ℕ) : AM (m + 1) 0 = AM m 0 + xi m ^ 2 := by
  unfold AM
  rw [Nat.sub_zero, Nat.sub_zero, Finset.sum_range_succ]
  ring

theorem odd_value_eq_even_add (m : ℕ) :
    AM (m + 1) 0 + AM m 0 = 2 * AM m 0 + xi m ^ 2 := by
  rw [AM_succ_zero]; ring

theorem objective_odd_eq_even_add (m : ℕ) (hm : 1 ≤ m) :
    objective (2 * m + 1) (gammaOdd m) = objective (2 * m) (gammaEven m) + xi m ^ 2 := by
  rw [objective_gammaOdd m hm, objective_gammaEven, ← odd_value_eq_even_add]

theorem xi_sq_pos (m : ℕ) : 0 < xi m ^ 2 :=
  pow_pos (xi_pos m) 2

theorem xi_sq_le_one (m : ℕ) : xi m ^ 2 ≤ 1 := by
  have h := xi_le_one m
  have h0 := le_of_lt (xi_pos m)
  nlinarith [h, h0]

theorem xi_sq_le_inv_succ (m : ℕ) : xi m ^ 2 ≤ (1 : ℝ) / ((m : ℝ) + 1) := by
  induction m with
  | zero => norm_num [xi_zero]
  | succ n ih =>
    have hcast : (((n + 1 : ℕ)) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
    have hstep : xi (n + 1) ^ 2 = xi n ^ 2 * (((n : ℝ) + 1 / 2) / ((n : ℝ) + 1)) ^ 2 := by
      rw [xi_succ_ratio n, mul_div_assoc, mul_pow]
    have hsq : (((n : ℝ) + 1 / 2) / ((n : ℝ) + 1)) ^ 2 ≤ ((n : ℝ) + 1) / ((n : ℝ) + 2) := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    rw [hcast, hstep]
    calc xi n ^ 2 * (((n : ℝ) + 1 / 2) / ((n : ℝ) + 1)) ^ 2
        ≤ ((1 : ℝ) / ((n : ℝ) + 1)) * (((n : ℝ) + 1) / ((n : ℝ) + 2)) :=
          mul_le_mul ih hsq (sq_nonneg _) (by positivity)
      _ = (1 : ℝ) / ((n : ℝ) + 2) := by
          field_simp
          try ring

end Qatlib.Papers.AdversarySrch07.MainResults.Asymptotic
