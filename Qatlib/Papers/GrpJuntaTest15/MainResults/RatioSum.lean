/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Basic.Real.Basic

@[expose] public section

/-!
# Ratio sum in the proof of Claim 3.11

The EGGT constraint check in arXiv:1507.03126v1 reduces to a finite
sum of falling-factorial ratios. The proof splits off the first
factor and uses the paper's recurrence.
-/

set_option autoImplicit false

namespace Qatlib.Papers.GrpJuntaTest15.MainResults

open scoped BigOperators

/-- The finite sum of falling-factorial ratios from the proof of Claim 3.11,
with the constant term indexed by zero. -/
theorem truncated_ratio_sum_range (a b : ℕ) (hab : a ≤ b) :
    (∑ i ∈ Finset.range (a + 1), ∏ j ∈ Finset.range i,
      ((a : ℝ) - j) / ((b : ℝ) - j)) =
      ((b : ℝ) + 1) / ((b : ℝ) - a + 1) := by
  induction a generalizing b with
  | zero =>
    have hb : (b : ℝ) + 1 ≠ 0 := by positivity
    simp [hb]
  | succ a ih =>
    cases b with
    | zero => omega
    | succ b =>
      have hab' : a ≤ b := Nat.le_of_succ_le_succ hab
      have hb : (b : ℝ) + 1 ≠ 0 := by positivity
      have hδ : (b : ℝ) - a + 1 ≠ 0 := by
        have hle : (a : ℝ) ≤ b := by exact_mod_cast hab'
        linarith
      rw [Finset.sum_range_succ']
      simp only [Finset.prod_range_zero, Nat.cast_succ, add_sub_add_right_eq_sub]
      have hp (i : ℕ) :
          (∏ j ∈ Finset.range (i + 1),
            ((a : ℝ) + 1 - (j : ℝ)) / ((b : ℝ) + 1 - (j : ℝ))) =
          (∏ j ∈ Finset.range i, ((a : ℝ) - j) / ((b : ℝ) - j)) *
            (((a : ℝ) + 1) / ((b : ℝ) + 1)) := by
        rw [Finset.prod_range_succ']
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero, add_sub_add_right_eq_sub]
      simp_rw [hp]
      rw [← Finset.sum_mul, ih b hab']
      field_simp [hb, hδ]
      ring

/-- The source's `T(a,b)` in Claim 3.11, with the constant term written separately. -/
theorem claim3_11_truncated_ratio_identity (a b : ℕ) (hab : a ≤ b) :
    1 + (∑ i ∈ Finset.Icc 1 a, ∏ j ∈ Finset.range i, ((a : ℝ) - j) / ((b : ℝ) - j)) =
      ((b : ℝ) + 1) / ((b : ℝ) - a + 1) := by
  have h := truncated_ratio_sum_range a b hab
  have hI : Finset.Ico 1 a.succ = Finset.Icc 1 a := by
    ext i
    simp only [Finset.mem_Ico, Finset.mem_Icc, Nat.lt_succ_iff]
  rw [Finset.sum_range_eq_add_Ico _ (Nat.succ_pos a), Finset.prod_range_zero, hI] at h
  exact h

end Qatlib.Papers.GrpJuntaTest15.MainResults
