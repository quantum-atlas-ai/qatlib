/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section


/-! Scalar decay and constant bounds for sequential quantum measurements.

The statements are the closed numerical consequences from fixed arXiv:1607.03236v3.
They do not assert the existence of a measurement or tester.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SeqMeasure16.MainResults.ScalarBounds

/-- Repeated acceptance with overlap at most one minus epsilon decays exponentially. -/
theorem einselected_acceptance_pow {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (x : ℝ) (hx : |x| ≤ 1 - ε) (k : ℕ) :
    ((1 + x) / 2) ^ k ≤ Real.exp (-(ε * (k : ℝ) / 2)) := by
  have hxle : x ≤ 1 - ε := (le_abs_self x).trans hx
  have hxge : -(1 - ε) ≤ x := by
    have h := neg_abs_le x
    linarith
  have hnonneg : (0 : ℝ) ≤ (1 + x) / 2 := by linarith
  have hbase : (1 + x) / 2 ≤ 1 - ε / 2 := by linarith
  have hexp : (1 : ℝ) - ε / 2 ≤ Real.exp (-(ε / 2)) := by
    have h := Real.one_sub_le_exp_neg (ε / 2)
    simpa [neg_div] using h
  have hpos : (0 : ℝ) ≤ 1 - ε / 2 := by linarith
  calc
    ((1 + x) / 2) ^ k ≤ (1 - ε / 2) ^ k := pow_le_pow_left₀ hnonneg hbase k
    _ ≤ (Real.exp (-(ε / 2))) ^ k := pow_le_pow_left₀ hpos hexp k
    _ = Real.exp (-(ε * (k : ℝ) / 2)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- The exponential of negative one is less than three sevenths. -/
theorem exp_neg_one_lt_three_sevenths : Real.exp (-1) < (3 : ℝ) / 7 :=
  lt_trans Real.exp_neg_one_lt_d9 (by norm_num)

/-- One minus the exponential of negative one is at least four sevenths. -/
theorem four_sevenths_le_one_sub_exp_neg_one :
    (4 : ℝ) / 7 ≤ 1 - Real.exp (-1) := by
  linarith [exp_neg_one_lt_three_sevenths]

/-- The sequential-measurement constant divided by four is at least one seventh. -/
theorem one_seventh_le_quarter_mw_constant :
    (1 : ℝ) / 7 ≤ (1 - Real.exp (-1)) / 4 := by
  linarith [four_sevenths_le_one_sub_exp_neg_one]

/-- Multiplication by a nonnegative statistic preserves the one-seventh lower bound. -/
theorem seventh_le_mw_lower (x : ℝ) (hx : 0 ≤ x) :
    x / 7 ≤ (1 - Real.exp (-1)) * x / 4 := by
  calc
    x / 7 = (1 / 7) * x := by ring
    _ ≤ ((1 - Real.exp (-1)) / 4) * x :=
      mul_le_mul_of_nonneg_right one_seventh_le_quarter_mw_constant hx
    _ = (1 - Real.exp (-1)) * x / 4 := by ring

end Qatlib.Papers.SeqMeasure16.MainResults.ScalarBounds
