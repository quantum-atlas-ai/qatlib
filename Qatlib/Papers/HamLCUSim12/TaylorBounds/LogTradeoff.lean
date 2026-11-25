/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Continuous exponent tradeoff for the multiproduct formula

This is the scalar optimization in Childs and Wiebe, arXiv:1202.5822v1,
Eqs. (80)–(82). The continuous optimizer is computed before rounding the
order to an integer.
-/

set_option autoImplicit false

namespace Qatlib.Papers.HamLCUSim12.TaylorBounds

/-- The square-root exponent bounds Eq. (80) from below at every positive real order. -/
theorem log_min_le {A B x : ℝ} (hA : 0 < A) (hB : 1 < B) (hx : 0 < x) :
    Real.sqrt (A * Real.log B) ≤ A * x + Real.log B / (4 * x) := by
  have hlog := Real.log_pos hB
  let y := Real.log B / (4 * x)
  have hy : 0 < y := by dsimp [y]; positivity
  have hmul : y * (4 * x) = Real.log B :=
    (eq_div_iff (show 4 * x ≠ 0 by positivity)).mp rfl
  change Real.sqrt (A * Real.log B) ≤ A * x + y
  refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  calc
    A * Real.log B = 4 * (A * x) * y := by rw [← hmul]; ring
    _ ≤ (A * x + y) ^ 2 := by nlinarith [sq_nonneg (A * x - y)]

/-- The continuous optimizer for Eq. (80) attains the square-root exponent with
coefficient at most `8 / 5` on the certified interval for `η`. -/
theorem log_optimal (η B : ℝ) (hηlo : 305 / 1000 < η) (hηhi : η < 312 / 1000)
    (hB : 1 < B) :
    let A := 1 + Real.log η / 2 + Real.log (25 / 3)
    Real.sqrt A ≤ 8 / 5 ∧
      A * Real.sqrt (Real.log B / (4 * A)) +
        Real.log B / (4 * Real.sqrt (Real.log B / (4 * A))) = Real.sqrt (A * Real.log B) := by
  let A := 1 + Real.log η / 2 + Real.log (25 / 3)
  change Real.sqrt A ≤ 8 / 5 ∧
    A * Real.sqrt (Real.log B / (4 * A)) +
      Real.log B / (4 * Real.sqrt (Real.log B / (4 * A))) = Real.sqrt (A * Real.log B)
  have hη : 0 < η := by linarith
  have hlog : Real.log (η * (25 / 3 : ℝ) ^ 2) =
      Real.log η + 2 * Real.log (25 / 3) := by
    rw [Real.log_mul hη.ne' (by positivity), Real.log_pow]
    norm_num
  have hA : 0 < A := by
    have h := Real.log_nonneg (show 1 ≤ η * (25 / 3 : ℝ) ^ 2 by nlinarith)
    rw [hlog] at h
    dsimp [A]
    linarith
  have hexp : (65 / 3 : ℝ) ≤ Real.exp (78 / 25) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg (x := (78 / 25 : ℝ)) (by norm_num) 8)
    norm_num [Finset.sum_range_succ, Nat.factorial_succ]
  have hlog' : Real.log (η * (25 / 3 : ℝ) ^ 2) ≤ 78 / 25 :=
    (Real.log_le_iff_le_exp (by positivity)).mpr (le_trans (by nlinarith) hexp)
  rw [hlog] at hlog'
  refine ⟨Real.sqrt_le_iff.mpr ⟨by norm_num, ?_⟩, ?_⟩
  · dsimp [A]
    nlinarith
  · have hBpos := Real.log_pos hB
    set x := Real.sqrt (Real.log B / (4 * A)) with hx
    have hxpos : 0 < x := Real.sqrt_pos.2 (by positivity)
    have hx2 : x ^ 2 = Real.log B / (4 * A) := Real.sq_sqrt (by positivity)
    have hBexp : Real.log B = 4 * A * x ^ 2 := by
      have h := (eq_div_iff (show 4 * A ≠ 0 by positivity)).mp hx2
      nlinarith
    rw [hBexp]
    have hcancel : 4 * A * x ^ 2 / (4 * x) = A * x := by
      field_simp
    have hsq : A * (4 * A * x ^ 2) = (2 * A * x) ^ 2 := by ring
    rw [hcancel, hsq, Real.sqrt_sq (by positivity)]
    ring

end Qatlib.Papers.HamLCUSim12.TaylorBounds
