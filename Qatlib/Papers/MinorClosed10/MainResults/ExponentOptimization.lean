/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-! # Exponent bookkeeping for Theorem 4.4

Childs--Kothari, arXiv:1011.1443v2, Section 4.3, pp. 16--17.

The optimisation in Theorem 4.4 substitutes
`k_i = √(t_i)·n^(1/2 − 1/(vc+1))` and compares the resulting expression with
`n^(3/2 − 1/(vc+1))`.  This module proves the exponent identity behind that
comparison and the constant-factor stability of the integer rounding step.  The
full sum and product estimates over the `vc` blocks are not formalized here.
-/

set_option autoImplicit false
namespace Qatlib.Papers.MinorClosed10.MainResults.ExponentOptimization

open Real

/-- The exponent `1/2 − 1/(vc+1)` used for the block parameters `k_i`. -/
noncomputable def blockExponent (vc : ℕ) : ℝ := (1 : ℝ) / 2 - 1 / ((vc : ℝ) + 1)

/-- The target exponent `3/2 − 1/(vc+1)` is one power of `n` above the block
exponent. -/
theorem targetExponent_eq_one_add (vc : ℕ) :
    (3 : ℝ) / 2 - 1 / ((vc : ℝ) + 1) = 1 + blockExponent vc := by
  unfold blockExponent
  ring

/-- Consequently `n^(3/2 − 1/(vc+1)) = n · n^(1/2 − 1/(vc+1))` for `n > 0`. -/
theorem rpow_target_eq (vc : ℕ) {n : ℝ} (hn : 0 < n) :
    Real.rpow n ((3 : ℝ) / 2 - 1 / ((vc : ℝ) + 1)) =
      n * Real.rpow n (blockExponent vc) := by
  rw [targetExponent_eq_one_add]
  simpa [Real.rpow_one] using Real.rpow_add hn 1 (blockExponent vc)

/-- For `vc ≥ 2` the block exponent is nonnegative. -/
theorem blockExponent_nonneg {vc : ℕ} (hvc : 2 ≤ vc) : 0 ≤ blockExponent vc := by
  unfold blockExponent
  have h : (1 : ℝ) ≤ (vc : ℝ) := by exact_mod_cast (le_trans (by norm_num) hvc)
  have hpos : (0 : ℝ) < (vc : ℝ) + 1 := by linarith
  have : 1 / ((vc : ℝ) + 1) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num) (by linarith)
  linarith

/-- For `vc ≥ 2` the target exponent is at most `3/2`. -/
theorem targetExponent_le_three_halves {vc : ℕ} (hvc : 2 ≤ vc) :
    (3 : ℝ) / 2 - 1 / ((vc : ℝ) + 1) ≤ 3 / 2 := by
  have h : 0 ≤ 1 / ((vc : ℝ) + 1) := by positivity
  linarith

/-- Replacing `α` by a rounded value in `[α, 2α]` and `k` by a rounded value in
`[k, 2k]` changes the ratio `k/α` by at most a factor of two. -/
theorem rounding_ratio_le_two {α α' k k' : ℝ} (hα : 0 < α) (hα' : α ≤ α')
    (_hα2 : α' ≤ 2 * α) (hk : 0 < k) (_hk' : k ≤ k') (hk2 : k' ≤ 2 * k) :
    k' / α' ≤ 2 * (k / α) := by
  have hα'pos : 0 < α' := lt_of_lt_of_le hα hα'
  rw [div_le_iff₀ hα'pos]
  have hdiv : 1 ≤ α' / α := (one_le_div hα).mpr hα'
  have hmul : 2 * (k / α) * α' = 2 * k * (α' / α) := by
    field_simp
  rw [hmul]
  have hbase : 2 * k ≤ 2 * k * (α' / α) := by
    nlinarith [hk, hdiv]
  linarith

/-- The square-root factor in display (2) is stable under the same rounding. -/
theorem sqrt_rounding_le {α α' k k' : ℝ} (hα : 0 < α) (hα' : α ≤ α')
    (hα2 : α' ≤ 2 * α) (hk : 0 < k) (hk' : k ≤ k') (hk2 : k' ≤ 2 * k) :
    Real.sqrt (k' / α') ≤ Real.sqrt 2 * Real.sqrt (k / α) := by
  have hratio := rounding_ratio_le_two hα hα' hα2 hk hk' hk2
  calc Real.sqrt (k' / α') ≤ Real.sqrt (2 * (k / α)) :=
        Real.sqrt_le_sqrt hratio
    _ = Real.sqrt 2 * Real.sqrt (k / α) := Real.sqrt_mul (by norm_num) _

end Qatlib.Papers.MinorClosed10.MainResults.ExponentOptimization
