/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# Precision bits for the gradient register

Theorem 21 of Gilyén, Arunachalam and Wiebe (arXiv:1711.00465v3) defines
the register width as a sum of two signed ceilings. Their logarithm arguments
multiply to `12 * L / ε`, independently of the grid scale.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QGradient17.GradientAlgo

/-- The two signed precisions in Theorem 21 give an explicit upper bound on the register width. -/
theorem source_precision_bits_order {r ε L : ℝ} (hr : 0 < r) (hε : 0 < ε) (hεL : ε < L) :
    let nε : ℤ := ⌈Real.logb 2 (4 / (r * ε))⌉
    let nL : ℤ := ⌈Real.logb 2 (3 * r * L)⌉
    ((nε + nL).toNat : ℝ) < Real.logb 2 (12 * L / ε) + 2 := by
  dsimp only
  have hL : 0 < L := hε.trans hεL
  have hfirst : 0 < 4 / (r * ε) := by positivity
  have hsecond : 0 < 3 * r * L := by positivity
  have hprod : 4 / (r * ε) * (3 * r * L) = 12 * L / ε := by
    field_simp [hr.ne', hε.ne']
    ring
  have hlog := Real.logb_mul (b := 2) hfirst.ne' hsecond.ne'
  rw [hprod] at hlog
  have hpos : 0 < Real.logb 2 (12 * L / ε) := by
    apply Real.logb_pos (by norm_num)
    apply (lt_div_iff₀ hε).2
    linarith
  have hceil := Int.le_ceil (Real.logb 2 (4 / (r * ε)))
  have hceil' := Int.le_ceil (Real.logb 2 (3 * r * L))
  have hnR : (0 : ℝ) ≤
      (((⌈Real.logb 2 (4 / (r * ε))⌉ : ℤ) + ⌈Real.logb 2 (3 * r * L)⌉ : ℤ) : ℝ) := by
    push_cast
    linarith
  have hn : 0 ≤ (⌈Real.logb 2 (4 / (r * ε))⌉ : ℤ) + ⌈Real.logb 2 (3 * r * L)⌉ := by
    exact_mod_cast hnR
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hn, Int.cast_add]
  linarith [Int.ceil_lt_add_one (Real.logb 2 (4 / (r * ε))),
    Int.ceil_lt_add_one (Real.logb 2 (3 * r * L))]

end Qatlib.Papers.QGradient17.GradientAlgo
