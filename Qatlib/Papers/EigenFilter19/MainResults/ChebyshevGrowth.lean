/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section


/-!
# Chebyshev growth for eigenstate filtering

A complete proof of arXiv:1910.14596v4, Lemma 13, using its
logarithmic hyperbolic parameter and the explicit source range.
-/

set_option autoImplicit false

namespace Qatlib.Papers.EigenFilter19.MainResults

/-- The logarithmic hyperbolic parameter dominates the square-root gap on the source range. -/
theorem parameter_bound {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 3 - 2 * Real.sqrt 2) :
    Real.sqrt δ ≤ Real.log (1 + δ + Real.sqrt (2 * δ + δ ^ 2)) := by
  have htwo : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hroot : (11 / 8 : ℝ) ≤ Real.sqrt 2 := by
    have := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  have hδquarter : δ ≤ 1 / 4 := by linarith
  have hs0 := Real.sqrt_nonneg δ
  have hssq := Real.sq_sqrt hδ0
  have hs : Real.sqrt δ ≤ 1 / 2 := by nlinarith
  have hr : (4 / 3 : ℝ) * Real.sqrt δ ≤ Real.sqrt (2 * δ + δ ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg δ]
  have hfrac : Real.sqrt δ ≤
      2 * ((4 / 3 : ℝ) * Real.sqrt δ) / ((4 / 3 : ℝ) * Real.sqrt δ + 2) := by
    apply (le_div_iff₀ (by positivity)).2
    nlinarith
  calc
    Real.sqrt δ ≤
        2 * ((4 / 3 : ℝ) * Real.sqrt δ) / ((4 / 3 : ℝ) * Real.sqrt δ + 2) := hfrac
    _ ≤ Real.log (1 + (4 / 3 : ℝ) * Real.sqrt δ) :=
      Real.le_log_one_add_of_nonneg (by positivity)
    _ ≤ Real.log (1 + δ + Real.sqrt (2 * δ + δ ^ 2)) := by
      apply Real.log_le_log (by positivity)
      linarith

end Qatlib.Papers.EigenFilter19.MainResults
