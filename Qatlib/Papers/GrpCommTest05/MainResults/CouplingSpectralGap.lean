/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false

namespace Qatlib.Papers.GrpCommTest05.MainResults

open Real

theorem exp_neg_le_one_sub_half {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Real.exp (-y) ≤ 1 - y / 2 := by
  have hpos : (0 : ℝ) < 1 + y := by linarith
  have h1 : 1 + y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
  have hinv : Real.exp (-y) ≤ (1 + y)⁻¹ := by
    rw [Real.exp_neg]
    have := one_div_le_one_div_of_le hpos h1
    rwa [one_div, one_div] at this
  have hquad : (1 + y)⁻¹ ≤ 1 - y / 2 := by
    rw [inv_le_iff_one_le_mul₀ hpos]
    nlinarith
  linarith

theorem spectralGap_ge_of_exp_bound {lam T : ℝ} (hT : 0 < T) (hT1 : 1 ≤ 2 * Real.exp 1 * T)
    (hlam : lam ≤ Real.exp (-(1 / (2 * Real.exp 1 * T)))) :
    1 / (4 * Real.exp 1 * T) ≤ 1 - lam := by
  have hden : (0 : ℝ) < 2 * Real.exp 1 * T := by positivity
  have hy0 : 0 ≤ 1 / (2 * Real.exp 1 * T) := by positivity
  have hy1 : 1 / (2 * Real.exp 1 * T) ≤ 1 := by
    rw [div_le_one hden]
    linarith
  have hstep := exp_neg_le_one_sub_half hy0 hy1
  have hgap : 1 / (4 * Real.exp 1 * T) ≤ 1 - Real.exp (-(1 / (2 * Real.exp 1 * T))) := by
    have hhalf : 1 / (4 * Real.exp 1 * T) = (1 / (2 * Real.exp 1 * T)) / 2 := by
      field_simp
      ring
    rw [hhalf]
    nlinarith
  linarith

end Qatlib.Papers.GrpCommTest05.MainResults
