/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DiscreteSim08.MainResults.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.DiscreteSim08.MainResults

theorem fidelity_three_stage_composition (ε1 ε2 ε3 : ℝ)
    (h1 : 0 ≤ ε1) (h2 : 0 ≤ ε2) (h3 : 0 ≤ ε3)
    (hsum : ε1 + ε2 + ε3 ≤ 1) :
    Real.sqrt (1 - (ε1 + ε2 + ε3)) ≤
      Real.sqrt (1 - ε1) * Real.sqrt (1 - ε2) * Real.sqrt (1 - ε3) := by
  have ha1 : 0 ≤ 1 - ε1 := by linarith
  have hb1 : 0 ≤ 1 - ε2 := by linarith
  have hc1 : 0 ≤ 1 - ε3 := by linarith
  have hprod0 : 0 ≤ Real.sqrt (1 - ε1) * Real.sqrt (1 - ε2) * Real.sqrt (1 - ε3) := by
    positivity
  refine Real.sqrt_le_iff.mpr ⟨hprod0, ?_⟩
  rw [show (Real.sqrt (1 - ε1) * Real.sqrt (1 - ε2) * Real.sqrt (1 - ε3)) ^ 2
      = (1 - ε1) * (1 - ε2) * (1 - ε3) by
    rw [mul_pow, mul_pow, Real.sq_sqrt ha1, Real.sq_sqrt hb1, Real.sq_sqrt hc1]]
  nlinarith [mul_nonneg h1 h2, mul_nonneg h1 h3, mul_nonneg h2 h3,
    mul_nonneg (mul_nonneg h1 h2) h3]

theorem fidelity_error_divided_nine (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    1 - ε ≤ Real.sqrt (1 - ε / 9) * Real.sqrt (1 - ε / 9) * Real.sqrt (1 - ε / 9) := by
  have hcomp := fidelity_three_stage_composition (ε / 9) (ε / 9) (ε / 9)
    (by linarith) (by linarith) (by linarith) (by linarith)
  have hsum : ε / 9 + ε / 9 + ε / 9 = ε / 3 := by ring
  rw [hsum] at hcomp
  have hge : 1 - ε ≤ Real.sqrt (1 - ε / 3) := by
    have hx : 0 ≤ 1 - ε := by linarith
    have hy : 0 ≤ 1 - ε / 3 := by linarith
    rw [Real.le_sqrt hx hy]
    nlinarith
  linarith

end Qatlib.Papers.DiscreteSim08.MainResults
