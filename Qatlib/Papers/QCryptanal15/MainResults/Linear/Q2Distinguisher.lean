/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCryptanal15.MainResults.Complexity.Core
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
set_option warningAsError false

set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace Qatlib.Papers.QCryptanal15.MainResults.Linear

open Complexity

noncomputable def q2LinearDistinguisherCost (ε : ℝ) : ℝ := 1 / ε

noncomputable def classicalLinearDistinguisherCost (ε : ℝ) : ℝ := 1 / ε ^ 2

noncomputable def countingErrorBound (p D : ℝ) : ℝ :=
  2 * Real.pi * Real.sqrt p / D + Real.pi ^ 2 / D ^ 2

noncomputable def countingBudget (ε : ℝ) : ℝ := 8 * Real.pi / ε

theorem q2_linear_quadratic_speedup (ε : ℝ) (hε : ε ≠ 0) :
    classicalLinearDistinguisherCost ε = q2LinearDistinguisherCost ε ^ 2 := by
  unfold classicalLinearDistinguisherCost q2LinearDistinguisherCost
  field_simp

theorem counting_budget_eq_linear_cost (ε : ℝ) :
    countingBudget ε = 8 * Real.pi * q2LinearDistinguisherCost ε := by
  unfold countingBudget q2LinearDistinguisherCost
  ring

theorem counting_budget_suffices (p ε : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    countingErrorBound p (countingBudget ε) ≤ ε / 2 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hs : Real.sqrt p ≤ 1 := by
    have hs2 : (Real.sqrt p) ^ 2 = p := Real.sq_sqrt hp0
    nlinarith [Real.sqrt_nonneg p]
  have hεne : ε ≠ 0 := hε0.ne'
  have hπne : Real.pi ≠ 0 := hπ.ne'
  unfold countingErrorBound countingBudget
  have hterm1 : 2 * Real.pi * Real.sqrt p / (8 * Real.pi / ε) =
      ε * Real.sqrt p / 4 := by
    field_simp
    ring
  have hterm2 : Real.pi ^ 2 / (8 * Real.pi / ε) ^ 2 = ε ^ 2 / 64 := by
    field_simp
    ring
  rw [hterm1, hterm2]
  have hb1 : ε * Real.sqrt p ≤ ε * 1 :=
    mul_le_mul_of_nonneg_left hs hε0.le
  have hb2 : ε ^ 2 ≤ ε := by nlinarith
  nlinarith

end Qatlib.Papers.QCryptanal15.MainResults.Linear
