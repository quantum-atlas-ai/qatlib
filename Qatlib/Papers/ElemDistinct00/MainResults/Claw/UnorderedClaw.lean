/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ElemDistinct00.MainResults.Defs
import Qatlib.Papers.ElemDistinct00.MainResults.Claw.OrReduction
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ElemDistinct00.MainResults.Claw

open Qatlib.Papers.ElemDistinct00.MainResults.Defs

def clawQ2UpperFunction (N M : ℕ) : ℝ :=
  if M ≤ N ^ 2 then
    (N : ℝ) ^ ((1 : ℝ) / 2) * (M : ℝ) ^ ((1 : ℝ) / 4) * Real.log (N : ℝ)
  else
    Real.sqrt (M : ℝ) * Real.log (N : ℝ)

theorem clawQ2UpperFunction_of_le {N M : ℕ} (h : M ≤ N ^ 2) :
    clawQ2UpperFunction N M =
      (N : ℝ) ^ ((1 : ℝ) / 2) * (M : ℝ) ^ ((1 : ℝ) / 4) * Real.log (N : ℝ) := by
  unfold clawQ2UpperFunction
  rw [if_pos h]

theorem clawQ2UpperFunction_of_gt {N M : ℕ} (h : ¬ M ≤ N ^ 2) :
    clawQ2UpperFunction N M = Real.sqrt (M : ℝ) * Real.log (N : ℝ) := by
  unfold clawQ2UpperFunction
  rw [if_neg h]

end Qatlib.Papers.ElemDistinct00.MainResults.Claw
