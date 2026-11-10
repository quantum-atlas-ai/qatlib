/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ResourceBounds.LogBudgets
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QPreimage16.ConditionalCost

open Qatlib.Foundations.ResourceBounds.LogBudgets

noncomputable def ledgerIterations (k : ℕ) : ℝ :=
  ((Int.floor ((Real.pi / 4) * (2 : ℝ) ^ k) : ℤ) : ℝ)

noncomputable def surfaceCodeCycles (iters tDepth : ℝ) : ℝ :=
  iters * 530 * (2 * tDepth)

noncomputable def totalCost (n Φ nDist σ : ℝ) : ℝ := (n + Φ * nDist) * σ

noncomputable def overhead (total : ℝ) (k : ℕ) : ℝ := (log2 total - k) / log2 256

theorem log2_256 : log2 256 = 8 := by
  unfold log2
  have h : (256 : ℝ) = 2 ^ (8 : ℕ) := by norm_num
  rw [h, Real.logb_pow]
  rw [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
  norm_num

theorem overhead_eq (total : ℝ) (k : ℕ) :
    overhead total k = (log2 total - k) / 8 := by
  unfold overhead
  rw [log2_256]

end Qatlib.Papers.QPreimage16.ConditionalCost
