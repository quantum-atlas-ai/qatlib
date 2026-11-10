/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AdiabStateGen03.MainResults.JaggedPath

theorem overlap_le_sqrt_gap {η r : ℝ} (_hη0 : 0 ≤ η) (_hη1 : η ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    r ≤ Real.sqrt (1 - 4 * (1 - η) * η * (1 - r ^ 2)) := by

  have hr2 : 0 ≤ 1 - r ^ 2 := by nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr1)]

  have h4 : 4 * (1 - η) * η ≤ 1 := by nlinarith [sq_nonneg (2 * η - 1)]

  have hprod : 4 * (1 - η) * η * (1 - r ^ 2) ≤ 1 := by
    have := mul_le_mul_of_nonneg_right h4 hr2
    nlinarith
  have hnonneg : 0 ≤ 1 - 4 * (1 - η) * η * (1 - r ^ 2) := by linarith
  rw [Real.le_sqrt hr0 hnonneg]

  have hkey : 0 ≤ (1 - r ^ 2) * (1 - 4 * (1 - η) * η) :=
    mul_nonneg hr2 (by linarith)
  nlinarith [hkey]

end Qatlib.Papers.AdiabStateGen03.MainResults.JaggedPath
