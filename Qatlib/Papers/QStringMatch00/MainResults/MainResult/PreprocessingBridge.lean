/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QStringMatch00.MainResults.MainResult
import Qatlib.Papers.QStringMatch00.MainResults.DeterministicSample

/-!
# Deterministic-sample cost bridge for QStringMatch00

This file connects the deterministic-sample stage bound to the main scalar
preprocessing cost by choosing the preprocessing coefficient explicitly.  It
does not construct the sample oracle or a string-matching circuit.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QStringMatch00.MainResults.MainResult

open Qatlib.Papers.QStringMatch00.MainResults.MainResult

open Qatlib.Papers.QStringMatch00.MainResults.DeterministicSample


/-- The deterministic-sample stage budget is covered by `preprocessCost` when
the coefficient is chosen to absorb the logarithmic guard. -/
theorem deterministic_sample_cost_le_preprocessCost
    (m : ℕ) (hm : 2 ≤ m) (C : ℝ) (hC : 0 ≤ C) :
    (stageCount m : ℝ) * stageCost m C ≤
      preprocessCost m (C * (2 * Real.log ((m : ℝ) + 2) + 2) /
        (Real.log (m : ℝ) + 1)) := by
  have h := deterministic_sample_cost m hm C hC
  have hlog : 0 < Real.log (m : ℝ) + 1 := by
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    have hnonneg : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
    linarith
  calc
    (stageCount m : ℝ) * stageCost m C ≤
        C * (2 * Real.log ((m : ℝ) + 2) + 2) * Real.sqrt m *
          (Real.log (m : ℝ) + 1) := h
    _ = preprocessCost m (C * (2 * Real.log ((m : ℝ) + 2) + 2) /
        (Real.log (m : ℝ) + 1)) := by
      unfold preprocessCost
      field_simp [ne_of_gt hlog]

end Qatlib.Papers.QStringMatch00.MainResults.MainResult
