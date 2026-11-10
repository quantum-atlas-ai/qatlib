/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCryptanal15.MainResults.Complexity.GroverBudget
import Qatlib.Papers.QCryptanal15.MainResults.Linear.Matsui2Q1
set_option warningAsError false

set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace Qatlib.Papers.QCryptanal15.MainResults.Linear

open Complexity

noncomputable def matsui2Q2Data (kout ε : ℝ) : ℝ := pow2 (kout / 2) / ε

noncomputable def matsui2Q2Time (kout ε k : ℝ) : ℝ :=
  pow2 (kout / 2) / ε + pow2 ((k - kout) / 2)

theorem matsui2_q2_data_grover (kout ε : ℝ) (hε : ε ≠ 0) :
    matsui2Q2Data kout ε = Real.sqrt (pow2 kout) * (1 / ε) := by
  unfold matsui2Q2Data
  rw [sqrt_pow2]
  field_simp

theorem matsui2_q2_cost (kout ε k : ℝ) :
    matsui2Q2Time kout ε k = matsui2Q2Data kout ε + Real.sqrt (pow2 (k - kout)) := by
  unfold matsui2Q2Time matsui2Q2Data
  rw [sqrt_pow2]

theorem matsui2_q2_time_ge_data (kout ε k : ℝ) :
    matsui2Q2Data kout ε ≤ matsui2Q2Time kout ε k := by
  unfold matsui2Q2Time
  exact le_add_of_nonneg_right (pow2_nonneg _)

theorem matsui2_q2_time_le_q1_time (kout ε k : ℝ) :
    matsui2Q2Time kout ε k ≤ matsui2Q1Time kout ε k := by
  unfold matsui2Q2Time matsui2Q1Time
  have h : 0 ≤ 1 / ε ^ 2 := div_nonneg zero_le_one (sq_nonneg ε)
  linarith

theorem matsui2_q2_data_grover_budget (kout : ℝ) :
    Real.pi / (4 * Real.sqrt (pow2 (-kout))) + 1 =
      Real.pi / 4 * pow2 (kout / 2) + 1 :=
  amplification_budget_pow2 kout

end Qatlib.Papers.QCryptanal15.MainResults.Linear
