/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCryptanal15.MainResults.Complexity.GroverBudget
import Qatlib.Papers.QCryptanal15.MainResults.Linear.Matsui1Q1
import Qatlib.Papers.QCryptanal15.MainResults.Linear.Q2Distinguisher
set_option warningAsError false

set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace Qatlib.Papers.QCryptanal15.MainResults.Linear

open Complexity

noncomputable def matsui1Q2Data (ℓ ε : ℝ) : ℝ := ℓ / ε

noncomputable def matsui1Q2Time (ℓ ε k : ℝ) : ℝ := ℓ / ε + pow2 ((k - ℓ) / 2)

theorem matsui1_q2_data_is_linear_counting (ℓ ε : ℝ) :
    matsui1Q2Data ℓ ε = ℓ * q2LinearDistinguisherCost ε := by
  unfold matsui1Q2Data q2LinearDistinguisherCost
  ring

theorem matsui1_q2_data_eq_epsilon_mul_q1 (ℓ ε : ℝ) (hε : ε ≠ 0) :
    matsui1Q2Data ℓ ε = ε * matsui1Q1Data ℓ ε := by
  unfold matsui1Q2Data matsui1Q1Data
  field_simp

theorem matsui1_q2_cost (ℓ ε k : ℝ) :
    matsui1Q2Time ℓ ε k = matsui1Q2Data ℓ ε + Real.sqrt (pow2 (k - ℓ)) := by
  unfold matsui1Q2Time matsui1Q2Data
  rw [sqrt_pow2]

theorem matsui1_q2_time_ge_data (ℓ ε k : ℝ) :
    matsui1Q2Data ℓ ε ≤ matsui1Q2Time ℓ ε k := by
  unfold matsui1Q2Time
  exact le_add_of_nonneg_right (pow2_nonneg _)

theorem matsui1_q2_grover_budget (k ℓ : ℝ) :
    Real.pi / (4 * Real.sqrt (pow2 (-(k - ℓ)))) + 1 =
      Real.pi / 4 * pow2 ((k - ℓ) / 2) + 1 :=
  amplification_budget_pow2 (k - ℓ)

end Qatlib.Papers.QCryptanal15.MainResults.Linear
