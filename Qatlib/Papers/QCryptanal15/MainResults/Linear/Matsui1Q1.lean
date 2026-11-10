/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCryptanal15.MainResults.Complexity.Core
import Qatlib.Papers.QCryptanal15.MainResults.Complexity.GroverBudget
set_option warningAsError false

set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace Qatlib.Papers.QCryptanal15.MainResults.Linear

open Complexity

noncomputable def matsui1Q1Data (ℓ ε : ℝ) : ℝ := ℓ / ε ^ 2

noncomputable def matsui1Q1Time (ℓ ε k : ℝ) : ℝ := ℓ / ε ^ 2 + pow2 ((k - ℓ) / 2)

theorem matsui1_q1_key_search_iterations (k ℓ : ℝ) :
    Real.sqrt (pow2 (k - ℓ)) = pow2 ((k - ℓ) / 2) := sqrt_pow2 (k - ℓ)

theorem matsui1_q1_cost (ℓ ε k : ℝ) :
    matsui1Q1Time ℓ ε k = matsui1Q1Data ℓ ε + Real.sqrt (pow2 (k - ℓ)) := by
  unfold matsui1Q1Time matsui1Q1Data
  rw [sqrt_pow2]

theorem matsui1_q1_classical_final_term (k ℓ : ℝ) :
    pow2 ((k - ℓ) / 2) ^ 2 = pow2 (k - ℓ) := pow2_half_sq (k - ℓ)

theorem matsui1_q1_time_ge_data (ℓ ε k : ℝ) :
    matsui1Q1Data ℓ ε ≤ matsui1Q1Time ℓ ε k := by
  unfold matsui1Q1Time
  exact le_add_of_nonneg_right (pow2_nonneg _)

theorem matsui1_q1_grover_budget (k ℓ : ℝ) :
    Real.pi / (4 * Real.sqrt (pow2 (-(k - ℓ)))) + 1 =
      Real.pi / 4 * pow2 ((k - ℓ) / 2) + 1 :=
  amplification_budget_pow2 (k - ℓ)

end Qatlib.Papers.QCryptanal15.MainResults.Linear
