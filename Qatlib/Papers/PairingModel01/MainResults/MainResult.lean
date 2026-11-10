/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PairingModel01.MainResults.StepCount
import Qatlib.Papers.PairingModel01.MainResults.ShortTimeApproximation
import Qatlib.Papers.PairingModel01.MainResults.AdiabaticProduct
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.PairingModel01.MainResults

open Qatlib.Concepts.ResourceBounds.AsymBounds

theorem main_result_steps_polynomial :
    ∃ C : ℚ, ∀ N : ℕ, pairingStepCount N ≤ C * ((N : ℚ) + 1) ^ 4 := by
  refine ⟨10, fun N => ?_⟩
  have h := pairingStepCount_le_budget N
  unfold pairingStepBudget at h
  have hcast : ((10 * (N + 1) ^ 4 : ℕ) : ℚ) = 10 * ((N : ℚ) + 1) ^ 4 := by
    push_cast
    ring
  linarith

theorem main_result_qubits (N : ℕ) :
    Fintype.card (Fin (2 ^ N)) = 2 ^ N ∧ Nat.log 2 (Fintype.card (Fin (2 ^ N))) = N :=
  ⟨register_dimension N, qubit_count N⟩

theorem main_result_total_cost (k N : ℕ) :
    pairingTotalSteps k N ≤ (k : ℚ) * 10 * ((N : ℚ) + 1) ^ 4 := by
  have h := pairingTotalSteps_le_budget k N
  unfold pairingStepBudget at h
  have hcast : ((10 * (N + 1) ^ 4 : ℕ) : ℚ) = 10 * ((N : ℚ) + 1) ^ 4 := by
    push_cast
    ring
  rw [hcast] at h
  calc pairingTotalSteps k N ≤ (k : ℚ) * (10 * ((N : ℚ) + 1) ^ 4) := h
    _ = (k : ℚ) * 10 * ((N : ℚ) + 1) ^ 4 := by ring

theorem main_result_budget_uniform : uniformUpperBound pairingStepBudget 10 4 :=
  pairingStepBudget_uniformUpperBound

theorem hundred_qubit_state_space : (10 : ℕ) ^ 29 < 2 ^ 100 := by
  norm_num

theorem state_space_ge_hundred (N : ℕ) (hN : 100 ≤ N) : (10 : ℕ) ^ 29 < 2 ^ N :=
  lt_of_lt_of_le hundred_qubit_state_space
    (pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hN)

theorem hundred_qubit_polynomial_vs_exponential :
    pairingStepBudget 100 < 10 ^ 29 ∧ (10 : ℕ) ^ 29 < 2 ^ 100 :=
  ⟨by norm_num [pairingStepBudget], hundred_qubit_state_space⟩

theorem main_result_summary (k N : ℕ) :
    Fintype.card (Fin (2 ^ N)) = 2 ^ N ∧
      Nat.log 2 (Fintype.card (Fin (2 ^ N))) = N ∧
      pairingTotalSteps k N ≤ (k : ℚ) * 10 * ((N : ℚ) + 1) ^ 4 ∧
      uniformUpperBound pairingStepBudget 10 4 :=
  ⟨register_dimension N, qubit_count N, main_result_total_cost k N,
    main_result_budget_uniform⟩

end Qatlib.Papers.PairingModel01.MainResults
