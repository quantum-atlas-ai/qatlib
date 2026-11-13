/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PairingModel01.MainResults.StepCount
import Qatlib.Papers.PairingModel01.MainResults.ShortTimeApproximation
import Qatlib.Papers.PairingModel01.MainResults.AdiabaticProduct

/-!
# Pairing-model register and resource bounds

The explicit step-count polynomial is bounded by a uniform quartic budget, and the
computational-basis register has dimension `2 ^ N`. These arithmetic resource statements
formalize the polynomial-versus-exponential comparison in [WuByrdLidar2002], including the
stated hundred-qubit example.

## Main statements

* `main_result_total_cost`: the `k`-step cost is bounded by `10 * k * (N + 1)^4`.
* `main_result_summary`: register dimension, qubit count, and uniform step-budget bounds are
  collected together.

## References

* [Wu et al., 2002][WuByrdLidar2002]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.PairingModel01.MainResults

open Qatlib.Concepts.ResourceBounds.AsymBounds

/-- There is a rational constant `C` such that `pairingStepCount N ≤ C * (N + 1)^4` for every
natural `N`. See [WuByrdLidar2002]. -/
theorem main_result_steps_polynomial :
    ∃ C : ℚ, ∀ N : ℕ, pairingStepCount N ≤ C * ((N : ℚ) + 1) ^ 4 := by
  refine ⟨10, fun N => ?_⟩
  have h := pairingStepCount_le_budget N
  unfold pairingStepBudget at h
  have hcast : ((10 * (N + 1) ^ 4 : ℕ) : ℚ) = 10 * ((N : ℚ) + 1) ^ 4 := by
    push_cast
    ring
  linarith

/-- The register has dimension `2 ^ N` and its base-two natural logarithm is `N`. See
[WuByrdLidar2002]. -/
theorem main_result_qubits (N : ℕ) :
    Fintype.card (Fin (2 ^ N)) = 2 ^ N ∧ Nat.log 2 (Fintype.card (Fin (2 ^ N))) = N :=
  ⟨register_dimension N, qubit_count N⟩

/-- The total cost of `k` pairing steps is at most `10 * k * (N + 1)^4`. See [WuByrdLidar2002]. -/
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

/-- The pairing step budget has uniform polynomial upper bound with coefficient ten and degree
four. See [WuByrdLidar2002]. -/
theorem main_result_budget_uniform : uniformUpperBound pairingStepBudget 10 4 :=
  pairingStepBudget_uniformUpperBound

/-- The state-space dimension `2 ^ 100` is greater than `10 ^ 29`. -/
theorem hundred_qubit_state_space : (10 : ℕ) ^ 29 < 2 ^ 100 := by
  norm_num

/-- For at least one hundred qubits, the state-space dimension is greater than `10 ^ 29`. -/
theorem state_space_ge_hundred (N : ℕ) (hN : 100 ≤ N) : (10 : ℕ) ^ 29 < 2 ^ N :=
  lt_of_lt_of_le hundred_qubit_state_space
    (pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hN)

/-- At one hundred qubits, the pairing step budget is less than `10 ^ 29`, while the state-space
dimension is greater than `10 ^ 29`. See [WuByrdLidar2002]. -/
theorem hundred_qubit_polynomial_vs_exponential :
    pairingStepBudget 100 < 10 ^ 29 ∧ (10 : ℕ) ^ 29 < 2 ^ 100 :=
  ⟨by norm_num [pairingStepBudget], hundred_qubit_state_space⟩

/-- The register has dimension `2 ^ N` and qubit count `N`, the `k`-step cost is at most `10 * k
* (N + 1)^4`, and the step budget has a uniform quartic upper bound. -/
theorem main_result_summary (k N : ℕ) :
    Fintype.card (Fin (2 ^ N)) = 2 ^ N ∧
      Nat.log 2 (Fintype.card (Fin (2 ^ N))) = N ∧
      pairingTotalSteps k N ≤ (k : ℚ) * 10 * ((N : ℚ) + 1) ^ 4 ∧
      uniformUpperBound pairingStepBudget 10 4 :=
  ⟨register_dimension N, qubit_count N, main_result_total_cost k N,
    main_result_budget_uniform⟩

end Qatlib.Papers.PairingModel01.MainResults
