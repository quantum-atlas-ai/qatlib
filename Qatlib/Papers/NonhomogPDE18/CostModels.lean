/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic

set_option autoImplicit false

namespace Qatlib.Papers.NonhomogPDE18.CostModels

def modeledTermCount (N : ℕ) : ℕ := 1 + 4 * N

def modeledGateCount (N K : ℕ) : ℕ := K * modeledTermCount N

theorem modeledGateCount_eq (N K : ℕ) :
    modeledGateCount N K = K * (4 * N + 1) := by
  unfold modeledGateCount modeledTermCount
  ring

theorem modeled_linear_bound (N K : ℕ) :
    modeledGateCount N K ≤ (5 * K) * (N + 1) := by
  rw [modeledGateCount_eq]
  have h1 : 4 * N + 1 ≤ 5 * (N + 1) := by omega
  calc
    K * (4 * N + 1) ≤ K * (5 * (N + 1)) := Nat.mul_le_mul_left K h1
    _ = (5 * K) * (N + 1) := by ring

theorem modeled_polynomial_dimension (K : ℕ) :
    ∃ c k : ℕ, ∀ N : ℕ, modeledGateCount N K ≤ c * (N + 1) ^ k := by
  refine ⟨5 * K, 1, fun N => ?_⟩
  rw [pow_one]
  exact modeled_linear_bound N K

end Qatlib.Papers.NonhomogPDE18.CostModels
