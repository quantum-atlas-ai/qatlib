/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MolEnergySim06.MainResults

def directQubits (n : ℕ) : ℕ := 2 * n

def compactQubits (configs : ℕ) : ℕ := Nat.clog 2 configs

theorem compactQubits_le_two_mul (n configs : ℕ) (h : configs ≤ 2 ^ (2 * n)) :
    compactQubits configs ≤ 2 * n := by
  unfold compactQubits
  exact Nat.clog_le_of_le_pow h

theorem mappings_linear_in_basis (n configs : ℕ) (h : configs ≤ 2 ^ (2 * n)) :
    compactQubits configs ≤ 2 * n ∧ directQubits n = 2 * n := by
  refine ⟨compactQubits_le_two_mul n configs h, rfl⟩

theorem compactQubits_le_direct (n configs : ℕ) (h : configs ≤ 2 ^ (2 * n)) :
    compactQubits configs ≤ directQubits n := by
  simpa [directQubits] using compactQubits_le_two_mul n configs h

def hamiltonianTerms (n : ℕ) : ℕ := n ^ 4

theorem hamiltonianTerms_le (n : ℕ) : hamiltonianTerms n ≤ (n + 1) ^ 4 := by
  unfold hamiltonianTerms
  exact Nat.pow_le_pow_left (Nat.le_succ n) 4

def gateUpperBound (n M : ℕ) : ℕ := 400 * M * (n + 1) ^ 4

theorem gates_bounded_polynomially (M : ℕ) (hM : 0 < M) :
    ∃ (c d : ℕ), 0 < c ∧ ∀ n : ℕ, gateUpperBound n M ≤ c * (n + 1) ^ d := by
  refine ⟨400 * M, 4, ?_, fun n => ?_⟩
  · exact Nat.mul_pos (by norm_num) hM
  · unfold gateUpperBound
    exact le_rfl

theorem gates_polynomial_in_qubits (q M : ℕ) :
    gateUpperBound (q / 2) M ≤ 400 * M * (q + 1) ^ 4 := by
  unfold gateUpperBound
  have h : q / 2 + 1 ≤ q + 1 := Nat.add_le_add_right (Nat.div_le_self q 2) 1
  exact Nat.mul_le_mul_left (400 * M) (Nat.pow_le_pow_left h 4)

theorem gates_with_linear_trotter (n : ℕ) :
    gateUpperBound n (n + 1) ≤ 400 * (n + 1) ^ 5 := by
  unfold gateUpperBound
  rw [show (n + 1) ^ 5 = (n + 1) ^ 4 * (n + 1) by rw [pow_succ]]
  have h : 400 * (n + 1) * (n + 1) ^ 4 = 400 * ((n + 1) ^ 4 * (n + 1)) := by ring
  rw [h]

end Qatlib.Papers.MolEnergySim06.MainResults
