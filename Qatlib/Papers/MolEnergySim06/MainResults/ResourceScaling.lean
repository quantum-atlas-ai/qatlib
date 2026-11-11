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

/-!
# Register and polynomial gate-count models

This module defines direct and compact register-size models and elementary polynomial resource
bounds for the molecular simulation setting of [AspuruGuzikEtAl2005]. `compactQubits` is the
binary ceiling logarithm of the configuration count, while `directQubits n` is `2 * n`.

The gate-count model `gateUpperBound` is quartic in the basis parameter for a fixed positive
step count and becomes quintic when that count is chosen linearly.

## Main statements

* `mappings_linear_in_basis`: Bound compact and direct encodings using the configuration-count
  hypothesis.
* `gates_bounded_polynomially`: The modeled gate count has a polynomial bound for fixed positive
  step count.
* `gates_with_linear_trotter`: A linear step count gives a quintic model bound.

## References

* [Aspuru-Guzik et al., 2005][AspuruGuzikEtAl2005]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MolEnergySim06.MainResults

/-- The direct-encoding qubit-count model `2 * n`. -/
def directQubits (n : ℕ) : ℕ := 2 * n

/-- The compact-encoding qubit count given by the binary ceiling logarithm of the number of
configurations. -/
def compactQubits (configs : ℕ) : ℕ := Nat.clog 2 configs

/-- If there are at most `2^(2 * n)` configurations, their compact encoding uses at most `2 * n`
qubits; see [AspuruGuzikEtAl2005]. -/
theorem compactQubits_le_two_mul (n configs : ℕ) (h : configs ≤ 2 ^ (2 * n)) :
    compactQubits configs ≤ 2 * n := by
  unfold compactQubits
  exact Nat.clog_le_of_le_pow h

/-- Under the configuration-count hypothesis, the compact count is at most `2 * n` and the
direct count equals `2 * n`; see [AspuruGuzikEtAl2005]. -/
theorem mappings_linear_in_basis (n configs : ℕ) (h : configs ≤ 2 ^ (2 * n)) :
    compactQubits configs ≤ 2 * n ∧ directQubits n = 2 * n := by
  refine ⟨compactQubits_le_two_mul n configs h, rfl⟩

/-- Under the configuration-count hypothesis, the compact qubit-count model is at most the
direct count. -/
theorem compactQubits_le_direct (n configs : ℕ) (h : configs ≤ 2 ^ (2 * n)) :
    compactQubits configs ≤ directQubits n := by
  simpa [directQubits] using compactQubits_le_two_mul n configs h

/-- The quartic Hamiltonian term-count model `n^4`. -/
def hamiltonianTerms (n : ℕ) : ℕ := n ^ 4

/-- The modeled Hamiltonian term count is at most `(n + 1)^4`; see [AspuruGuzikEtAl2005]. -/
theorem hamiltonianTerms_le (n : ℕ) : hamiltonianTerms n ≤ (n + 1) ^ 4 := by
  unfold hamiltonianTerms
  exact Nat.pow_le_pow_left (Nat.le_succ n) 4

/-- The gate-count model `400 * M * (n + 1)^4` for basis parameter `n` and step count `M`. -/
def gateUpperBound (n M : ℕ) : ℕ := 400 * M * (n + 1) ^ 4

/-- For fixed positive `M`, the modeled gate count is bounded by `c * (n + 1)^d` for some
positive natural coefficient `c` and natural exponent `d`; see [AspuruGuzikEtAl2005]. -/
theorem gates_bounded_polynomially (M : ℕ) (hM : 0 < M) :
    ∃ (c d : ℕ), 0 < c ∧ ∀ n : ℕ, gateUpperBound n M ≤ c * (n + 1) ^ d := by
  refine ⟨400 * M, 4, ?_, fun n => ?_⟩
  · exact Nat.mul_pos (by norm_num) hM
  · unfold gateUpperBound
    exact le_rfl

/-- Replacing the basis parameter by `q / 2` bounds the modeled gate count by `400 * M * (q +
1)^4`; see [AspuruGuzikEtAl2005]. -/
theorem gates_polynomial_in_qubits (q M : ℕ) :
    gateUpperBound (q / 2) M ≤ 400 * M * (q + 1) ^ 4 := by
  unfold gateUpperBound
  have h : q / 2 + 1 ≤ q + 1 := Nat.add_le_add_right (Nat.div_le_self q 2) 1
  exact Nat.mul_le_mul_left (400 * M) (Nat.pow_le_pow_left h 4)

/-- Choosing `M = n + 1` bounds the modeled gate count by `400 * (n + 1)^5`; see
[AspuruGuzikEtAl2005]. -/
theorem gates_with_linear_trotter (n : ℕ) :
    gateUpperBound n (n + 1) ≤ 400 * (n + 1) ^ 5 := by
  unfold gateUpperBound
  rw [show (n + 1) ^ 5 = (n + 1) ^ 4 * (n + 1) by rw [pow_succ]]
  have h : 400 * (n + 1) * (n + 1) ^ 4 = 400 * ((n + 1) ^ 4 * (n + 1)) := by ring
  rw [h]

end Qatlib.Papers.MolEnergySim06.MainResults
