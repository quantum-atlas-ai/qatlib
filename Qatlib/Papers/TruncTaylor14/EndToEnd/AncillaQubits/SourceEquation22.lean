/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.FactorialTaylor.FactorialTaylorSimulation

set_option backward.isDefEq.respectTransparency false

/-!
# Source Eq. (22) — ancilla qubit count

arXiv:1412.4687v1, p. 4, Eq. (22): the ancillary state
`|k⟩|ℓ₁⟩…|ℓ_k⟩` (`0 ≤ k ≤ K`, `1 ≤ ℓ_i ≤ L`) uses a unary `K`-qubit first
register plus `K` index registers of `log₂ L` qubits each, so

`K + K·log₂ L = O( log(L) · log(T/ε) / loglog(T/ε) )`.

Here `K` is `factorialTaylorCutoff m` (the native cutoff driven by the
precision parameter `m = Θ(log(T/ε))`, cf. Eq. (18)), and the shape bound
comes from the frozen rate `K·log₂ m ≤ C m`
(`factorial_taylor_native_cutoff_and_rate`).  The displayed expression is
stated up to an absolute constant and a threshold, with `log₂ L + 1`
instead of `log₂ L` so that the degenerate `L = 1` case is covered by the
same constant.

Frozen FQNs reused: `factorialTaylorCutoff`,
`factorial_taylor_native_cutoff_and_rate`; derived bound
`cutoff_rate`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TruncTaylor14.EndToEnd.AncillaQubits

open Qatlib.Concepts.CoherentSim.FactorialTaylor

/-- Ancilla qubit count of the Taylor-LCU program: `K` unary qubits for the
order register plus `K` registers of `⌈log₂ L⌉` qubits for the indices. -/
def ancillaQubits (K L : ℕ) : ℕ := K + K * Nat.clog 2 (max 1 L)


/-- The frozen native-cutoff rate, restated in divided form: the least `K`
with `(K+1)! ≥ 2^m` satisfies `K ≤ C m / log₂ m`. -/
private theorem cutoff_rate :
    ∃ C m₀ : ℕ, 0 < C ∧ 2 ≤ m₀ ∧ ∀ m ≥ m₀,
      (factorialTaylorCutoff m : ℝ) ≤
        C * (m : ℝ) / (Nat.log 2 m : ℝ) := by
  obtain ⟨C, m₀, hC, hm₀, hrate⟩ :=
    factorial_taylor_native_cutoff_and_rate.2
  refine ⟨C, max m₀ 2, hC, le_max_right _ _, ?_⟩
  intro m hm
  have hm0 : m₀ ≤ m := (le_max_left _ _).trans hm
  have hm2 : 2 ≤ m := (le_max_right _ _).trans hm
  have hlogpos : 0 < Nat.log 2 m := Nat.log_pos (by norm_num) hm2
  have hcast : (factorialTaylorCutoff m : ℝ) * (Nat.log 2 m : ℝ) ≤ C * (m : ℝ) := by
    exact_mod_cast hrate m hm0
  rw [le_div_iff₀ (by exact_mod_cast hlogpos)]
  exact hcast

/-- arXiv:1412.4687v1 Eq. (22), p. 4: the ancilla state of the truncated
Taylor construction needs `O(log(L)·log(T/ε)/loglog(T/ε))` qubits.  Stated
with the native cutoff of Eq. (18) and the precision parameter `m`. -/
theorem source_equation22 :
    ∃ C m₀ : ℕ, 0 < C ∧ 2 ≤ m₀ ∧ ∀ (L m : ℕ), m₀ ≤ m →
      (ancillaQubits (factorialTaylorCutoff m) L : ℝ) ≤
        C * ((Nat.clog 2 (max 1 L) : ℝ) + 1) * (m : ℝ) / (Nat.log 2 m : ℝ) := by
  obtain ⟨D, n₀, hD, hn₀, hrate⟩ :=
    cutoff_rate
  refine ⟨D, max n₀ 2, hD, le_max_right _ _, ?_⟩
  intro L m hm
  have hm0 : n₀ ≤ m := (le_max_left _ _).trans hm
  have hm2 : 2 ≤ m := (le_max_right _ _).trans hm
  have hK := hrate m hm0
  have hc : (0 : ℝ) ≤ (Nat.clog 2 (max 1 L) : ℝ) + 1 := by positivity
  have hcast : (ancillaQubits (factorialTaylorCutoff m) L : ℝ) =
      (factorialTaylorCutoff m : ℝ) * ((Nat.clog 2 (max 1 L) : ℝ) + 1) := by
    unfold ancillaQubits
    push_cast
    ring
  rw [hcast]
  calc (factorialTaylorCutoff m : ℝ) * ((Nat.clog 2 (max 1 L) : ℝ) + 1)
      ≤ (D * (m : ℝ) / (Nat.log 2 m : ℝ)) *
          ((Nat.clog 2 (max 1 L) : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hK hc
    _ = D * ((Nat.clog 2 (max 1 L) : ℝ) + 1) * (m : ℝ) /
          (Nat.log 2 m : ℝ) := by ring

end Qatlib.Papers.TruncTaylor14.EndToEnd.AncillaQubits
