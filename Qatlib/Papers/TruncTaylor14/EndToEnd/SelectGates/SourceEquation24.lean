/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.FactorialTaylor.FactorialTaylorSimulation

set_option backward.isDefEq.respectTransparency false

/-!
# Source Eq. (24) — gate cost of `select(V)`

arXiv:1412.4687v1, p. 4, Eq. (24).  One controlled-`select(H)` is built from
`O(log L)`-gate generalised Toffoli gates and an `n`-qubit controlled Pauli
tensor product, so each costs `O(L(n+log L))`; there are `K` of them:

`K·L·(n+log₂L) = O( L(n+log L) · log(T/ε) / loglog(T/ε) )`.

The order bound uses the frozen native-cutoff rate (cf. Eq. (18)) with
`m = Θ(log(T/ε))`.

Frozen FQNs reused: `factorialTaylorCutoff`,
`factorial_taylor_native_cutoff_and_rate` (restated locally
as `cutoff_rate`).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TruncTaylor14.EndToEnd.SelectGates

open Qatlib.Concepts.CoherentSim.FactorialTaylor

/-- Gate cost of `select(V)`: `K` controlled-selects, each costing
`L·(n + ⌈log₂ L⌉)` gates. -/
def selectGates (K L n : ℕ) : ℕ := K * L * (n + Nat.clog 2 (max 1 L))


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

/-- arXiv:1412.4687v1 Eq. (24), p. 4: `select(V)` costs
`O(L(n+log L)·log(T/ε)/loglog(T/ε))` elementary gates. -/
theorem source_equation24 :
    ∃ C m₀ : ℕ, 0 < C ∧ 2 ≤ m₀ ∧ ∀ (L n m : ℕ), m₀ ≤ m →
      (selectGates (factorialTaylorCutoff m) L n : ℝ) ≤
        C * (L : ℝ) * ((n : ℝ) + (Nat.clog 2 (max 1 L) : ℝ)) * (m : ℝ) /
          (Nat.log 2 m : ℝ) := by
  obtain ⟨D, n₀, hD, hn₀, hrate⟩ :=
    cutoff_rate
  refine ⟨D, max n₀ 2, hD, le_max_right _ _, ?_⟩
  intro L n m hm
  have hm0 : n₀ ≤ m := (le_max_left _ _).trans hm
  have hK := hrate m hm0
  have hcast : (selectGates (factorialTaylorCutoff m) L n : ℝ) =
      (factorialTaylorCutoff m : ℝ) * (L : ℝ) *
        ((n : ℝ) + (Nat.clog 2 (max 1 L) : ℝ)) := by
    unfold selectGates
    push_cast
    ring
  rw [hcast]
  calc (factorialTaylorCutoff m : ℝ) * (L : ℝ) *
          ((n : ℝ) + (Nat.clog 2 (max 1 L) : ℝ))
      ≤ (D * (m : ℝ) / (Nat.log 2 m : ℝ)) * (L : ℝ) *
          ((n : ℝ) + (Nat.clog 2 (max 1 L) : ℝ)) := by
        have hc : (0 : ℝ) ≤ (L : ℝ) * ((n : ℝ) + (Nat.clog 2 (max 1 L) : ℝ)) := by
          positivity
        nlinarith [mul_le_mul_of_nonneg_right hK hc]
    _ = D * (L : ℝ) * ((n : ℝ) + (Nat.clog 2 (max 1 L) : ℝ)) * (m : ℝ) /
          (Nat.log 2 m : ℝ) := by ring

end Qatlib.Papers.TruncTaylor14.EndToEnd.SelectGates
