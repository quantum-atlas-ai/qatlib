/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.FactorialTaylor.FactorialTaylorSimulation

set_option backward.isDefEq.respectTransparency false

/-!
# Source Eq. (23) — gate cost of `B`

arXiv:1412.4687v1, p. 3–4, Eq. (23).  `B` is a tensor product over the
`K + 1` registers: the first factor prepares
`Σ_{k=0}^K √(t^k/k!) |1^k 0^{K-k}⟩` in `O(K)` gates (one rotation plus
`K-1` controlled rotations), and each of the other `K` factors prepares
`Σ_ℓ √α_ℓ |ℓ⟩` in `O(L)` gates.  Total

`K + K·L = O( L · log(T/ε) / loglog(T/ε) )`.

The order bound is obtained from the frozen rate for the native cutoff
(`factorialTaylorCutoff m`, `m = Θ(log(T/ε))`), exactly as in Eq. (22).
The `K` term is absorbed using `L ≥ 1` (i.e. `K ≤ K·L`).

Frozen FQNs reused: `factorialTaylorCutoff`,
`factorial_taylor_native_cutoff_and_rate` (restated locally
as `cutoff_rate`).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TruncTaylor14.EndToEnd.PrepareGates

open Qatlib.Concepts.CoherentSim.FactorialTaylor

/-- Gate cost of the preparation unitary `B`: `K` gates for the order
register plus `L` gates for each of the `K` index registers. -/
def prepareGates (K L : ℕ) : ℕ := K + K * L


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

/-- arXiv:1412.4687v1 Eq. (23), p. 4: the preparation `B` costs
`O(L·log(T/ε)/loglog(T/ε))` elementary gates. -/
theorem source_equation23 :
    ∃ C m₀ : ℕ, 0 < C ∧ 2 ≤ m₀ ∧ ∀ (L m : ℕ), 1 ≤ L → m₀ ≤ m →
      (prepareGates (factorialTaylorCutoff m) L : ℝ) ≤
        C * (L : ℝ) * (m : ℝ) / (Nat.log 2 m : ℝ) := by
  obtain ⟨D, n₀, hD, hn₀, hrate⟩ :=
    cutoff_rate
  refine ⟨2 * D, max n₀ 2, by positivity, le_max_right _ _, ?_⟩
  intro L m hL hm
  have hm0 : n₀ ≤ m := (le_max_left _ _).trans hm
  have hK := hrate m hm0
  have hcast : (prepareGates (factorialTaylorCutoff m) L : ℝ) =
      (factorialTaylorCutoff m : ℝ) * ((L : ℝ) + 1) := by
    unfold prepareGates
    push_cast
    ring
  rw [hcast]
  have hstep : (factorialTaylorCutoff m : ℝ) * ((L : ℝ) + 1) ≤
      (D * (m : ℝ) / (Nat.log 2 m : ℝ)) * ((L : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right hK (by positivity)
  have h2 : (L : ℝ) + 1 ≤ 2 * (L : ℝ) := by
    have : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    linarith
  have hstep2 : (D * (m : ℝ) / (Nat.log 2 m : ℝ)) * ((L : ℝ) + 1) ≤
      (D * (m : ℝ) / (Nat.log 2 m : ℝ)) * (2 * (L : ℝ)) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have hfinal : (D * (m : ℝ) / (Nat.log 2 m : ℝ)) * (2 * (L : ℝ)) =
      (2 * D : ℕ) * (L : ℝ) * (m : ℝ) / (Nat.log 2 m : ℝ) := by
    push_cast
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  exact hstep.trans (hstep2.trans (le_of_eq hfinal))

end Qatlib.Papers.TruncTaylor14.EndToEnd.PrepareGates
