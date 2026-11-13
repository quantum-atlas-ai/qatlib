/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.FactorialTaylor.FactorialTaylorSimulation

set_option backward.isDefEq.respectTransparency false

/-!
# Source Eq. (18) — the log/loglog truncation order

arXiv:1412.4687v1, p. 3, Eq. (18): the truncation order is
`K = O(log(T/ε) / log log(T/ε))` with `T = (Σ α_ℓ) t`.

The native search `factorialTaylorCutoff m` is the least `K` with
`(K+1)! ≥ 2^m`, and `factorial_taylor_native_cutoff_and_rate` proves the
integer rate `K · log₂ m ≤ C m` (its proof uses `C = 12`, `m₀ = 4`).
Dividing by `log₂ m` gives the source's order bound with some absolute
constant.  The program's precision parameter is
`m = factorialTaylorPrecision s k = 2(k + ⌈log₂ max 1 s⌉ + 8)`, which is
`Θ(log(T/ε))` for `k = Θ(log 1/ε)` and `s = Θ(T)`; the theorem is stated in
`m`, exactly as the cutoff is defined.

Library definitions and theorems:
`Qatlib.Concepts.CoherentSim.FactorialTaylor.factorialTaylorCutoff`,
`factorialTaylorPrecision`,
`factorial_taylor_native_cutoff_and_rate`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TruncTaylor14.FactorialTaylor.LogLogCutoff

open Qatlib.Concepts.CoherentSim.FactorialTaylor

/-- Eq. (18), p. 3: the native factorial cutoff is `O(m / log₂ m)`, with an
absolute constant and threshold. -/
theorem source_equation18 :
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

/-- The same order bound at the program's concrete precision parameter
`m = factorialTaylorPrecision s k`. -/
theorem source_equation18_precision :
    ∃ C m₀ : ℕ, 0 < C ∧ 2 ≤ m₀ ∧ ∀ s k : ℕ, m₀ ≤ factorialTaylorPrecision s k →
      (factorialTaylorCutoff (factorialTaylorPrecision s k) : ℝ) ≤
        C * (factorialTaylorPrecision s k : ℝ) /
          (Nat.log 2 (factorialTaylorPrecision s k) : ℝ) := by
  obtain ⟨C, m₀, hC, hm₀, h⟩ := source_equation18
  exact ⟨C, m₀, hC, hm₀, fun s k hk => h _ hk⟩

end Qatlib.Papers.TruncTaylor14.FactorialTaylor.LogLogCutoff
