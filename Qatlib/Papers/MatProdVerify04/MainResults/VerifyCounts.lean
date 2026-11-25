/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Initialization, phase tests, and diffusion in Figure 1

Verify Once initializes the stored contractions in time `2kn + k²`.
Each phase test takes `n` time units and uses no queries. Each diffusion
update reads `2n` entries from each of `A` and `B`, and `4k` from `C`.
Keeping the counts separate also gives the resulting unit-cost time bound
for the listed initialization and loop stages.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MatProdVerify04.MainResults

/-- Across `ℓ` updates, the Figure 1 query budgets for each of `A`, `B`
and for `C` are bounded separately when `ℓ ≤ k ≤ n`. -/
theorem verify_update_queries_le {n k ℓ : ℕ} (hkn : k ≤ n) (hℓ : ℓ ≤ k) :
    ℓ * (2 * n) ≤ 2 * k * n ∧
    ℓ * (4 * k) ≤ 4 * k * n := by
  have hAB : ℓ * (2 * n) ≤ 2 * k * n := by
    rw [show 2 * k * n = k * (2 * n) by ring]
    exact Nat.mul_le_mul_right _ hℓ
  refine ⟨hAB, ?_⟩
  rw [show 4 * k * n = k * (4 * n) by ring]
  exact Nat.mul_le_mul hℓ (by omega)

/-- The Figure 1 initialization and repeated phase-test/diffusion stages
take at most `12kn` in the paper's unit-cost model. -/
theorem verify_listed_time_le {n k ℓ : ℕ} (hkn : k ≤ n) (hℓ : ℓ ≤ k) :
    2 * k * n + k * k + ℓ * (n + (2 * n + 2 * n + 4 * k)) ≤ 12 * k * n := by
  have hinit : k * k ≤ k * n := Nat.mul_le_mul_left _ hkn
  have hstep : n + (2 * n + 2 * n + 4 * k) ≤ 9 * n := by omega
  calc
    _ ≤ 2 * k * n + k * n + k * (9 * n) :=
      Nat.add_le_add (Nat.add_le_add_left hinit _) (Nat.mul_le_mul hℓ hstep)
    _ = _ := by ring

end Qatlib.Papers.MatProdVerify04.MainResults
