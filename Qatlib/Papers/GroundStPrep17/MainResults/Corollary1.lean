/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GroundStPrep17.MainResults.CostLedger

set_option backward.isDefEq.respectTransparency false

/-!
# Corollary 1 of arXiv:1712.03193v2 (fixed version v2, 2 Feb 2018)

*Ground state preparation with phase estimation for unknown ground energy*
(Appendix B, eq. (B10)).

The ground energy is first estimated by phase estimation to precision
`ξ = O(χ ε Δ)` (eq. (B9)), which by Proposition 2 costs
`Õ(Λ/(χ⁴Δε) + Φ/χ)` gates; the preparation then uses the same
`O(log N + log 1/ε + log 1/Δ)` qubits as Proposition 3.  Formalised by
evaluating the Proposition 2 ledger `peRunCost` at `ξ = χ ε Δ`.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.GroundStPrep17.MainResults.CorollaryOne

open Qatlib.Papers.GroundStPrep17.MainResults

/-- **Corollary 1, eq. (B10)**: gate complexity `Õ(Λ/(χ⁴Δε) + Φ/χ)`. -/
theorem corollary1_gateComplexity (N : ℕ) {Λ Φ Δ χ ε φ0 : ℝ}
    (hΛ : 0 < Λ) (hΦ : 0 < Φ) (hΔ : 0 < Δ) (hχ : 0 < χ) (hχ1 : χ ≤ 1)
    (hε : 0 < ε) (hφ0 : 0 < φ0) :
    IsTildeO (peRunCost Λ Φ χ (χ * Δ * ε)) (Λ / (χ ^ 4 * Δ * ε) + Φ / χ)
      (polylogScale N Δ ε φ0 χ) := by
  have hξ : 0 < χ * Δ * ε := by positivity
  have h := peRunCost_le (N := N) (Δ := Δ) (ε := ε) (φ0 := φ0) (ξ := χ * Δ * ε)
    hΛ hΦ hΔ hχ hχ1 hε hφ0 hξ
  have heq : Λ / (χ ^ 3 * (χ * Δ * ε)) + Φ / χ = Λ / (χ ^ 4 * Δ * ε) + Φ / χ := by
    have hd : χ ^ 3 * (χ * Δ * ε) = χ ^ 4 * Δ * ε := by ring
    rw [hd]
  rwa [heq] at h

/-- **Corollary 1, qubit count**: same qubit count as Proposition 3,
`O(log N + log 1/ε + log 1/Δ)`. -/
theorem corollary1_qubitComplexity (N : ℕ) {ε Δ : ℝ} (hε : 0 < ε) (hΔ : 0 < Δ) :
    IsBigO (prepQubitLedger N ε Δ + 1) (prepQubitLedger N ε Δ) :=
  prepQubitLedger_bigO N hε hΔ

end Qatlib.Papers.GroundStPrep17.MainResults.CorollaryOne
