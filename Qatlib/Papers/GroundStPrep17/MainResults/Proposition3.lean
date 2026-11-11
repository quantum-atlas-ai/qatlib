/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GroundStPrep17.MainResults.CostLedger

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 3 of arXiv:1712.03193v2 (fixed version v2, 2 Feb 2018)

*Ground state preparation with phase estimation for known ground energy*
(Appendix B, pp. 13-17).

If `λ₀` is known to precision `O(|φ₀| ε Δ)`, phase estimation prepares an
`ε`-close ground state in gate complexity

`O(Λ/(|φ₀|² Δ ε) + Φ/|φ₀|)`   (eq. (B1))

using `O(log N + log 1/ε + log 1/Δ)` qubits.  The ledger formalised is
`CostLedger.knownEnergyPEGateCost`: `1/|φ₀|` runs of phase estimation at
precision `|φ₀|εΔ` (eq. (B8)); only resource statements are formal.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.GroundStPrep17.MainResults.PropositionThree

open Qatlib.Papers.GroundStPrep17.MainResults

/-- The precision `O(|φ₀| ε Δ)` to which `λ₀` must be known (Prop. 3 / eq. (B7)). -/
def knownEnergyPrecision (φ0 Δ ε : ℝ) : ℝ := φ0 * Δ * ε

/-- The known-energy precision is positive for positive input parameters. -/
lemma knownEnergyPrecision_pos {φ0 Δ ε : ℝ} (hφ0 : 0 < φ0) (hΔ : 0 < Δ) (hε : 0 < ε) :
    0 < knownEnergyPrecision φ0 Δ ε := by
  unfold knownEnergyPrecision
  positivity

/-- **Proposition 3, eq. (B1)**: gate complexity
`O(Λ/(|φ₀|²Δε) + Φ/|φ₀|)`. -/
theorem proposition3_gateComplexity (N : ℕ) {Λ Φ Δ ε φ0 χ : ℝ}
    (hΛ : 0 < Λ) (hΦ : 0 < Φ) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hφ0 : 0 < φ0) (hχ : 0 < χ) (hε1 : ε ≤ 1) (hφ01 : φ0 ≤ 1) :
    IsTildeO (knownEnergyPEGateCost Λ Φ φ0 Δ ε)
      (Λ / (φ0 ^ 2 * Δ * ε) + Φ / φ0) (polylogScale N Δ ε φ0 χ) :=
  knownEnergyPEGateCost_le N hΛ hΦ hΔ hε hφ0 hχ hε1 hφ01

/-- **Proposition 3, qubit count**: `O(log N + log 1/ε + log 1/Δ)` qubits. -/
theorem proposition3_qubitComplexity (N : ℕ) {ε Δ : ℝ} (hε : 0 < ε) (hΔ : 0 < Δ) :
    IsBigO (prepQubitLedger N ε Δ + 1) (prepQubitLedger N ε Δ) :=
  prepQubitLedger_bigO N hε hΔ

end Qatlib.Papers.GroundStPrep17.MainResults.PropositionThree
