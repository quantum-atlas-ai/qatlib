/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GroundStPrep17.MainResults.CostLedger

set_option backward.isDefEq.respectTransparency false

/-!
# Corollary 2 of arXiv:1712.03193v2 (fixed version v2, 2 Feb 2018)

*Filtering method from an energy estimate with `ξ = Õ(Δ)`* (Appendix C,
eqs. (C36), (C37)).

With the ground energy known to precision `ξ = Õ(Δ)`, the filtering method
prepares the ground state with gate complexity

`Õ(Λ/(χ ξ^{3/2}) + Φ/(χ √ξ))`   (eq. (C36))

and

`O(log N + (log(1/χ)/log log(1/χ)) · log(1/ξ))` qubits   (eq. (C37)).

Formalised through `CostLedger.unknownEnergyGateCost` evaluated at `Δ := ξ`
and `filteringQubitXiLedger`.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.GroundStPrep17.MainResults.CorollaryTwo

open Qatlib.Papers.GroundStPrep17.MainResults

/-- **Corollary 2, eq. (C36)**: gate complexity `Õ(Λ/(χξ^{3/2}) + Φ/(χ√ξ))`. -/
theorem corollary2_gateComplexity (N : ℕ) {Λ Φ ξ χ ε φ0 : ℝ}
    (hΛ : 0 < Λ) (hΦ : 0 < Φ) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hχ : 0 < χ) (hχ1 : χ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) (hφ0 : 0 < φ0) :
    IsTildeO (unknownEnergyGateCost Λ Φ ξ χ ε)
      (Λ / (χ * ξ ^ (3 / 2 : ℝ)) + Φ / (χ * Real.sqrt ξ))
      (polylogScale N ξ ε φ0 χ) := by
  have h := unknownEnergyGateCost_le (N := N) (Δ := ξ) hΛ hΦ hξ hξ1 hχ hχ1 hε hε1 hφ0
  have heq : unknownEnergyBound Λ Φ ξ χ
      = Λ / (χ * ξ ^ (3 / 2 : ℝ)) + Φ / (χ * Real.sqrt ξ) := by
    unfold unknownEnergyBound
    rw [← mul_sqrt_eq_rpow hξ]
  rwa [heq] at h

/-- **Corollary 2, eq. (C37)**: the qubit ledger
`log N + (log χ⁻¹/log log χ⁻¹) log ξ⁻¹` is `O` of itself with the flag qubit. -/
theorem corollary2_qubitComplexity (N : ℕ) {χ ξ : ℝ}
    (hχ : 0 < χ) (hχ1 : χ ≤ 1) (hξ : 0 < ξ)
    (hL : Real.exp 1 ≤ Real.log (χ⁻¹)) :
    IsBigO (filteringQubitXiLedger N χ ξ + 1) (filteringQubitXiLedger N χ ξ) :=
  filteringQubitXiLedger_bigO N hχ hχ1 hξ hL

end Qatlib.Papers.GroundStPrep17.MainResults.CorollaryTwo
