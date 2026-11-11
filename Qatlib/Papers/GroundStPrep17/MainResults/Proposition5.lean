/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GroundStPrep17.MainResults.CostLedger

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 5 of arXiv:1712.03193v2 (fixed version v2, 2 Feb 2018)

*Filtering method with unknown ground energy* (Appendix C, eqs. (C21), (C6)).

Combining amplitude amplification (per Section IV) with the filtering method,
the ground state is prepared with gate complexity

`Õ(Λ/(χ Δ^{3/2}) + Φ/(χ √Δ))`   (eq. (C21))

and the same number (C6) of qubits as Proposition 4.  Formalised through
`CostLedger.unknownEnergyGateCost` and `filteringQubitLedger`.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.GroundStPrep17.MainResults.PropositionFive

open Qatlib.Papers.GroundStPrep17.MainResults

/-- **Proposition 5, eq. (C21)**: gate complexity `Õ(Λ/(χΔ^{3/2}) + Φ/(χ√Δ))`. -/
theorem proposition5_gateComplexity (N : ℕ) {Λ Φ Δ χ ε φ0 : ℝ}
    (hΛ : 0 < Λ) (hΦ : 0 < Φ) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hχ : 0 < χ) (hχ1 : χ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) (hφ0 : 0 < φ0) :
    IsTildeO (unknownEnergyGateCost Λ Φ Δ χ ε)
      (Λ / (χ * Δ ^ (3 / 2 : ℝ)) + Φ / (χ * Real.sqrt Δ))
      (polylogScale N Δ ε φ0 χ) := by
  have h := unknownEnergyGateCost_le (N := N) hΛ hΦ hΔ hΔ1 hχ hχ1 hε hε1 hφ0
  have heq : unknownEnergyBound Λ Φ Δ χ
      = Λ / (χ * Δ ^ (3 / 2 : ℝ)) + Φ / (χ * Real.sqrt Δ) := by
    unfold unknownEnergyBound
    rw [← mul_sqrt_eq_rpow hΔ]
  rwa [heq] at h

/-- **Proposition 5, qubit count**: same number (C6) of qubits. -/
theorem proposition5_qubitComplexity (N : ℕ) {χ ε Δ : ℝ}
    (hχ : 0 < χ) (hε : 0 < ε) (hχε : χ * ε ≤ 1)
    (hL : Real.exp 1 ≤ Real.log (1 / (χ * ε))) (hΔ : 0 < Δ) :
    IsBigO (filteringQubitLedger N χ ε Δ + 1) (filteringQubitLedger N χ ε Δ) :=
  filteringQubitLedger_bigO N hχ hε hχε hL hΔ

end Qatlib.Papers.GroundStPrep17.MainResults.PropositionFive
