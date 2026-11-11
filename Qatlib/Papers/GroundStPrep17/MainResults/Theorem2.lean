/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GroundStPrep17.MainResults.CostLedger

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 2 of arXiv:1712.03193v2 (fixed version v2, 2 Feb 2018)

*Ground state preparation with unknown ground energy* (p. 2).

Using amplitude amplification on the Section III construction, the paper obtains
gate complexity

`Õ(Λ/(χ Δ^{3/2}) + Φ/(χ √Δ))`   (eq. (3))

with the same qubit count (2) as Theorem 1.  The ledger formalised here is
`CostLedger.unknownEnergyGateCost`: `(Λ/Δ + Φ) · √L / χ` with
`L = Θ(Δ⁻¹ log(1/(χε)))` the number of LCU terms (eqs. (17), (22)); this is
exactly the amplitude-amplification cost quoted below eq. (3).  Only the
resource statements are formal; the state-preparation semantics is not
modelled.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.GroundStPrep17.MainResults.TheoremTwo

open Qatlib.Papers.GroundStPrep17.MainResults

/-- **Theorem 2, eq. (3)**: gate complexity `Õ(Λ/(χ Δ^{3/2}) + Φ/(χ √Δ))` of the
unknown-ground-energy preparation. -/
theorem theorem2_gateComplexity (N : ℕ) {Λ Φ Δ χ ε φ0 : ℝ}
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

/-- **Theorem 2, qubit count (2)**: the unknown-ground-energy preparation uses
the same number of qubits as Theorem 1. -/
theorem theorem2_qubitComplexity (N : ℕ) {Δ ε φ0 χ : ℝ}
    (hΔ : 0 < Δ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hφ0 : 0 < φ0)
    (hχ : 0 < χ) (hχ1 : χ ≤ 1) :
    IsTildeO (sectionIIIQubitCost N Δ ε χ) (paperQubitBound N Δ ε)
      (polylogScale N Δ ε φ0 χ) :=
  sectionIIIQubitCost_le N hΔ hε hε1 hφ0 hχ hχ1

end Qatlib.Papers.GroundStPrep17.MainResults.TheoremTwo
