/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GroundStPrep17.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 1 of arXiv:1712.03193v2 (Ge, Tura, Cirac; fixed version v2, 2 Feb 2018)

*Ground state preparation with known ground energy* (p. 2).

The paper assumes `λ₀` is known to precision `O(Δ / log(1/(χε)))` and gives a
procedure preparing an `ε`-close ground state with constant success probability,
using

* `Õ(Λ/(|φ₀|Δ) + Φ/|φ₀|)` gates (eq. (1)),
* `O(log N + log log(1/ε) + log(1/Δ))` qubits (eq. (2)), including one flag
  qubit whose measurement outcome indicates success.

The formal statements below are the quantitative content: the gate ledger of the
Section III construction (`SourceModel.sectionIIIGateCost`, eq. (28) with the
substitutions (17), (22)) is `Õ` of the displayed bound, the qubit ledger is
`O` of the displayed qubit bound, and the flag qubit is the explicit additive
`+1` of the qubit ledger.  The state-preparation semantics itself (`ε`-closeness,
success probability, the flag readout) is not modelled, as no quantum-circuit
framework is used for this paper layer; only the resource statements are formal.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.GroundStPrep17.MainResults.TheoremOne

open Qatlib.Papers.GroundStPrep17.MainResults

/-- Theorem 1 hypothesis (p. 2): the ground energy `λ₀` is known to precision
`O(Δ / log(1/(χε)))`, i.e. some estimate `λ₀'` satisfies
`|λ₀ - λ₀'| ≤ C Δ / log(1/(χε))`. -/
def groundEnergyKnownToPrecision (ground estimate Δ χ ε : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ |ground - estimate| ≤ C * (Δ / Real.log (1 / (χ * ε)))

/-- The qubit ledger of eq. (2) without its flag qubit. -/
def theorem1BaseQubitLedger (N : ℕ) (Δ ε χ : ℝ) : ℝ :=
  Real.log ((N : ℝ) + 2) + Real.log (Real.log (1 / (χ * ε)) + 2)
    + Real.log (Δ⁻¹ + 2)

/-- The flag qubit of Theorem 1: the full qubit ledger of eq. (2) is the
register/ancilla ledger plus exactly one flag qubit. -/
theorem theorem1_flagQubit (N : ℕ) (Δ ε χ : ℝ) :
    sectionIIIQubitCost N Δ ε χ = theorem1BaseQubitLedger N Δ ε χ + 1 := by
  unfold sectionIIIQubitCost theorem1BaseQubitLedger
  ring

/-- **Theorem 1, eq. (1)**: gate complexity `Õ(Λ/(|φ₀|Δ) + Φ/|φ₀|)` of the
known-ground-energy preparation. -/
theorem theorem1_gateComplexity (N : ℕ) {Λ Φ φ0 Δ ε χ : ℝ}
    (hΛ : 0 < Λ) (hΦ : 0 < Φ) (hφ0 : 0 < φ0)
    (hΔ : 0 < Δ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hχ : 0 < χ) (hχ1 : χ ≤ 1)
    (_hprec : ∃ ground estimate : ℝ, groundEnergyKnownToPrecision ground estimate Δ χ ε) :
    IsTildeO (sectionIIIGateCost N Λ Φ φ0 Δ ε χ)
      (Λ / (φ0 * Δ) + Φ / φ0) (polylogScale N Δ ε φ0 χ) :=
  sectionIIIGateCost_le N hΛ hΦ hφ0 hΔ hε hε1 hχ hχ1

/-- **Theorem 1, eq. (2)**: the known-ground-energy preparation uses
`O(log N + log log(1/ε) + log(1/Δ))` qubits. -/
theorem theorem1_qubitComplexity (N : ℕ) {Δ ε φ0 χ : ℝ}
    (hΔ : 0 < Δ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hφ0 : 0 < φ0)
    (hχ : 0 < χ) (hχ1 : χ ≤ 1) :
    IsTildeO (sectionIIIQubitCost N Δ ε χ) (paperQubitBound N Δ ε)
      (polylogScale N Δ ε φ0 χ) :=
  sectionIIIQubitCost_le N hΔ hε hε1 hφ0 hχ hχ1

end Qatlib.Papers.GroundStPrep17.MainResults.TheoremOne
