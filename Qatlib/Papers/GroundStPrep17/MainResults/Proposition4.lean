/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GroundStPrep17.MainResults.CostLedger

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 4 of arXiv:1712.03193v2 (fixed version v2, 2 Feb 2018)

*Filtering method with known ground energy* (Appendix C, eqs. (C4)-(C6)).

If `λ₀` is known to precision

`O(Δ / √(log³(1/(|φ₀|ε)) · log log(1/(|φ₀|ε))))`   (eq. (C4)),

the filtering method prepares an `ε`-close ground state with gate complexity

`Õ(Λ/(|φ₀|Δ) + Φ/|φ₀|)`   (eq. (C5))

and

`O(log N + log(1/ε) + η · log(1/Δ))` qubits,
`η = log(1/(χε)) / log log(1/(χε))`   (eq. (C6)).

The gate ledger is `CostLedger.filteringGateCost = (η² k Λ + Φ)/|φ₀|`
(eqs. (C16)-(C19)); the qubit ledger is `filteringQubitLedger` (C6).
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.GroundStPrep17.MainResults.PropositionFour

open Qatlib.Papers.GroundStPrep17.MainResults

/-- The precision of eq. (C4):
`Δ / √(log³(1/(|φ₀|ε)) · log log(1/(|φ₀|ε)))`. -/
def filteringPrecision (Δ φ0 ε : ℝ) : ℝ :=
  Δ / Real.sqrt (Real.log (1 / (φ0 * ε)) ^ 3 * Real.log (Real.log (1 / (φ0 * ε))))

/-- Positivity of the precision (C4) in the regime `log(1/(|φ₀|ε)) ≥ e`. -/
lemma filteringPrecision_pos {Δ φ0 ε : ℝ} (hΔ : 0 < Δ) (hφ0 : 0 < φ0) (hε : 0 < ε)
    (hL : Real.exp 1 ≤ Real.log (1 / (φ0 * ε))) :
    0 < filteringPrecision Δ φ0 ε := by
  have h1 : 0 < Real.log (1 / (φ0 * ε)) := by linarith [Real.exp_pos 1]
  have h2 : 1 ≤ Real.log (Real.log (1 / (φ0 * ε))) := by
    have h := Real.log_le_log (Real.exp_pos 1) hL
    rwa [Real.log_exp] at h
  have h3 : 0 < Real.log (1 / (φ0 * ε)) ^ 3 * Real.log (Real.log (1 / (φ0 * ε))) := by
    positivity
  unfold filteringPrecision
  exact div_pos hΔ (Real.sqrt_pos.mpr h3)

/-- **Proposition 4, eq. (C5)**: gate complexity `Õ(Λ/(|φ₀|Δ) + Φ/|φ₀|)`. -/
theorem proposition4_gateComplexity (N : ℕ) {Λ Φ Δ χ ε φ0 : ℝ}
    (hΛ : 0 < Λ) (hΦ : 0 < Φ) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hχ : 0 < χ) (hχ1 : χ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) (hφ0 : 0 < φ0)
    (hχε : χ * ε ≤ 1) (hL : Real.exp 1 ≤ Real.log (1 / (χ * ε)))
    (_hprec : 0 < filteringPrecision Δ φ0 ε) :
    IsTildeO (filteringGateCost Λ Φ φ0 χ ε Δ)
      (Λ / (φ0 * Δ) + Φ / φ0) (polylogScale N Δ ε φ0 χ) :=
  filteringGateCost_le N hΛ hΦ hΔ hΔ1 hχ hχ1 hε hε1 hφ0 hχε hL

/-- **Proposition 4, eq. (C6)**: the qubit ledger `log N + log 1/ε + η log 1/Δ`
is `O` of itself with the flag qubit. -/
theorem proposition4_qubitComplexity (N : ℕ) {χ ε Δ : ℝ}
    (hχ : 0 < χ) (hε : 0 < ε) (hχε : χ * ε ≤ 1)
    (hL : Real.exp 1 ≤ Real.log (1 / (χ * ε))) (hΔ : 0 < Δ) :
    IsBigO (filteringQubitLedger N χ ε Δ + 1) (filteringQubitLedger N χ ε Δ) :=
  filteringQubitLedger_bigO N hχ hε hχε hL hΔ

end Qatlib.Papers.GroundStPrep17.MainResults.PropositionFour
