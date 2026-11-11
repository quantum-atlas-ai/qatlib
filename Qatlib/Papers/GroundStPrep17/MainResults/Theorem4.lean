/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GroundStPrep17.MainResults.CostLedger

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 4 of arXiv:1712.03193v2 (fixed version v2, 2 Feb 2018)

*Ground state preparation from an energy estimate with `ξ = Õ(Δ)`* (p. 3).

When the ground energy is known only to precision `ξ = Õ(Δ)`, the paper obtains
gate complexity

`Õ(Λ/(χ ξ^{3/2}) + Φ/(χ √ξ))`   (eq. (5))

and `O(log N + log ξ⁻¹)` qubits; alternatively, combining with phase estimation
as in Theorem 3,

`Õ(Λ/(χ³ξ^κ) + Λ/(χ ξ^{(3-κ)/2}) + Φ/(χ ξ^{(1-κ)/2}))`   (eq. (6))

with the same number of qubits.  Both are formalised through the ledgers of
`CostLedger` evaluated at `Δ := ξ`; only resource statements are formal.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.GroundStPrep17.MainResults.TheoremFour

open Qatlib.Papers.GroundStPrep17.MainResults

/-- **Theorem 4, eq. (5)**: gate complexity `Õ(Λ/(χ ξ^{3/2}) + Φ/(χ √ξ))`. -/
theorem theorem4_gateComplexity (N : ℕ) {Λ Φ ξ χ ε φ0 : ℝ}
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

/-- **Theorem 4, qubit count**: `O(log N + log ξ⁻¹)` qubits, i.e. the
estimation ledger. -/
theorem theorem4_qubitComplexity (N : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    IsBigO (estimationQubitLedger N ξ + 1) (estimationQubitLedger N ξ) :=
  estimationQubitLedger_bigO N hξ

/-- **Theorem 4, eq. (6)**: the combined gate complexity
`Õ(Λ/(χ³ξ^κ) + Λ/(χξ^{(3-κ)/2}) + Φ/(χξ^{(1-κ)/2}))`, `κ ∈ [0,1]`. -/
theorem theorem4_gateComplexity_combined (N : ℕ) {Λ Φ ξ χ ε φ0 κ : ℝ}
    (hΛ : 0 < Λ) (hΦ : 0 < Φ) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hχ : 0 < χ) (hχ1 : χ ≤ 1) (hε : 0 < ε) (hφ0 : 0 < φ0)
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) :
    IsTildeO (combinedGateCost Λ Φ ξ χ κ)
      (Λ / (χ ^ 3 * ξ ^ κ) + Λ / (χ * ξ ^ ((3 - κ) / 2))
        + Φ / (χ * ξ ^ ((1 - κ) / 2)))
      (polylogScale N ξ ε φ0 χ) := by
  have h := combinedGateCost_le (N := N) (Δ := ξ) hΛ hΦ hξ hξ1 hχ hχ1 hε hφ0 hκ0 hκ1
  have hexp : 0 ≤ (1 - κ) / 2 := by linarith
  have hξe : ξ ^ ((1 - κ) / 2) ≤ 1 := by
    simpa using Real.rpow_le_rpow hξ.le hξ1 hexp
  have hΦχ : Φ / χ ≤ Φ / (χ * ξ ^ ((1 - κ) / 2)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hm : χ * ξ ^ ((1 - κ) / 2) ≤ χ * 1 := mul_le_mul_of_nonneg_left hξe hχ.le
    nlinarith [hm, hΦ]
  have hA : 0 ≤ Λ / (χ ^ 3 * ξ ^ κ) := by positivity
  have hB : 0 ≤ Λ / (χ * ξ ^ ((3 - κ) / 2)) := by positivity
  have hC : 0 ≤ Φ / (χ * ξ ^ ((1 - κ) / 2)) := by positivity
  have hb : combinedBound Λ Φ ξ χ κ
      ≤ 2 * (Λ / (χ ^ 3 * ξ ^ κ) + Λ / (χ * ξ ^ ((3 - κ) / 2))
        + Φ / (χ * ξ ^ ((1 - κ) / 2))) := by
    unfold combinedBound phaseEstimationPriorBound
    linarith [hΦχ, hA, hB, hC]
  exact IsTildeO_mono_bound (bound' := Λ / (χ ^ 3 * ξ ^ κ) + Λ / (χ * ξ ^ ((3 - κ) / 2))
        + Φ / (χ * ξ ^ ((1 - κ) / 2))) (K := 2)
    (polylogScale_nonneg N hξ hε hφ0 hχ) h hb (by norm_num)

/-- **Theorem 4, eq. (6) qubit count**: same number of qubits as (5), i.e. the
estimation ledger. -/
theorem theorem4_qubitComplexity_combined (N : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    IsBigO (estimationQubitLedger N ξ + 1) (estimationQubitLedger N ξ) :=
  estimationQubitLedger_bigO N hξ

end Qatlib.Papers.GroundStPrep17.MainResults.TheoremFour
