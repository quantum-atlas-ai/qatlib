/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GroundStPrep17.MainResults.CostLedger

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 6 of arXiv:1712.03193v2 (fixed version v2, 2 Feb 2018)

*Combining the filtering method with phase estimation* (Appendix C,
eqs. (C38), (C39)).

(i) With a preliminary phase-estimation precision `Δ^κ` (`κ ∈ [0,1]`) the
filtering method achieves

`Õ(Λ/(χ³Δ^κ) + Λ/(χ Δ^{(3-κ)/2}) + Φ/(χ Δ^{(1-κ)/2}))`   (eq. (C38))

and the same number (C6) of qubits.

(ii) For `ξ = Õ(Δ)` the same argument as Corollary 2 gives

`Õ(Λ/(χ³ξ^κ) + Λ/(χ ξ^{(3-κ)/2}) + Φ/(χ Δ^{(1-κ)/2}))`   (eq. (C39))

and the same number (C37) of qubits.  Note that (C39) as printed in the paper
keeps `Δ` in the last term (the text says "the same argument as Corollary 2",
which suggests `ξ`; the ledger below is evaluated at `Δ := ξ`, so the printed
`Δ`-form is recovered from the monotonicity `Δ ≤ ξ` of the `ξ = Õ(Δ)` regime,
recorded as the explicit hypothesis `hΔξ`).

Both parts are formalised through `CostLedger.combinedGateCost` and the
filtering qubit ledgers; only resource statements are formal.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.GroundStPrep17.MainResults.PropositionSix

open Qatlib.Papers.GroundStPrep17.MainResults

/-- **Proposition 6(i), eq. (C38)**: gate complexity
`Õ(Λ/(χ³Δ^κ) + Λ/(χΔ^{(3-κ)/2}) + Φ/(χΔ^{(1-κ)/2}))`. -/
theorem proposition6_gateComplexity (N : ℕ) {Λ Φ Δ χ ε φ0 κ : ℝ}
    (hΛ : 0 < Λ) (hΦ : 0 < Φ) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hχ : 0 < χ) (hχ1 : χ ≤ 1) (hε : 0 < ε) (hφ0 : 0 < φ0)
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) :
    IsTildeO (combinedGateCost Λ Φ Δ χ κ)
      (Λ / (χ ^ 3 * Δ ^ κ) + Λ / (χ * Δ ^ ((3 - κ) / 2))
        + Φ / (χ * Δ ^ ((1 - κ) / 2)))
      (polylogScale N Δ ε φ0 χ) := by
  have h := combinedGateCost_le (N := N) hΛ hΦ hΔ hΔ1 hχ hχ1 hε hφ0 hκ0 hκ1
  have hexp : 0 ≤ (1 - κ) / 2 := by linarith
  have hΔe : Δ ^ ((1 - κ) / 2) ≤ 1 := by
    simpa using Real.rpow_le_rpow hΔ.le hΔ1 hexp
  have hΦχ : Φ / χ ≤ Φ / (χ * Δ ^ ((1 - κ) / 2)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hm : χ * Δ ^ ((1 - κ) / 2) ≤ χ * 1 := mul_le_mul_of_nonneg_left hΔe hχ.le
    nlinarith [hm, hΦ]
  have hA : 0 ≤ Λ / (χ ^ 3 * Δ ^ κ) := by positivity
  have hB : 0 ≤ Λ / (χ * Δ ^ ((3 - κ) / 2)) := by positivity
  have hC : 0 ≤ Φ / (χ * Δ ^ ((1 - κ) / 2)) := by positivity
  have hb : combinedBound Λ Φ Δ χ κ
      ≤ 2 * (Λ / (χ ^ 3 * Δ ^ κ) + Λ / (χ * Δ ^ ((3 - κ) / 2))
        + Φ / (χ * Δ ^ ((1 - κ) / 2))) := by
    unfold combinedBound phaseEstimationPriorBound
    linarith [hΦχ, hA, hB, hC]
  exact IsTildeO_mono_bound (bound' := Λ / (χ ^ 3 * Δ ^ κ) + Λ / (χ * Δ ^ ((3 - κ) / 2))
        + Φ / (χ * Δ ^ ((1 - κ) / 2))) (K := 2)
    (polylogScale_nonneg N hΔ hε hφ0 hχ) h hb (by norm_num)

/-- **Proposition 6(i), qubit count**: the same number (C6) of qubits. -/
theorem proposition6_qubitComplexity (N : ℕ) {χ ε Δ : ℝ}
    (hχ : 0 < χ) (hε : 0 < ε) (hχε : χ * ε ≤ 1)
    (hL : Real.exp 1 ≤ Real.log (1 / (χ * ε))) (hΔ : 0 < Δ) :
    IsBigO (filteringQubitLedger N χ ε Δ + 1) (filteringQubitLedger N χ ε Δ) :=
  filteringQubitLedger_bigO N hχ hε hχε hL hΔ

/-- **Proposition 6(ii), eq. (C39)**: gate complexity
`Õ(Λ/(χ³ξ^κ) + Λ/(χξ^{(3-κ)/2}) + Φ/(χΔ^{(1-κ)/2}))` in the regime `Δ ≤ ξ`. -/
theorem proposition6_gateComplexity_xi (N : ℕ) {Λ Φ Δ ξ χ ε φ0 κ : ℝ}
    (hΛ : 0 < Λ) (hΦ : 0 < Φ) (hΔ : 0 < Δ) (hΔξ : Δ ≤ ξ) (hξ1 : ξ ≤ 1)
    (hχ : 0 < χ) (hχ1 : χ ≤ 1) (hε : 0 < ε) (hφ0 : 0 < φ0)
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) :
    IsTildeO (combinedGateCost Λ Φ ξ χ κ)
      (Λ / (χ ^ 3 * ξ ^ κ) + Λ / (χ * ξ ^ ((3 - κ) / 2))
        + Φ / (χ * Δ ^ ((1 - κ) / 2)))
      (polylogScale N ξ ε φ0 χ) := by
  have hξ0 : 0 < ξ := lt_of_lt_of_le hΔ hΔξ
  have h := combinedGateCost_le (N := N) (Δ := ξ) hΛ hΦ hξ0 hξ1 hχ hχ1 hε hφ0 hκ0 hκ1
  have hexp : 0 ≤ (1 - κ) / 2 := by linarith
  have hpow : Δ ^ ((1 - κ) / 2) ≤ ξ ^ ((1 - κ) / 2) :=
    Real.rpow_le_rpow hΔ.le hΔξ hexp
  have hΔ1 : Δ ≤ 1 := le_trans hΔξ hξ1
  have hΔe : Δ ^ ((1 - κ) / 2) ≤ 1 := by
    simpa using Real.rpow_le_rpow hΔ.le hΔ1 hexp
  have hΦχ : Φ / χ ≤ Φ / (χ * Δ ^ ((1 - κ) / 2)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hm : χ * Δ ^ ((1 - κ) / 2) ≤ χ * 1 := mul_le_mul_of_nonneg_left hΔe hχ.le
    nlinarith [hm, hΦ]
  have hthird : Φ / (χ * ξ ^ ((1 - κ) / 2)) ≤ Φ / (χ * Δ ^ ((1 - κ) / 2)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : χ * Δ ^ ((1 - κ) / 2) ≤ χ * ξ ^ ((1 - κ) / 2) :=
      mul_le_mul_of_nonneg_left hpow hχ.le
    nlinarith [h1, hΦ]
  have hA : 0 ≤ Λ / (χ ^ 3 * ξ ^ κ) := by positivity
  have hB : 0 ≤ Λ / (χ * ξ ^ ((3 - κ) / 2)) := by positivity
  have hC : 0 ≤ Φ / (χ * Δ ^ ((1 - κ) / 2)) := by positivity
  have hb : combinedBound Λ Φ ξ χ κ
      ≤ 2 * (Λ / (χ ^ 3 * ξ ^ κ) + Λ / (χ * ξ ^ ((3 - κ) / 2))
        + Φ / (χ * Δ ^ ((1 - κ) / 2))) := by
    unfold combinedBound phaseEstimationPriorBound
    linarith [hΦχ, hthird, hA, hB, hC]
  exact IsTildeO_mono_bound (bound' := Λ / (χ ^ 3 * ξ ^ κ) + Λ / (χ * ξ ^ ((3 - κ) / 2))
        + Φ / (χ * Δ ^ ((1 - κ) / 2))) (K := 2)
    (polylogScale_nonneg N hξ0 hε hφ0 hχ) h hb (by norm_num)

/-- **Proposition 6(ii), qubit count**: the same number (C37) of qubits. -/
theorem proposition6_qubitComplexity_xi (N : ℕ) {χ ξ : ℝ}
    (hχ : 0 < χ) (hχ1 : χ ≤ 1) (hξ : 0 < ξ)
    (hL : Real.exp 1 ≤ Real.log (χ⁻¹)) :
    IsBigO (filteringQubitXiLedger N χ ξ + 1) (filteringQubitXiLedger N χ ξ) :=
  filteringQubitXiLedger_bigO N hχ hχ1 hξ hL

end Qatlib.Papers.GroundStPrep17.MainResults.PropositionSix
