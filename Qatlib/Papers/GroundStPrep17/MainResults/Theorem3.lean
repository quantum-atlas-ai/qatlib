/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GroundStPrep17.MainResults.CostLedger

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 3 of arXiv:1712.03193v2 (fixed version v2, 2 Feb 2018)

*Combining the known- and unknown-energy approaches* (p. 3).

Choosing a preliminary phase-estimation precision `Δ^κ` (`κ ∈ [0,1]`) and then
running the minimum-label energy search on the resulting interval of size
`Δ^κ`, the paper obtains gate complexity

`Õ(Λ/(χ³Δ^κ) + Λ/(χ Δ^{(3-κ)/2}) + Φ/(χ Δ^{(1-κ)/2}))`   (eq. (4))

with the same qubit count (2).  Formalised as the ledger
`CostLedger.combinedGateCost` (prior phase estimation `(1/χ)(Λ/(χΔ^κ)+Φ)` plus
minimum-label search `(Λ/Δ+Φ)√(Δ^κ/Δ)/χ`); only resource statements are
formal.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.GroundStPrep17.MainResults.TheoremThree

open Qatlib.Papers.GroundStPrep17.MainResults

/-- **Theorem 3, eq. (4)**: gate complexity
`Õ(Λ/(χ³Δ^κ) + Λ/(χΔ^{(3-κ)/2}) + Φ/(χΔ^{(1-κ)/2}))`, `κ ∈ [0,1]`. -/
theorem theorem3_gateComplexity (N : ℕ) {Λ Φ Δ χ ε φ0 κ : ℝ}
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

/-- **Theorem 3, qubit count (2)**: same qubit count as Theorem 1. -/
theorem theorem3_qubitComplexity (N : ℕ) {Δ ε φ0 χ : ℝ}
    (hΔ : 0 < Δ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hφ0 : 0 < φ0)
    (hχ : 0 < χ) (hχ1 : χ ≤ 1) :
    IsTildeO (sectionIIIQubitCost N Δ ε χ) (paperQubitBound N Δ ε)
      (polylogScale N Δ ε φ0 χ) :=
  sectionIIIQubitCost_le N hΔ hε hε1 hφ0 hχ hχ1

end Qatlib.Papers.GroundStPrep17.MainResults.TheoremThree
