/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ResolventQPE24.MainResults.Prelude

set_option backward.isDefEq.respectTransparency false

/-!
# Main result for QERE: Theorem 4.9

Fixed source: arXiv:2410.04837v1 (Alase--Karuvade), §4, p. 26, Eq. (146).

`c021` = Theorem 4.9 (complexity of solving QERE): with
`δ ∈ Θ(ε_eig ε_st²/κ_S⁴)` the query count
`α_A K_δ(-iA)/δ · log(1/ε_st)` is of order
`α_A κ_S⁴ K_δ(-iA)/(ε_eig ε_st²) · log(1/ε_st)`.  Circuit synthesis and the
state-accuracy analysis are not formalised; the query ledger is.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.ResolventQPE24.MainResults.Real

open Qatlib.Papers.ResolventQPE24.MainResults.Prelude

/-- **c021 — Theorem 4.9 (complexity of solving QERE), p. 26, Eq. (146).**
There is a constant `C` such that for every `ε_st ∈ (0,1]` one can choose
`δ ∈ Θ(ε_eig ε_st²/κ_S⁴)` for which the QERE query count
`α_A K_δ(-iA)/δ · log(1/ε_st)` is bounded by
`C · α_A κ_S⁴ K_δ(-iA)/(ε_eig ε_st²) · log(1/ε_st)`. -/
theorem theorem4_9_query_complexity
    (αA κS Kδ εeig : ℝ) (hαA : 0 < αA) (hκS : 0 < κS) (hKδ : 0 ≤ Kδ)
    (hεeig : 0 < εeig) :
    ∃ C : ℝ, 0 < C ∧ ∀ εst : ℝ, 0 < εst → εst ≤ 1 →
      ∃ δ : ℝ, 0 < δ ∧
        (εeig * εst ^ 2 / κS ^ 4) / C ≤ δ ∧
        δ ≤ C * (εeig * εst ^ 2 / κS ^ 4) ∧
        αA * Kδ / δ * Real.log (1 / εst) ≤ C * qereQueryBound αA κS Kδ εeig εst := by
  refine ⟨2, by norm_num, ?_⟩
  intro εst hεst hεst1
  have hx0 : 0 < εeig * εst ^ 2 / κS ^ 4 := by positivity
  refine ⟨εeig * εst ^ 2 / κS ^ 4, hx0, ?_, ?_, ?_⟩
  · linarith
  · nlinarith
  · rw [qereQueryBound]
    have hlog : 0 ≤ Real.log (1 / εst) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hεst]
      linarith
    have hkl : 0 ≤ αA * κS ^ 4 * Kδ / (εeig * εst ^ 2) := by positivity
    have hcost : 0 ≤ αA * κS ^ 4 * Kδ / (εeig * εst ^ 2) * Real.log (1 / εst) :=
      mul_nonneg hkl hlog
    rw [show αA * Kδ / (εeig * εst ^ 2 / κS ^ 4) * Real.log (1 / εst) =
        αA * κS ^ 4 * Kδ / (εeig * εst ^ 2) * Real.log (1 / εst) by
      field_simp]
    linarith

end Qatlib.Papers.ResolventQPE24.MainResults.Real
