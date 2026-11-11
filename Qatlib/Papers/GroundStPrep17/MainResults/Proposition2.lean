/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GroundStPrep17.MainResults.CostLedger

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 2 of arXiv:1712.03193v2 (fixed version v2, 2 Feb 2018)

*Phase-estimation energy estimation* (Appendix A, eq. (A1)).

Phase estimation determines `λ₀` to additive precision `ξ` in gate complexity

`Õ(Λ/(χ³ ξ) + Φ/χ)`   (eq. (A1))

and `O(log N + log 1/ξ)` qubits.  The ledger formalised is
`CostLedger.peRunCost`: `1/χ` runs of phase estimation, each of gate cost
`2^k Λ + Φ` with `2^k = 1/(χξ)`.  The precision (`AdditivePrecision`) and the
estimation semantics are recorded as predicates; only resource statements are
formal.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.GroundStPrep17.MainResults.PropositionTwo

open Qatlib.Papers.GroundStPrep17.MainResults

/-- Proposition 2's accuracy statement: the estimate is within additive `ξ` of
`λ₀`. -/
def additivePrecision (estimate exact ξ : ℝ) : Prop := |estimate - exact| ≤ ξ

/-- **Proposition 2, eq. (A1)**: gate complexity `Õ(Λ/(χ³ξ) + Φ/χ)`. -/
theorem proposition2_gateComplexity (N : ℕ) {Λ Φ Δ ε φ0 χ ξ : ℝ}
    (hΛ : 0 < Λ) (hΦ : 0 < Φ) (hΔ : 0 < Δ) (hχ : 0 < χ) (hχ1 : χ ≤ 1)
    (hε : 0 < ε) (hφ0 : 0 < φ0) (hξ : 0 < ξ)
    (_hacc : ∃ estimate exact : ℝ, additivePrecision estimate exact ξ) :
    IsTildeO (peRunCost Λ Φ χ ξ) (Λ / (χ ^ 3 * ξ) + Φ / χ)
      (polylogScale N Δ ε φ0 χ) :=
  peRunCost_le N hΛ hΦ hΔ hχ hχ1 hε hφ0 hξ

/-- **Proposition 2, qubit count**: `O(log N + log 1/ξ)` qubits. -/
theorem proposition2_qubitComplexity (N : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    IsBigO (estimationQubitLedger N ξ + 1) (estimationQubitLedger N ξ) :=
  estimationQubitLedger_bigO N hξ

end Qatlib.Papers.GroundStPrep17.MainResults.PropositionTwo
