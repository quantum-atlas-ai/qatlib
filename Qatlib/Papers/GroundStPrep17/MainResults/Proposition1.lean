/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GroundStPrep17.MainResults.CostLedger

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 1 of arXiv:1712.03193v2 (fixed version v2, 2 Feb 2018)

*Minimum label finding* (Appendix A, pp. 8-9).

Given a circuit `C_Φ` on `q+n+m` qubits preparing

`|Φ⟩ = |0⟩^{⊗q} Σ_{i=0}^{2ⁿ-1} |i⟩|Φᵢ⟩ + |R⟩`   (eq. (29))

and parameters `ζ ∈ (0,1)`, `δ ∈ (0,1/5)`, `J̃ ≤ J` with

`‖|Φ_J⟩‖ ≥ ζ` and `Σ_{i=0}^{J̃} ‖|Φᵢ⟩‖² < ζ² δ / (4 n log(n/δ) ln²(2/δ))`   (eq. (30)),

the algorithm prepares `|j⟩|Φ_j⟩/‖|Φ_j⟩‖` for some `j ∈ [J̃, J]` with
probability at least `1 - 5δ`, using

* `O((n/ζ) log²(n/δ))` calls to `C_Φ`   (eq. (31)),
* `O(poly(q,n,m)/ζ · log²(n/δ))` additional elementary gates   (eq. (32)),
* `q + n + m + 1` qubits.

The formal statements are the quantitative resource bounds on the ledgers
`CostLedger.minLabelCallCost` / `minLabelGateLedger` and the explicit success
margin `1 - 5δ`; the amplitude/window condition (30) is recorded as the
threshold predicate `minLabelTruncationCondition`, and the state-preparation
semantics (29) is not modelled.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.GroundStPrep17.MainResults.PropositionOne

open Qatlib.Papers.GroundStPrep17.MainResults

/-- The truncation window of eq. (30):
`ζ² δ / (4 n log(n/δ) ln²(2/δ))`, the bound on `Σ_{i ≤ J̃} ‖|Φᵢ⟩‖²`. -/
def minLabelAmplitudeWindow (n : ℕ) (ζ δ : ℝ) : ℝ :=
  ζ ^ 2 * δ / (4 * (n : ℝ) * Real.log ((n : ℝ) / δ) * (Real.log (2 / δ)) ^ 2)

/-- Condition (30): the truncated tail mass is below the window.  `tailMass`
plays the role of `Σ_{i=0}^{J̃} ‖|Φᵢ⟩‖²`. -/
def minLabelTruncationCondition (n : ℕ) (ζ δ tailMass : ℝ) : Prop :=
  tailMass < minLabelAmplitudeWindow n ζ δ

/-- The success probability `1 - 5δ` of Proposition 1. -/
def minLabelSuccessProbability (δ : ℝ) : ℝ := 1 - 5 * δ

/-- Eq. (30) window positivity for `ζ > 0`, `δ ∈ (0, 1/5)`. -/
lemma minLabelAmplitudeWindow_pos {n : ℕ} {ζ δ : ℝ}
    (hn : 1 ≤ n) (hζ : 0 < ζ) (hδ : 0 < δ) (hδ1 : δ < 1 / 5) :
    0 < minLabelAmplitudeWindow n ζ δ := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h1 : 1 < (n : ℝ) / δ := by
    rw [lt_div_iff₀ hδ]
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have h2 : 1 < 2 / δ := by
    rw [lt_div_iff₀ hδ]
    linarith
  have hL : 0 < Real.log ((n : ℝ) / δ) := Real.log_pos h1
  have hM : 0 < Real.log (2 / δ) := Real.log_pos h2
  unfold minLabelAmplitudeWindow
  positivity

/-- The success probability of Proposition 1 is positive. -/
lemma minLabelSuccessProbability_pos {δ : ℝ} (hδ : δ < 1 / 5) :
    0 < minLabelSuccessProbability δ := by
  unfold minLabelSuccessProbability
  linarith

/-- The success probability of Proposition 1 is below one. -/
lemma minLabelSuccessProbability_lt_one {δ : ℝ} (hδ : 0 < δ) :
    minLabelSuccessProbability δ < 1 := by
  unfold minLabelSuccessProbability
  linarith

/-- **Proposition 1, eq. (31)**: `O((n/ζ) log²(n/δ))` calls to `C_Φ`. -/
theorem proposition1_callComplexity {n : ℕ} {ζ δ : ℝ}
    (hn : 1 ≤ n) (hζ : 0 < ζ) (hL : 1 ≤ Real.log ((n : ℝ) / δ)) :
    IsBigO (minLabelCallCost n ζ δ) (minLabelCallBound n ζ δ) :=
  minLabelCallCost_le hn hζ hL

/-- **Proposition 1, eq. (32)**: `O(poly(q,n,m)/ζ · log²(n/δ))` elementary
gates, with `poly(q,n,m) = (q+n+m+1)²`. -/
theorem proposition1_gateComplexity {q n m : ℕ} {ζ δ : ℝ}
    (hn : 1 ≤ n) (hζ : 0 < ζ) (hL : 1 ≤ Real.log ((n : ℝ) / δ)) :
    IsBigO (minLabelGateLedger q n m ζ δ) (minLabelGateBound q n m ζ δ) :=
  minLabelGateLedger_le hn hζ hL

/-- **Proposition 1, qubit count**: `q + n + m + 1` qubits, exactly. -/
theorem proposition1_qubitCount (q n m : ℕ) :
    minLabelQubitCount q n m = q + n + m + 1 := rfl

end Qatlib.Papers.GroundStPrep17.MainResults.PropositionOne
