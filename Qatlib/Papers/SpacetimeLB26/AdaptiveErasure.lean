/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ProbabilityCore.ErasureAdaptive.RecordedRun

/-!
# Adaptive erasure survival bounds

This module bounds the survival probability of adaptive erasure policies by deterministic width
allocations under the same total budget. `avoid_complete_erasure` also records the budget on
every history and gives the exponential bound used in [BhartiHaugTanggara2026].

## Main statements

* `deterministic_allocation`: Every erasure policy has a deterministic allocation of total width
  at most `C` whose product survival probability bounds the policy survival probability from
  above.
* `avoid_complete_erasure`: Every history obeys the budget `C`, and for `0 < p < 1` and positive
  `S`, the probability of surviving all layers is at most `exp (-S * p^(C/S))`.

## References

* [Bharti et al., 2026][BhartiHaugTanggara2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open scoped NNReal ENNReal BigOperators
namespace Qatlib.Papers.SpacetimeLB26.AdaptiveErasure
open Qatlib.Foundations.ProbabilityCore.ErasureAdaptive

/-- Every erasure policy has a deterministic allocation of total width at most `C` whose product
survival probability bounds the policy survival probability from above. See
[BhartiHaugTanggara2026]. -/
theorem deterministic_allocation {R : Type*} (p : ℝ≥0) (hp : p ≤ 1) {S C : ℕ}
    (policy : ErasurePolicy R S C) :
    ∃ widths : Fin S → ℕ, (∑ i, widths i) ≤ C ∧
      execute p hp policy true ≤ (↑(∏ i, (1-p^(widths i)) : ℝ≥0) : ℝ≥0∞) :=
  execute_le_allocation p hp policy

/-- Every history obeys the budget `C`, and for `0 < p < 1` and positive `S`, the probability of
surviving all layers is at most `exp (-S * p^(C/S))`. See [BhartiHaugTanggara2026]. -/
theorem avoid_complete_erasure {R : Type*} (p : ℝ≥0) (hp : 0 < p) (hp1 : p < 1)
    {S C : ℕ} (hS : 0 < S) (policy : ErasurePolicy R S C) :
    (∀ history : History policy, (∑ s, historyWidths policy history s) ≤ C) ∧
    (((recordedRun p hp1.le policy).map (survives policy)) true).toReal ≤
      Real.exp (-(S : ℝ) * (p : ℝ) ^ ((C : ℝ)/(S : ℝ))) :=
  ⟨history_cost_le policy, recorded_survival_le_exp p hp hp1 hS policy⟩

end Qatlib.Papers.SpacetimeLB26.AdaptiveErasure
