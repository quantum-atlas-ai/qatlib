/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ProbabilityCore.ErasureAdaptive.RecordedRun
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open scoped NNReal ENNReal BigOperators
namespace Qatlib.Papers.SpacetimeLB26.AdaptiveErasure
open Qatlib.Foundations.ProbabilityCore.ErasureAdaptive

theorem deterministic_allocation {R : Type*} (p : ℝ≥0) (hp : p ≤ 1) {S C : ℕ}
    (policy : ErasurePolicy R S C) :
    ∃ widths : Fin S → ℕ, (∑ i, widths i) ≤ C ∧
      execute p hp policy true ≤ (↑(∏ i, (1-p^(widths i)) : ℝ≥0) : ℝ≥0∞) :=
  execute_le_allocation p hp policy

theorem avoid_complete_erasure {R : Type*} (p : ℝ≥0) (hp : 0 < p) (hp1 : p < 1)
    {S C : ℕ} (hS : 0 < S) (policy : ErasurePolicy R S C) :
    (∀ history : History policy, (∑ s, historyWidths policy history s) ≤ C) ∧
    (((recordedRun p hp1.le policy).map (survives policy)) true).toReal ≤
      Real.exp (-(S : ℝ) * (p : ℝ) ^ ((C : ℝ)/(S : ℝ))) :=
  ⟨history_cost_le policy, recorded_survival_le_exp p hp hp1 hS policy⟩

end Qatlib.Papers.SpacetimeLB26.AdaptiveErasure
