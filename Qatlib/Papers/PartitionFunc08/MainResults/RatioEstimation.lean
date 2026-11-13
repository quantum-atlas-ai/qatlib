/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PartitionFunc08.MainResults.Model.SchemeDefs

/-!
# Ratio estimation from phase accuracy

A phase estimate is converted into a ratio estimate by `(1 + cos θ') / 2` when `cos θ = 2 * α -
1`. The deterministic error bound `cos_phase_rel_error` transfers a phase-accuracy event of
probability at least seven eighths to relative ratio accuracy. These estimates form part of the
partition-function scheme in [WocjanEtAl2009a].

## Main statements

* `cos_phase_rel_error`: If `α ≥ 0`, `cos θ = 2 * α - 1`, and `|θ' - θ| ≤ 2 * ε * α`, then the
  ratio estimate `(1 + cos θ') / 2` differs from `α` by at most `ε * α`.
* `lemma1_ratio_estimation`: For nonnegative `α` and positive `ε`, a measurable phase estimate
  accurate within `2 * ε * α` with probability at least seven eighths yields a ratio estimate of
  relative error `ε` with at least the same probability.

## References

* [Wocjan et al., 2009][WocjanEtAl2009a]
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Qatlib.Papers.PartitionFunc08.MainResults.RatioEstimation

/-- If `α ≥ 0`, `cos θ = 2 * α - 1`, and `|θ' - θ| ≤ 2 * ε * α`, then the ratio estimate `(1 +
cos θ') / 2` differs from `α` by at most `ε * α`. See [Wocjan et al.,
2009][WocjanEtAl2009a]. -/
theorem cos_phase_rel_error {α ε θ θ' : ℝ} (hα0 : 0 ≤ α)
    (hcos : Real.cos θ = 2 * α - 1)
    (h : |θ' - θ| ≤ 2 * ε * α) :
    |α - (1 + Real.cos θ') / 2| ≤ ε * α := by
  have hα : α = (1 + Real.cos θ) / 2 := by linarith
  have hdiff : α - (1 + Real.cos θ') / 2 = (Real.cos θ - Real.cos θ') / 2 := by
    linarith [hα]
  calc |α - (1 + Real.cos θ') / 2|
      = |Real.cos θ - Real.cos θ'| / 2 := by
        rw [hdiff, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ |θ - θ'| / 2 := by
        have := abs_cos_sub_cos_le' θ θ'
        linarith
    _ = |θ' - θ| / 2 := by rw [abs_sub_comm]
    _ ≤ ε * α := by linarith

/-- For nonnegative `α` and positive `ε`, a measurable phase estimate accurate within `2 * ε *
α` with probability at least seven eighths yields a ratio estimate of relative error `ε`
with at least the same probability. See [Wocjan et al., 2009][WocjanEtAl2009a]. -/
theorem lemma1_ratio_estimation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {α ε θ : ℝ} (hα0 : 0 ≤ α) (hcos : Real.cos θ = 2 * α - 1) (hε0 : 0 < ε)
    (θ' : Ω → ℝ) (hθ' : Measurable θ')
    (hphase : 7 / 8 ≤ μ.real {ω | |θ' ω - θ| ≤ 2 * ε * α}) :
    7 / 8 ≤ μ.real (relAccEvent α ε (fun ω => (1 + Real.cos (θ' ω)) / 2)) := by
  refine le_trans hphase (measureReal_mono ?_)
  intro ω hω
  simp only [relAccEvent, Set.mem_setOf_eq] at hω ⊢
  exact ⟨by

      have h := cos_phase_rel_error hα0 hcos hω
      have habs := abs_le.mp h
      linarith [habs.1],
    by
      have h := cos_phase_rel_error hα0 hcos hω
      have habs := abs_le.mp h
      linarith [habs.2]⟩

end Qatlib.Papers.PartitionFunc08.MainResults.RatioEstimation
