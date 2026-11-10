/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PartitionFunc08.MainResults.Model.SchemeDefs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Qatlib.Papers.PartitionFunc08.MainResults.RatioEstimation

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
