/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PhaseEstimation.Theorem11Quan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators Classical
open Qatlib.Concepts.AmplitudeCore.PhaseEstimation

namespace Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation

lemma sinc_sq_lower (t : ℝ) (ht0 : 0 < t) (ht : t ≤ 1 / 2) :
    4 / Real.pi ^ 2 ≤ Real.sin (Real.pi * t) ^ 2 / (Real.pi ^ 2 * t ^ 2) := by
  have hs : 2 * t ≤ Real.sin (Real.pi * t) := by
    have h := Real.mul_le_sin (x := Real.pi * t) (by positivity)
      (by nlinarith [Real.pi_pos])
    have he : 2 / Real.pi * (Real.pi * t) = 2 * t := by field_simp
    linarith
  have hsin2 : 4 * t ^ 2 ≤ Real.sin (Real.pi * t) ^ 2 := by
    nlinarith [hs, ht0]
  have hden : 0 < Real.pi ^ 2 * t ^ 2 := by positivity
  have hdiv : (4 * t ^ 2) / (Real.pi ^ 2 * t ^ 2) ≤
      Real.sin (Real.pi * t) ^ 2 / (Real.pi ^ 2 * t ^ 2) :=
    div_le_div_of_nonneg_right hsin2 hden.le
  have heq : (4 * t ^ 2) / (Real.pi ^ 2 * t ^ 2) = 4 / Real.pi ^ 2 := by
    field_simp
  linarith

theorem phase_estimation_best_approx_success (M : ℕ) (ω : ℝ) (hM : 2 < M)
    (hω0 : 0 ≤ ω) (hω1 : ω < 1) :
    ∃ x : Fin M,
      bhmt11CircleDist ((x.val : ℝ) / (M : ℝ)) ω ≤ 1 / (2 * (M : ℝ)) ∧
      4 / Real.pi ^ 2 ≤ bhmt11OutcomeMass M ω x := by
  have hM0 : 0 < M := by omega
  have hm : (0 : ℝ) < M := by positivity
  by_cases hi : ∃ j : ℤ, (M : ℝ) * ω = (j : ℝ)
  · obtain ⟨x, hx, hxmass⟩ :=
      bhmt_phase_estimation_theorem11_grid M ω hM0 hω0 hω1 hi
    refine ⟨x, ?_, ?_⟩
    · have he : (x.val : ℝ) / (M : ℝ) = ω := by
        rw [div_eq_iff (ne_of_gt hm)]
        nlinarith
      rw [he, bhmt_phase_estimation_theorem11_distance_round]
      simp
    · rw [hxmass]
      have hpi2 : (4 : ℝ) < Real.pi ^ 2 := by
        nlinarith [Real.pi_gt_d2, Real.pi_pos]
      have hone : (4 : ℝ) / Real.pi ^ 2 ≤ 1 :=
        (div_le_one (by positivity : (0 : ℝ) < Real.pi ^ 2)).mpr hpi2.le
      simpa using hone
  · obtain ⟨t, ht0, ht1, x, y, hxy, hx, hy⟩ :=
      bhmt_phase_estimation_theorem11_nearest_labels M ω hM hω0 hω1 hi
    have hmx := bhmt_phase_estimation_theorem11_mass_lower M ω hM0 x t ht0 hx
    have hpos : 0 < 1 - t := by linarith
    have hmy :=
      bhmt_phase_estimation_theorem11_mass_lower M ω hM0 y (1 - t) hpos hy
    by_cases ht : t ≤ 1 / 2
    · refine ⟨x, ?_, ?_⟩
      · rw [hx]
        have hle : t / (M : ℝ) ≤ (1 / 2) / (M : ℝ) :=
          div_le_div_of_nonneg_right ht hm.le
        calc
          t / (M : ℝ) ≤ (1 / 2) / (M : ℝ) := hle
          _ = 1 / (2 * (M : ℝ)) := by field_simp
      · exact (sinc_sq_lower t ht0 ht).trans hmx
    · have ht2 : 1 / 2 < t := lt_of_not_ge ht
      refine ⟨y, ?_, ?_⟩
      · rw [hy]
        have hsle : 1 - t ≤ 1 / 2 := by linarith
        have hle : (1 - t) / (M : ℝ) ≤ (1 / 2) / (M : ℝ) :=
          div_le_div_of_nonneg_right hsle hm.le
        calc
          (1 - t) / (M : ℝ) ≤ (1 / 2) / (M : ℝ) := hle
          _ = 1 / (2 * (M : ℝ)) := by field_simp
      · exact (sinc_sq_lower (1 - t) hpos (by linarith)).trans hmy

end Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation
