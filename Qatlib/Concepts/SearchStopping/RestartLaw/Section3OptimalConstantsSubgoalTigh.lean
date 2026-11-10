/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.RestartLaw.Section3OptimalConstantsSubgoalStat
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option warningAsError false

namespace Qatlib.Concepts.SearchStopping.RestartLaw

theorem section3OptimalConstantsSubgoal : Section3OptimalConstantsSubgoal := by
  intro z hz hl hu
  have hz0 : 0 < z := by linarith
  have hc : Real.cos (z / 2) ≠ 0 := by
    intro h
    rw [Real.tan_eq_sin_div_cos, h, div_zero] at hz
    linarith
  have hs : Real.sin (z / 2) = z * Real.cos (z / 2) := by
    exact (div_eq_iff hc).mp (by simpa [Real.tan_eq_sin_div_cos] using hz)
  have hunit := Real.sin_sq_add_cos_sq (z / 2)
  have hden : 0 < 1 + z ^ 2 := by positivity
  have hsq : Real.sin (z / 2) ^ 2 = z ^ 2 / (1 + z ^ 2) := by
    apply (eq_div_iff (ne_of_gt hden)).mpr
    rw [hs] at hunit ⊢
    nlinarith [congrArg (fun t : ℝ => z ^ 2 * t) hunit]
  have hsz : 0 < Real.sin (z / 2) ^ 2 := by rw [hsq]; positivity
  have he : z / (4 * Real.sin (z / 2) ^ 2) = (1 + z ^ 2) / (4 * z) := by
    rw [hsq]
    field_simp [ne_of_gt hz0, ne_of_gt hden]
  have hzsqlo : (233112 / 100000 : ℝ) ^ 2 < z ^ 2 := by nlinarith
  have hzsqhi : z ^ 2 < (233113 / 100000 : ℝ) ^ 2 := by nlinarith
  have hp1 : (8445 / 10000 : ℝ) < Real.sin (z / 2) ^ 2 := by
    rw [hsq, lt_div_iff₀ hden]
    nlinarith
  have hp2 : Real.sin (z / 2) ^ 2 < (8446 / 10000 : ℝ) := by
    rw [hsq, div_lt_iff₀ hden]
    nlinarith
  have hd : 0 < 4 * z := by positivity
  have he1 : (69002 / 100000 : ℝ) < z / (4 * Real.sin (z / 2) ^ 2) := by
    rw [he, lt_div_iff₀ hd]
    nlinarith
  have he2 : z / (4 * Real.sin (z / 2) ^ 2) < (69003 / 100000 : ℝ) := by
    rw [he, div_lt_iff₀ hd]
    nlinarith
  refine ⟨hp1, hp2, ?_, ?_, he1, he2, ?_, ?_⟩
  · linarith
  · linarith
  · linarith [Real.pi_lt_d2]
  · linarith [Real.pi_gt_d2]

end Qatlib.Concepts.SearchStopping.RestartLaw
