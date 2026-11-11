/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Confidence Log

An exact integer comparison provides a uniform logarithmic confidence constant.
-/
set_option autoImplicit false
namespace Qatlib.Foundations.FiniteStats.BornEstimator.ConfidenceLog

/-- An exact integer comparison provides a uniform logarithmic confidence constant. -/
theorem log_eight_le_log_ten : (16 : ℝ)*Real.log 8 ≤ 15*Real.log 10 := by
  have hp : (8 : ℝ)^16 ≤ 10^15 := by norm_num
  have h := Real.log_le_log (by positivity : (0 : ℝ)<8^16) hp
  rw [Real.log_pow,Real.log_pow] at h
  norm_num at h ⊢
  exact h

/-- The original entire confidence range admits one valid constant, including delta between one sixteenth and one tenth. -/
theorem uniform_confidence_log (δ : ℝ) (hδ : 0<δ) (hmax : δ ≤ 1/10) :
    Real.log (1/δ)/16 ≤ Real.log (1/(8*δ)) := by
  have hL : Real.log 10 ≤ Real.log (1/δ) := by
    apply Real.log_le_log (by norm_num : (0 : ℝ)<10)
    apply (le_div_iff₀ hδ).2
    linarith
  have he : 1/(8*δ)=(1/δ)/8 := by ring
  rw [he,Real.log_div (ne_of_gt (div_pos (by norm_num : (0 : ℝ)<1) hδ)) (by norm_num : (8 : ℝ)≠0)]
  have h := log_eight_le_log_ten
  linarith

end Qatlib.Foundations.FiniteStats.BornEstimator.ConfidenceLog
