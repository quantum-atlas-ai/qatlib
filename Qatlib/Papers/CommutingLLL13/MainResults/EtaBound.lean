/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# The unrounded natural-logarithm threshold

This module bounds the real threshold `thresholdNoCeil m η = 4 * m * η * log(η + 2)` for `m ≥ 2`
and `η > 0`. The logarithmic inequalities supply the unrounded scalar threshold estimate
associated with Appendix A.2 of [SattathArad2015].

## Main statements

* `appendix_A2_mul`: Bounds the logarithmic numerator at the real threshold.
* `appendix_A2`: Bounds the numerator-to-threshold ratio by `1 / η`.

## References

* [Sattath and Arad, 2015][SattathArad2015]
-/

namespace Qatlib.Papers.CommutingLLL13.MainResults.EtaBound

/-- The real-valued threshold `4 * m * η * log(η + 2)` before taking a natural-number ceiling. -/
noncomputable def thresholdNoCeil (m : ℕ) (η : ℝ) : ℝ :=
  4 * (m : ℝ) * η * Real.log (η + 2)

/-- For `m ≥ 2` and `η > 0`, `log(thresholdNoCeil m η) + m ≤ 4 * m * log(η + 2)`, the
natural-logarithm threshold inequality associated with [Sattath and Arad, Appendix
A.2][SattathArad2015]. -/
theorem appendix_A2_mul (m : ℕ) (hm : 2 ≤ m) (η : ℝ) (hη : 0 < η) :
    Real.log (thresholdNoCeil m η) + (m : ℝ)
      ≤ 4 * (m : ℝ) * Real.log (η + 2) := by
  unfold thresholdNoCeil
  set L := Real.log (η + 2) with hLdef
  have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos (by linarith)
  have hLne : L ≠ 0 := hLpos.ne'
  have hηne : η ≠ 0 := hη.ne'
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hmne : (m : ℝ) ≠ 0 := hmpos.ne'

  have hexp : Real.log (4 * (m : ℝ) * η * L)
      = Real.log (4 * (m : ℝ)) + Real.log η + Real.log L := by
    rw [Real.log_mul (by positivity : (4 : ℝ) * (m : ℝ) * η ≠ 0) hLne,
        Real.log_mul (by positivity : (4 : ℝ) * (m : ℝ) ≠ 0) hηne,
        Real.log_mul (by norm_num) hmne]

  have hlog4m : Real.log (4 * (m : ℝ)) ≤ (m : ℝ) + 1 / 2 := by
    have hlog4 : Real.log 4 ≤ 3 / 2 := by
      have h4 : Real.log 4 = Real.log 2 + Real.log 2 := by
        rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      rw [h4]
      linarith [Real.log_two_lt_d9]
    have hlogm : Real.log (m : ℝ) ≤ (m : ℝ) - 1 := Real.log_le_sub_one_of_pos hmpos
    have hsplit : Real.log (4 * (m : ℝ)) = Real.log 4 + Real.log (m : ℝ) :=
      Real.log_mul (by norm_num) hmne
    rw [hsplit]
    linarith
  by_cases hL1 : 1 ≤ L
  · have hlogeta : Real.log η ≤ L := by
      rw [hLdef]; exact Real.log_le_log hη (by linarith)
    have hlogL : Real.log L ≤ L - 1 := Real.log_le_sub_one_of_pos hLpos
    rw [hexp]
    nlinarith [hlog4m, hlogeta, hlogL, hmR, hL1]
  · have hLlt : L < 1 := not_le.mp hL1
    have heta_lt_one : η < 1 := by
      have h1 : (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      rw [h1, hLdef] at hLlt
      have hlt : η + 2 < Real.exp 1 :=
        (Real.log_lt_log_iff (by linarith) (Real.exp_pos 1)).mp hLlt
      have he : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
      linarith
    have hlogetanon : Real.log η ≤ 0 := le_of_lt (Real.log_neg hη heta_lt_one)
    have hlogLnon : Real.log L ≤ 0 := le_of_lt (Real.log_neg hLpos hLlt)
    have hLgt : Real.log 2 < L := by
      rw [hLdef]; exact Real.log_lt_log (by norm_num) (by linarith)
    rw [hexp]
    nlinarith [hlog4m, hlogetanon, hlogLnon, hLgt, Real.log_two_gt_d9, hmR, hmpos]

/-- For `m ≥ 2` and `η > 0`, `(log(thresholdNoCeil m η) + m) / thresholdNoCeil m η ≤ 1 / η`.
This is the unrounded natural-logarithm ratio bound associated with [Sattath and Arad,
Appendix A.2][SattathArad2015]. -/
theorem appendix_A2 (m : ℕ) (hm : 2 ≤ m) (η : ℝ) (hη : 0 < η) :
    (Real.log (thresholdNoCeil m η) + (m : ℝ)) / thresholdNoCeil m η ≤ 1 / η := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hLpos : 0 < Real.log (η + 2) := Real.log_pos (by linarith)
  have hTpos : 0 < thresholdNoCeil m η := by
    unfold thresholdNoCeil
    positivity
  have hmul := appendix_A2_mul m hm η hη
  rw [div_le_iff₀ hTpos]
  have hTdiv : (1 / η) * thresholdNoCeil m η
      = 4 * (m : ℝ) * Real.log (η + 2) := by
    unfold thresholdNoCeil
    field_simp
  rw [hTdiv]
  exact hmul

end Qatlib.Papers.CommutingLLL13.MainResults.EtaBound
