/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutingLLL13.MainResults.EtaBound
import Qatlib.Papers.CommutingLLL13.MainResults.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Tactic

/-!
# A ceiling-adjusted failure threshold

This module controls the logarithmic numerator after rounding the natural-logarithm threshold to
an integer. For positive `η` and `κ` satisfying `η * δ * κ = 1`, it bounds the resulting failure
expression by `δ`, as in the threshold analysis of [SattathArad2015].

## Main statements

* `ceil_log_bound`: Bounds the numerator using the unrounded threshold plus one.
* `eq5_le_delta`: Bounds the rounded threshold expression by the target `δ`.

## References

* [Sattath and Arad, 2015][SattathArad2015]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

noncomputable section

namespace Qatlib.Papers.CommutingLLL13.MainResults.FailureBound

open Qatlib.Papers.CommutingLLL13.MainResults

/-- For `m ≥ 2` and `η > 0`, `log(thresholdNoCeil m η + 1) + m ≤ 4 * m * log(η + 2)`,
controlling the numerator after ceiling rounding. -/
theorem ceil_log_bound (m : ℕ) (hm : 2 ≤ m) (η : ℝ) (hη : 0 < η) :
    Real.log (EtaBound.thresholdNoCeil m η + 1) + (m : ℝ)
      ≤ 4 * (m : ℝ) * Real.log (η + 2) := by
  set L := Real.log (η + 2) with hLdef
  set T0 := EtaBound.thresholdNoCeil m η with hT0def
  have hLpos : 0 < L := by
    rw [hLdef]; exact Real.log_pos (by linarith)
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hT0pos : 0 < T0 := by
    rw [hT0def]; unfold EtaBound.thresholdNoCeil
    positivity
  have hT0eq : T0 = 4 * (m : ℝ) * η * L := by rw [hT0def]; rfl
  have hbase := EtaBound.appendix_A2_mul m hm η hη
  have hexp : Real.log T0 = Real.log (4 * (m : ℝ)) + Real.log η + Real.log L := by
    rw [hT0eq]
    rw [Real.log_mul (by positivity : (4 : ℝ) * (m : ℝ) * η ≠ 0) hLpos.ne',
        Real.log_mul (by positivity : (4 : ℝ) * (m : ℝ) ≠ 0) hη.ne',
        Real.log_mul (by norm_num) hmpos.ne']
  have hlog4m : Real.log (4 * (m : ℝ)) ≤ (m : ℝ) + 1 / 2 := by
    have hlog4 : Real.log 4 ≤ 3 / 2 := by
      have h4 : Real.log 4 = Real.log 2 + Real.log 2 := by
        rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      rw [h4]; linarith [Real.log_two_lt_d9]
    have hlogm : Real.log (m : ℝ) ≤ (m : ℝ) - 1 := Real.log_le_sub_one_of_pos hmpos
    rw [Real.log_mul (by norm_num) hmpos.ne']
    linarith
  by_cases hL1 : 1 ≤ L
  · by_cases hT01 : 1 ≤ T0
    · have hlog_le : Real.log (T0 + 1) ≤ Real.log (2 * T0) := by
        apply Real.log_le_log (by positivity)
        linarith
      have hlog2T : Real.log (2 * T0) = Real.log 2 + Real.log T0 :=
        Real.log_mul (by norm_num) hT0pos.ne'
      have hlogeta : Real.log η ≤ L := by
        rw [hLdef]; exact Real.log_le_log hη (by linarith)
      have hlogL : Real.log L ≤ L - 1 := Real.log_le_sub_one_of_pos hLpos
      have hslack : Real.log 2 + Real.log T0 + (m : ℝ) ≤ 4 * (m : ℝ) * L := by
        rw [hexp]
        nlinarith [hlog4m, hlogeta, hlogL, hL1, hmR, Real.log_two_lt_d9]
      linarith
    · have hT0lt : T0 < 1 := not_le.mp hT01
      have hlog_le : Real.log (T0 + 1) ≤ Real.log 2 := by
        apply Real.log_le_log (by positivity)
        linarith
      nlinarith [hlog_le, hL1, hmR, Real.log_two_lt_d9]
  · have hLlt : L < 1 := not_le.mp hL1
    have heta_lt_one : η < 1 := by
      have h1 : (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      rw [h1, hLdef] at hLlt
      have hlt : η + 2 < Real.exp 1 :=
        (Real.log_lt_log_iff (by linarith) (Real.exp_pos 1)).mp hLlt
      have he : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
      linarith
    have hprod : η * L < 1 := by
      have h1 : η * L < η * 1 := mul_lt_mul_of_pos_left hLlt hη
      nlinarith
    have hT0lt4 : T0 < 4 * (m : ℝ) := by
      rw [hT0eq]
      nlinarith [hprod, hmpos]
    have hlog_le : Real.log (T0 + 1) ≤ Real.log (4 * (m : ℝ) + 1) := by
      apply Real.log_le_log (by positivity)
      linarith
    have hlog4m1 : Real.log (4 * (m : ℝ) + 1) ≤ (m : ℝ) + 0.525 := by
      have h4m : (0 : ℝ) < 4 * (m : ℝ) := by positivity
      have hstep : Real.log (4 * (m : ℝ) + 1)
          ≤ Real.log (4 * (m : ℝ)) + 1 / (4 * (m : ℝ)) := by
        have hx : (0 : ℝ) < 1 + 1 / (4 * (m : ℝ)) := by positivity
        have h := Real.log_le_sub_one_of_pos hx
        rw [show 4 * (m : ℝ) + 1 = (4 * (m : ℝ)) * (1 + 1 / (4 * (m : ℝ))) by
          field_simp]
        rw [Real.log_mul h4m.ne' hx.ne']
        linarith
      have hlog4 : Real.log 4 ≤ 1.4 := by
        have h4 : Real.log 4 = Real.log 2 + Real.log 2 := by
          rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
        rw [h4]; linarith [Real.log_two_lt_d9]
      have hlogm : Real.log (m : ℝ) ≤ (m : ℝ) - 1 := Real.log_le_sub_one_of_pos hmpos
      have hlog4m : Real.log (4 * (m : ℝ)) = Real.log 4 + Real.log (m : ℝ) :=
        Real.log_mul (by norm_num) hmpos.ne'
      have hinv : 1 / (4 * (m : ℝ)) ≤ 1 / 8 := by
        rw [one_div_le_one_div] <;> nlinarith
      linarith
    have hLlog2 : Real.log 2 < L := by
      rw [hLdef]; exact Real.log_lt_log (by norm_num) (by linarith)
    nlinarith [hlog_le, hlog4m1, hLlog2, Real.log_two_gt_d9, hmR]

/-- For `m ≥ 2`, positive `η` and `κ`, and `η * δ * κ = 1`, the natural-logarithm failure
expression at `thresholdNatural m η` is at most `δ`. This gives the ceiling-adjusted
threshold estimate associated with [Sattath and Arad, Appendix A.2][SattathArad2015]. -/
theorem eq5_le_delta
    (m : ℕ) (hm : 2 ≤ m) (η κ δ : ℝ) (hη : 0 < η) (hκ : 0 < κ)
    (hηδ : η * δ * κ = 1) :
    (Real.log ((Defs.thresholdNatural m η : ℝ)) + (m : ℝ))
        / ((Defs.thresholdNatural m η : ℝ) * κ) ≤ δ := by
  set T := Defs.thresholdNatural m η with hTdef
  set T0 := EtaBound.thresholdNoCeil m η with hT0def
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hLpos : 0 < Real.log (η + 2) := Real.log_pos (by linarith)
  have hT0pos : 0 < T0 := by
    rw [hT0def]
    unfold EtaBound.thresholdNoCeil
    exact mul_pos (mul_pos (mul_pos (by norm_num) hmpos) hη) hLpos
  have hTge : T0 ≤ (T : ℝ) := by
    rw [hTdef]; exact Nat.le_ceil T0
  have hTlt : (T : ℝ) < T0 + 1 := by
    rw [hTdef]; exact Nat.ceil_lt_add_one (le_of_lt hT0pos)
  have hTpos : (0 : ℝ) < (T : ℝ) := lt_of_lt_of_le hT0pos hTge

  have hlogT : Real.log (T : ℝ) ≤ Real.log (T0 + 1) :=
    Real.log_le_log hTpos (le_of_lt hTlt)

  have hb : Real.log (T0 + 1) + (m : ℝ) ≤ 4 * (m : ℝ) * Real.log (η + 2) := by
    simpa only [hT0def] using ceil_log_bound m hm η hη
  have hbm : Real.log (T : ℝ) + (m : ℝ) ≤ 4 * (m : ℝ) * Real.log (η + 2) := by
    linarith

  have hkey : η * (Real.log (T : ℝ) + (m : ℝ)) ≤ (T : ℝ) := by
    have h1 : η * (Real.log (T : ℝ) + (m : ℝ))
        ≤ η * (4 * (m : ℝ) * Real.log (η + 2)) :=
      mul_le_mul_of_nonneg_left hbm (le_of_lt hη)
    have h2 : η * (4 * (m : ℝ) * Real.log (η + 2)) = T0 := by
      rw [hT0def]; unfold EtaBound.thresholdNoCeil; ring
    rw [h2] at h1
    linarith

  have hδeq : δ = 1 / (η * κ) := by
    rw [eq_div_iff (by positivity : η * κ ≠ 0)]
    linarith [hηδ]
  rw [hδeq,
      div_le_iff₀ (by positivity : (0 : ℝ) < (T : ℝ) * κ)]
  have hrhs : (1 / (η * κ)) * ((T : ℝ) * κ) = (T : ℝ) / η := by
    field_simp
  rw [hrhs, le_div_iff₀ hη]
  linarith [hkey]

end Qatlib.Papers.CommutingLLL13.MainResults.FailureBound
