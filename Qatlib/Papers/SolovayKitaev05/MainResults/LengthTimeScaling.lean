/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UnbiasedBases.ThreeBasis.SolovayKitaevCount
set_option warningAsError false

namespace Qatlib.Papers.SolovayKitaev05.MainResults.LengthTimeScaling

open Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo.SU2

set_option autoImplicit false

noncomputable def skLengthExponent : ℝ := Real.log 5 / Real.log (3 / 2)

noncomputable def skRuntimeExponent : ℝ := Real.log 3 / Real.log (3 / 2)

theorem log_three_halves_pos : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)

theorem skLengthExponent_eq_frozen : skLengthExponent = skExponent := rfl

theorem five_eq_rpow : (5 : ℝ) = (3 / 2 : ℝ) ^ skLengthExponent := by
  unfold skLengthExponent
  have hlogne : Real.log (3 / 2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 3 / 2))
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
  rw [mul_comm (Real.log (3 / 2 : ℝ)), div_mul_cancel₀ _ hlogne]
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 5)]

theorem three_eq_rpow : (3 : ℝ) = (3 / 2 : ℝ) ^ skRuntimeExponent := by
  unfold skRuntimeExponent
  have hlogne : Real.log (3 / 2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 3 / 2))
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
  rw [mul_comm (Real.log (3 / 2 : ℝ)), div_mul_cancel₀ _ hlogne]
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 3)]

theorem eq8_length_exponent {R : ℝ} (_hR : 0 < R) {n : ℕ}
    (hn : (3 / 2 : ℝ) ^ n = R) :
    (5 : ℝ) ^ n = R ^ skLengthExponent := by
  have hbase : (0 : ℝ) < 3 / 2 := by norm_num
  calc (5 : ℝ) ^ n = ((3 / 2 : ℝ) ^ skLengthExponent) ^ n := by rw [five_eq_rpow]
    _ = (3 / 2 : ℝ) ^ (skLengthExponent * (n : ℝ)) := by
          rw [← Real.rpow_natCast ((3 / 2 : ℝ) ^ skLengthExponent) n,
            ← Real.rpow_mul hbase.le]
    _ = (3 / 2 : ℝ) ^ ((n : ℝ) * skLengthExponent) := by rw [mul_comm]
    _ = ((3 / 2 : ℝ) ^ n) ^ skLengthExponent := by
          rw [Real.rpow_mul hbase.le, Real.rpow_natCast]
    _ = R ^ skLengthExponent := by rw [hn]

theorem eq9_runtime_exponent {R : ℝ} (_hR : 0 < R) {n : ℕ}
    (hn : (3 / 2 : ℝ) ^ n = R) :
    (3 : ℝ) ^ n = R ^ skRuntimeExponent := by
  have hbase : (0 : ℝ) < 3 / 2 := by norm_num
  calc (3 : ℝ) ^ n = ((3 / 2 : ℝ) ^ skRuntimeExponent) ^ n := by
          conv_lhs => rw [three_eq_rpow]
    _ = (3 / 2 : ℝ) ^ (skRuntimeExponent * (n : ℝ)) := by
          rw [← Real.rpow_natCast ((3 / 2 : ℝ) ^ skRuntimeExponent) n,
            ← Real.rpow_mul hbase.le]
    _ = (3 / 2 : ℝ) ^ ((n : ℝ) * skRuntimeExponent) := by rw [mul_comm]
    _ = ((3 / 2 : ℝ) ^ n) ^ skRuntimeExponent := by
          rw [Real.rpow_mul hbase.le, Real.rpow_natCast]
    _ = R ^ skRuntimeExponent := by rw [hn]

theorem three_lt_skLengthExponent : 3 < skLengthExponent := by
  rw [skLengthExponent_eq_frozen]
  exact three_lt_skExponent

theorem skLengthExponent_lt_four : skLengthExponent < 4 := by
  rw [skLengthExponent_eq_frozen]
  exact skExponent_lt_four

theorem two_lt_skRuntimeExponent : 2 < skRuntimeExponent := by
  have hlog := log_three_halves_pos
  unfold skRuntimeExponent
  rw [lt_div_iff₀ hlog]
  have h : Real.log ((3 / 2 : ℝ) ^ (2 : ℕ)) < Real.log 3 := by
    refine Real.log_lt_log (by norm_num) ?_
    norm_num
  rw [Real.log_pow] at h
  norm_num at h ⊢
  linarith

theorem skRuntimeExponent_lt_three : skRuntimeExponent < 3 := by
  have hlog := log_three_halves_pos
  unfold skRuntimeExponent
  rw [div_lt_iff₀ hlog]
  have h : Real.log 3 < Real.log ((3 / 2 : ℝ) ^ (3 : ℕ)) := by
    refine Real.log_lt_log (by norm_num) ?_
    norm_num
  rw [Real.log_pow] at h
  norm_num at h ⊢
  linarith

end Qatlib.Papers.SolovayKitaev05.MainResults.LengthTimeScaling
