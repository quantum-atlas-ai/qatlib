/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPreimage16.ConditionalCost.Defs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QPreimage16.ConditionalCost

open Qatlib.Foundations.ResourceBounds.LogBudgets

noncomputable def sha256Cycles (tDepth : ℝ) : ℝ :=
  surfaceCodeCycles (ledgerIterations 128) tDepth

noncomputable def sha256Total (tDepth : ℝ) : ℝ :=
  totalCost 2402 1 3600 (sha256Cycles tDepth)

theorem sha256_cycles_formula (tDepth : ℝ) :
    sha256Cycles tDepth = ledgerIterations 128 * 530 * (2 * tDepth) := rfl

theorem sha256_total_cost_eq (tDepth : ℝ) :
    sha256Total tDepth = 6002 * sha256Cycles tDepth := by
  unfold sha256Total totalCost
  norm_num

theorem sha256_overhead_eq (tDepth : ℝ) :
    overhead (sha256Total tDepth) 128 = (log2 (sha256Total tDepth) - 128) / 8 := by
  rw [overhead_eq]
  norm_num

lemma sha256_cycles_pos (tDepth : ℝ)
    (hlo : (2 : ℝ) ^ (153.7 : ℝ) ≤ sha256Cycles tDepth) : 0 < sha256Cycles tDepth :=
  lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) hlo

lemma sha256_total_lower (tDepth : ℝ)
    (hlo : (2 : ℝ) ^ (153.7 : ℝ) ≤ sha256Cycles tDepth) :
    (2 : ℝ) ^ (165 : ℝ) ≤ sha256Total tDepth := by
  have htot := sha256_total_cost_eq tDepth
  calc (2 : ℝ) ^ (165 : ℝ) ≤ (2 : ℝ) ^ (165.7 : ℝ) :=
        (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr (by norm_num)
    _ = (2 : ℝ) ^ (12 : ℝ) * (2 : ℝ) ^ (153.7 : ℝ) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        norm_num
    _ = 4096 * (2 : ℝ) ^ (153.7 : ℝ) := by
        rw [show (2 : ℝ) ^ (12 : ℝ) = 4096 by
          rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) from rfl, Real.rpow_natCast]; norm_num]
    _ ≤ 6002 * (2 : ℝ) ^ (153.7 : ℝ) :=
        mul_le_mul_of_nonneg_right (by norm_num : (4096 : ℝ) ≤ 6002) (by positivity)
    _ ≤ 6002 * sha256Cycles tDepth := mul_le_mul_of_nonneg_left hlo (by norm_num)
    _ = sha256Total tDepth := htot.symm

lemma sha256_total_upper (tDepth : ℝ)
    (hlo : (2 : ℝ) ^ (153.7 : ℝ) ≤ sha256Cycles tDepth)
    (hhi : sha256Cycles tDepth ≤ (2 : ℝ) ^ (153.9 : ℝ)) :
    sha256Total tDepth ≤ (2 : ℝ) ^ (167 : ℝ) := by
  have hpos := sha256_cycles_pos tDepth hlo
  have htot := sha256_total_cost_eq tDepth
  calc sha256Total tDepth = 6002 * sha256Cycles tDepth := htot
    _ ≤ 8192 * sha256Cycles tDepth :=
        mul_le_mul_of_nonneg_right (by norm_num : (6002 : ℝ) ≤ 8192) hpos.le
    _ ≤ 8192 * (2 : ℝ) ^ (153.9 : ℝ) :=
        mul_le_mul_of_nonneg_left hhi (by norm_num)
    _ = (2 : ℝ) ^ (13 : ℝ) * (2 : ℝ) ^ (153.9 : ℝ) := by
        rw [show (2 : ℝ) ^ (13 : ℝ) = 8192 by
          rw [show (13 : ℝ) = ((13 : ℕ) : ℝ) from rfl, Real.rpow_natCast]; norm_num]
    _ = (2 : ℝ) ^ (166.9 : ℝ) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        norm_num
    _ ≤ (2 : ℝ) ^ (167 : ℝ) :=
        (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr (by norm_num)

lemma sha256_log_lower (tDepth : ℝ)
    (hlo : (2 : ℝ) ^ (153.7 : ℝ) ≤ sha256Cycles tDepth) :
    (165 : ℝ) ≤ log2 (sha256Total tDepth) := by
  have htot := sha256_total_cost_eq tDepth
  have htotpos : 0 < sha256Total tDepth := by
    rw [htot]
    exact mul_pos (by norm_num) (sha256_cycles_pos tDepth hlo)
  have hlow : (2 : ℝ) ^ (165 : ℝ) ≤ sha256Total tDepth := sha256_total_lower tDepth hlo
  calc (165 : ℝ) = log2 ((2 : ℝ) ^ (165 : ℝ)) := (log2_two_rpow 165).symm
    _ ≤ log2 (sha256Total tDepth) :=
        log2_mono (Real.rpow_pos_of_pos (by norm_num) _) hlow

lemma sha256_log_upper (tDepth : ℝ)
    (hlo : (2 : ℝ) ^ (153.7 : ℝ) ≤ sha256Cycles tDepth)
    (hhi : sha256Cycles tDepth ≤ (2 : ℝ) ^ (153.9 : ℝ)) :
    log2 (sha256Total tDepth) ≤ (167 : ℝ) := by
  have htot := sha256_total_cost_eq tDepth
  have htotpos : 0 < sha256Total tDepth := by
    rw [htot]
    exact mul_pos (by norm_num) (sha256_cycles_pos tDepth hlo)
  have hhigh : sha256Total tDepth ≤ (2 : ℝ) ^ (167 : ℝ) := sha256_total_upper tDepth hlo hhi
  calc log2 (sha256Total tDepth) ≤ log2 ((2 : ℝ) ^ (167 : ℝ)) := log2_mono htotpos hhigh
    _ = 167 := log2_two_rpow 167

theorem sha256_reported_magnitude (tDepth : ℝ)
    (hlo : (2 : ℝ) ^ (153.7 : ℝ) ≤ sha256Cycles tDepth)
    (hhi : sha256Cycles tDepth ≤ (2 : ℝ) ^ (153.9 : ℝ)) :
    (2 : ℝ) ^ (165 : ℝ) ≤ sha256Total tDepth ∧
      sha256Total tDepth ≤ (2 : ℝ) ^ (167 : ℝ) ∧
      4.6 ≤ overhead (sha256Total tDepth) 128 ∧
      overhead (sha256Total tDepth) 128 ≤ 4.9 := by
  refine ⟨sha256_total_lower tDepth hlo, sha256_total_upper tDepth hlo hhi, ?_, ?_⟩
  · rw [sha256_overhead_eq]
    have h := sha256_log_lower tDepth hlo
    have : (4.6 : ℝ) ≤ ((165 : ℝ) - 128) / 8 := by norm_num
    linarith
  · rw [sha256_overhead_eq]
    have h := sha256_log_upper tDepth hlo hhi
    have : ((167 : ℝ) - 128) / 8 ≤ (4.9 : ℝ) := by norm_num
    linarith

end Qatlib.Papers.QPreimage16.ConditionalCost
