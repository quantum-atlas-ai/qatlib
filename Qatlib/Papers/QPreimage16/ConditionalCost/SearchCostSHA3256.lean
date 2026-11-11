/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPreimage16.ConditionalCost.Defs

/-!
# Conditional SHA3-256 preimage-search resource bounds

This module defines the SHA3-256 cycle and total-cost expressions in the conditional model of
[AmyEtAl2017]. The total-cost multiplier is 1061600, and assumed cycle bounds yield
corresponding bounds on total cost, its base-two logarithm, and overhead.

The result `sha3_256_reported_magnitude` bounds the total cost between `2 ^ 166` and `2 ^ 168`
and the overhead between 4.7 and 5.0 under the stated cycle interval.

## Main statements

* `sha3_256_total_cost_eq`: The SHA3-256 total-cost expression equals 1061600 times its cycle
  estimate.
* `sha3_256_reported_magnitude`: If the SHA3-256 cycle estimate lies between `2 ^ 146.4` and `2
  ^ 146.6`, its total cost lies between `2 ^ 166` and `2 ^ 168`, with overhead between 4.7 and
  5.0. These conditional bounds bracket the magnitude reported in [AmyEtAl2017].

## References

* [Amy et al., 2017][AmyEtAl2017]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QPreimage16.ConditionalCost

open Qatlib.Foundations.ResourceBounds.LogBudgets

/-- The conditional SHA3-256 cycle estimate obtained from `ledgerIterations 128` and the
supplied T-depth. -/
noncomputable def sha3_256Cycles (tDepth : ℝ) : ℝ :=
  surfaceCodeCycles (ledgerIterations 128) tDepth

/-- The SHA3-256 total-cost expression with qubit parameters 3200, 294, and 3600 and cycle count
`sha3_256Cycles tDepth`. -/
noncomputable def sha3_256Total (tDepth : ℝ) : ℝ :=
  totalCost 3200 294 3600 (sha3_256Cycles tDepth)

/-- The SHA3-256 cycle estimate equals `ledgerIterations 128 * 530 * (2 * tDepth)`. -/
theorem sha3_256_cycles_formula (tDepth : ℝ) :
    sha3_256Cycles tDepth = ledgerIterations 128 * 530 * (2 * tDepth) := rfl

/-- The SHA3-256 total-cost expression equals 1061600 times its cycle estimate. -/
theorem sha3_256_total_cost_eq (tDepth : ℝ) :
    sha3_256Total tDepth = 1061600 * sha3_256Cycles tDepth := by
  unfold sha3_256Total totalCost
  norm_num

/-- The SHA3-256 overhead relative to exponent 128 equals `(log2 (sha3_256Total tDepth) - 128) /
8`. -/
theorem sha3_256_overhead_eq (tDepth : ℝ) :
    overhead (sha3_256Total tDepth) 128 = (log2 (sha3_256Total tDepth) - 128) / 8 := by
  rw [overhead_eq]
  norm_num

/-- A SHA3-256 cycle estimate at least `2 ^ 146.4` is strictly positive. -/
lemma sha3_256_cycles_pos (tDepth : ℝ)
    (hlo : (2 : ℝ) ^ (146.4 : ℝ) ≤ sha3_256Cycles tDepth) : 0 < sha3_256Cycles tDepth :=
  lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) hlo

/-- A cycle estimate at least `2 ^ 146.4` implies a SHA3-256 total cost at least `2 ^ 166`. -/
lemma sha3_256_total_lower (tDepth : ℝ)
    (hlo : (2 : ℝ) ^ (146.4 : ℝ) ≤ sha3_256Cycles tDepth) :
    (2 : ℝ) ^ (166 : ℝ) ≤ sha3_256Total tDepth := by
  have htot := sha3_256_total_cost_eq tDepth
  calc (2 : ℝ) ^ (166 : ℝ) ≤ (2 : ℝ) ^ (166.4 : ℝ) :=
        (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr (by norm_num)
    _ = (2 : ℝ) ^ (20 : ℝ) * (2 : ℝ) ^ (146.4 : ℝ) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        norm_num
    _ = 1048576 * (2 : ℝ) ^ (146.4 : ℝ) := by
        rw [show (2 : ℝ) ^ (20 : ℝ) = 1048576 by
          rw [show (20 : ℝ) = ((20 : ℕ) : ℝ) from rfl, Real.rpow_natCast]; norm_num]
    _ ≤ 1061600 * (2 : ℝ) ^ (146.4 : ℝ) :=
        mul_le_mul_of_nonneg_right (by norm_num : (1048576 : ℝ) ≤ 1061600) (by positivity)
    _ ≤ 1061600 * sha3_256Cycles tDepth := mul_le_mul_of_nonneg_left hlo (by norm_num)
    _ = sha3_256Total tDepth := htot.symm

/-- A cycle estimate between `2 ^ 146.4` and `2 ^ 146.6` implies a SHA3-256 total cost at most
`2 ^ 168`. -/
lemma sha3_256_total_upper (tDepth : ℝ)
    (hlo : (2 : ℝ) ^ (146.4 : ℝ) ≤ sha3_256Cycles tDepth)
    (hhi : sha3_256Cycles tDepth ≤ (2 : ℝ) ^ (146.6 : ℝ)) :
    sha3_256Total tDepth ≤ (2 : ℝ) ^ (168 : ℝ) := by
  have hpos := sha3_256_cycles_pos tDepth hlo
  have htot := sha3_256_total_cost_eq tDepth
  calc sha3_256Total tDepth = 1061600 * sha3_256Cycles tDepth := htot
    _ ≤ 2097152 * sha3_256Cycles tDepth :=
        mul_le_mul_of_nonneg_right (by norm_num : (1061600 : ℝ) ≤ 2097152) hpos.le
    _ ≤ 2097152 * (2 : ℝ) ^ (146.6 : ℝ) :=
        mul_le_mul_of_nonneg_left hhi (by norm_num)
    _ = (2 : ℝ) ^ (21 : ℝ) * (2 : ℝ) ^ (146.6 : ℝ) := by
        rw [show (2 : ℝ) ^ (21 : ℝ) = 2097152 by
          rw [show (21 : ℝ) = ((21 : ℕ) : ℝ) from rfl, Real.rpow_natCast]; norm_num]
    _ = (2 : ℝ) ^ (167.6 : ℝ) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        norm_num
    _ ≤ (2 : ℝ) ^ (168 : ℝ) :=
        (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr (by norm_num)

/-- A cycle estimate at least `2 ^ 146.4` implies `log2 (sha3_256Total tDepth) ≥ 166`. -/
lemma sha3_256_log_lower (tDepth : ℝ)
    (hlo : (2 : ℝ) ^ (146.4 : ℝ) ≤ sha3_256Cycles tDepth) :
    (166 : ℝ) ≤ log2 (sha3_256Total tDepth) := by
  have hlow : (2 : ℝ) ^ (166 : ℝ) ≤ sha3_256Total tDepth := sha3_256_total_lower tDepth hlo
  calc (166 : ℝ) = log2 ((2 : ℝ) ^ (166 : ℝ)) := (log2_two_rpow 166).symm
    _ ≤ log2 (sha3_256Total tDepth) :=
        log2_mono (Real.rpow_pos_of_pos (by norm_num) _) hlow

/-- A cycle estimate between `2 ^ 146.4` and `2 ^ 146.6` implies `log2 (sha3_256Total tDepth) ≤
168`. -/
lemma sha3_256_log_upper (tDepth : ℝ)
    (hlo : (2 : ℝ) ^ (146.4 : ℝ) ≤ sha3_256Cycles tDepth)
    (hhi : sha3_256Cycles tDepth ≤ (2 : ℝ) ^ (146.6 : ℝ)) :
    log2 (sha3_256Total tDepth) ≤ (168 : ℝ) := by
  have htot := sha3_256_total_cost_eq tDepth
  have htotpos : 0 < sha3_256Total tDepth := by
    rw [htot]
    exact mul_pos (by norm_num) (sha3_256_cycles_pos tDepth hlo)
  have hhigh : sha3_256Total tDepth ≤ (2 : ℝ) ^ (168 : ℝ) := sha3_256_total_upper tDepth hlo hhi
  calc log2 (sha3_256Total tDepth) ≤ log2 ((2 : ℝ) ^ (168 : ℝ)) := log2_mono htotpos hhigh
    _ = 168 := log2_two_rpow 168

/-- If the SHA3-256 cycle estimate lies between `2 ^ 146.4` and `2 ^ 146.6`, its total cost lies
between `2 ^ 166` and `2 ^ 168`, with overhead between 4.7 and 5.0. These conditional bounds
bracket the magnitude reported in [AmyEtAl2017]. -/
theorem sha3_256_reported_magnitude (tDepth : ℝ)
    (hlo : (2 : ℝ) ^ (146.4 : ℝ) ≤ sha3_256Cycles tDepth)
    (hhi : sha3_256Cycles tDepth ≤ (2 : ℝ) ^ (146.6 : ℝ)) :
    (2 : ℝ) ^ (166 : ℝ) ≤ sha3_256Total tDepth ∧
      sha3_256Total tDepth ≤ (2 : ℝ) ^ (168 : ℝ) ∧
      4.7 ≤ overhead (sha3_256Total tDepth) 128 ∧
      overhead (sha3_256Total tDepth) 128 ≤ 5.0 := by
  refine ⟨sha3_256_total_lower tDepth hlo, sha3_256_total_upper tDepth hlo hhi, ?_, ?_⟩
  · rw [sha3_256_overhead_eq]
    have h := sha3_256_log_lower tDepth hlo
    have : (4.7 : ℝ) ≤ ((166 : ℝ) - 128) / 8 := by norm_num
    linarith
  · rw [sha3_256_overhead_eq]
    have h := sha3_256_log_upper tDepth hlo hhi
    have : ((168 : ℝ) - 128) / 8 ≤ (5.0 : ℝ) := by norm_num
    linarith

end Qatlib.Papers.QPreimage16.ConditionalCost
