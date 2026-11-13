/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Information-rate bounds for greedy ordered search

Certifies the exact information value and the resulting six-query rate used in the greedy
ordered-search comparison of [BenOrHassidim2007]. The arithmetic gives rate `32 / 99`, proves it
is below `1 / 3`, and compares it with the printed decimal value 0.32.

## Main statements

* `source_theorem1_2_query_complexity`: bounds the query expression when the information
  parameter is at least `fggsInfo`.

## References

* [Ben-Or and Hassidim, 2007][BenOrHassidim2007]
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.OrderedBayes.BayesRatioCore
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels.OrderedSearch2007

namespace Qatlib.Papers.OrderedList07.MainResults

/-- The greedy-search information quantity `fggsInfo` equals `297 / 16` [BenOrHassidim2007]. -/
theorem source_theorem1_2_greedy_info_certificate : fggsInfo = 297 / 16 := rfl

/-- The ratio of six queries to `fggsInfo` is `32 / 99`. -/
theorem source_theorem1_2_six_queries_per_unit_info : (6 : ℝ) / fggsInfo = 32 / 99 := by
  rw [source_theorem1_2_greedy_info_certificate]
  norm_num

/-- The ratio `6 / fggsInfo` is strictly less than one third [BenOrHassidim2007]. -/
theorem source_theorem1_2_rate_below_one_third : (6 : ℝ) / fggsInfo < 1 / 3 := by
  rw [source_theorem1_2_six_queries_per_unit_info]
  norm_num

/-- The printed value `32 / 100` is strictly smaller than `6 / fggsInfo` [BenOrHassidim2007]. -/
theorem source_theorem1_2_printed_032_refuted : (32 : ℝ) / 100 < 6 / fggsInfo := by
  rw [source_theorem1_2_six_queries_per_unit_info]
  norm_num

/-- For `n ≥ 16` and `Ir ≥ fggsInfo`, the query expression `6 * log₂ n / Ir` is strictly less
than `log₂ n / 3` [BenOrHassidim2007]. -/
theorem source_theorem1_2_query_complexity
    (n : ℕ) (hn : 16 ≤ n) (Ir : ℝ) (hIr : fggsInfo ≤ Ir) :
    6 * (Real.log n / Real.log 2) / Ir < (Real.log n / Real.log 2) / 3 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hIpos : 0 < fggsInfo := by
    rw [source_theorem1_2_greedy_info_certificate]
    norm_num
  have hIrpos : 0 < Ir := lt_of_lt_of_le hIpos hIr
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hL : 0 < Real.log n / Real.log 2 := div_pos hlog h2
  have hrate : (6 : ℝ) / Ir ≤ 32 / 99 := by
    have hmono : (6 : ℝ) / Ir ≤ 6 / fggsInfo :=
      div_le_div_of_nonneg_left (by norm_num) hIpos hIr
    rw [source_theorem1_2_six_queries_per_unit_info] at hmono
    exact hmono
  have hstep : 6 * (Real.log n / Real.log 2) / Ir
      = ((6 : ℝ) / Ir) * (Real.log n / Real.log 2) := by ring
  have hbound : ((6 : ℝ) / Ir) * (Real.log n / Real.log 2)
      ≤ (32 / 99) * (Real.log n / Real.log 2) :=
    mul_le_mul_of_nonneg_right hrate hL.le
  have hlt : (32 / 99 : ℝ) * (Real.log n / Real.log 2)
      < (1 / 3) * (Real.log n / Real.log 2) := by
    apply mul_lt_mul_of_pos_right _ hL
    norm_num
  have hthird : (1 / 3 : ℝ) * (Real.log n / Real.log 2) = (Real.log n / Real.log 2) / 3 := by
    ring
  linarith [hstep, hbound, hlt, hthird]

end Qatlib.Papers.OrderedList07.MainResults
