/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.CountedWalk.CountedSzegedyAccess
import Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointWord
import Qatlib.Concepts.QueryWordCore.AdjointCircuits
import Qatlib.Papers.ClawFinding07.MainResults.QueryBound.CostDefs

/-!
# Counted Szegedy walk costs

This module connects the adjoint-query count of `countedSzegedyWord` with the scalar detection
cost expression `szegedyCost` used for the walk analysis in [Tani2009]. A step uses four counted
queries, and a repetition bound controls the resulting finite word cost.

## Main statements

* `countedSzegedy_step_queries`: four queries per walk word.
* `countedSzegedy_repeat_queries`: exact query count for a repeated word.
* `countedSzegedy_query_le_cost`: comparison with the Szegedy cost expression.

## References

* [Tani, 2009][Tani2009]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ClawFinding07.MainResults.QueryBound

open Qatlib.Concepts.WalkSearch.CountedWalk
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open scoped BigOperators

/-- One `countedSzegedyWord` contains exactly four adjoint-counted queries. -/
theorem countedSzegedy_step_queries {I : Type*} [Fintype I] [DecidableEq I]
    (j : I) : adjointQueryCount (countedSzegedyWord j) = 4 :=
  (counted_szegedy_actual_word_and_counts j).2.1

/-- Repeating and flattening the counted Szegedy word `T` times gives exactly `4*T`
adjoint-counted queries; see [Tani2009]. -/
theorem countedSzegedy_repeat_queries {I : Type*} [Fintype I] [DecidableEq I]
    (j : I) (T : ℕ) :
    adjointQueryCount ((List.replicate T (countedSzegedyWord j)).flatten) = 4 * T := by
  induction T with
  | zero => simp [adjointQueryCount]
  | succ T ih =>
      rw [List.replicate_succ, List.flatten_cons, adjointQueryCount_append, ih,
        countedSzegedy_step_queries]
      ring

/-- If `CU ≥ 0`, `δ*ε > 0`, and `T ≤ 1/sqrt (δ*ε)+1`, then `CU+4*T` is at most `4*szegedyCost CU
0 1 δ ε+4`; see [Tani2009]. -/
theorem countedSzegedy_query_le_cost {CU δ ε : ℝ} (T : ℕ)
    (hCU : 0 ≤ CU) (hδε : 0 < δ * ε)
    (hT : (T : ℝ) ≤ 1 / Real.sqrt (δ * ε) + 1) :
    CU + 4 * (T : ℝ) ≤ 4 * szegedyCost CU 0 1 δ ε + 4 := by
  have hcost : szegedyCost CU 0 1 δ ε = CU + 1 / Real.sqrt (δ * ε) := by
    simp only [szegedyCost, zero_add]
  rw [hcost]
  nlinarith [hCU, hT]

end Qatlib.Papers.ClawFinding07.MainResults.QueryBound
