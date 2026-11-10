/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.CountedWalk.CountedSzegedyAccess
import Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointWord
import Qatlib.Concepts.QueryWordCore.AdjointCircuits
import Qatlib.Papers.ClawFinding07.MainResults.QueryBound.CostDefs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ClawFinding07.MainResults.QueryBound

open Qatlib.Concepts.WalkSearch.CountedWalk
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open scoped BigOperators

theorem countedSzegedy_step_queries {I : Type*} [Fintype I] [DecidableEq I]
    (j : I) : adjointQueryCount (countedSzegedyWord j) = 4 :=
  (counted_szegedy_actual_word_and_counts j).2.1

theorem countedSzegedy_repeat_queries {I : Type*} [Fintype I] [DecidableEq I]
    (j : I) (T : ℕ) :
    adjointQueryCount ((List.replicate T (countedSzegedyWord j)).flatten) = 4 * T := by
  induction T with
  | zero => simp [adjointQueryCount]
  | succ T ih =>
      rw [List.replicate_succ, List.flatten_cons, adjointQueryCount_append, ih,
        countedSzegedy_step_queries]
      ring

theorem countedSzegedy_query_le_cost {CU δ ε : ℝ} (T : ℕ)
    (hCU : 0 ≤ CU) (hδε : 0 < δ * ε)
    (hT : (T : ℝ) ≤ 1 / Real.sqrt (δ * ε) + 1) :
    CU + 4 * (T : ℝ) ≤ 4 * szegedyCost CU 0 1 δ ε + 4 := by
  have hcost : szegedyCost CU 0 1 δ ε = CU + 1 / Real.sqrt (δ * ε) := by
    simp only [szegedyCost, zero_add]
  rw [hcost]
  nlinarith [hCU, hT]

end Qatlib.Papers.ClawFinding07.MainResults.QueryBound
