/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Ring
import Qatlib.Concepts.SearchStopping.UnknownCount.Theorem3CorrectedStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeSearch.InterruptMin

namespace Qatlib.Concepts.SearchStopping.UnknownCount
universe u

theorem theorem3Corrected : Theorem3Corrected.{u} := by
  intro I _ _ hN
  (try dsimp only)
  have hsizes := (search_exponential_schedule _ hN).2.1
  refine ⟨?_,?_,?_,search_uniform_timeout hN⟩
  · intro A hA
    have hlaw := search_terminal_law_nonempty A hA
    exact ⟨hlaw.1,hlaw.2,search_terminal_output_nonempty A hA,
      search_terminal_cost_nonempty A hA,search_terminal_boolean_cost A hA,
      search_terminal_source_lookup_cost A hA⟩
  · intro A stage budget
    have hlaw := search_finite_budget_law hN A _ hsizes stage budget
    exact ⟨hlaw.1,hlaw.2,fun i hi => search_finite_budget_no_false_positive hN A _ hsizes stage budget i hi⟩
  · exact search_empty_budget_timeout hN _ hsizes

theorem search_source_strict_scale_counterexample :
    ¬ ((4 : ℝ) / (2 * Real.sqrt ((4-3)*3)) < Real.sqrt (4/3 : ℝ)) := by
  have heq : (4 : ℝ) / (2 * Real.sqrt ((4-3)*3)) = Real.sqrt (4/3 : ℝ) := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
    ring
  rw [heq]
  exact lt_irrefl _

end Qatlib.Concepts.SearchStopping.UnknownCount
