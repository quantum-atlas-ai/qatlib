/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.Theorem1DenseStat
import Qatlib.Concepts.WalkSearch.Primitives.TriangleSearchCorrectedDefinitions
import Qatlib.Concepts.WalkSearch.MainResults.Theorem1Quan
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.WalkSearch.Primitives

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.WalkSearch.MainResults

theorem dense_source_four_terms (n : ℕ) (hn : 1≤n) :
    sourceFourTermBudget n (3/7) (1/7) (1/7)≤4*(n:ℝ)^(10/7:ℝ) := source_dense_four_term_budget n hn
open scoped Classical
set_option warningAsError false

theorem theorem1Dense_answer : Theorem1Dense := by
  intro n hn G family ets hfamily hets k K c dHi dLo τ tThin sgs hk hc hdLo
  have hh := theorem1_answer n (3/7) (1/7) (1/7) hn (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) G family ets hfamily hets
  (try dsimp only at hh)
  norm_num only [sourceSearchExecution,show (1:ℝ)-1/7=6/7 by norm_num,show (1:ℝ)-3/7=4/7 by norm_num] at hh
  have hfull := hh hk hc hdLo
  have hsgs : sourceSearchExecution family n (Nat.ceil ((n:ℝ)^(1-1/7:ℝ))) = sgs := by
    dsimp only [sgs,τ]
    congr 1
    norm_num
  rw [hsgs] at hfull
  refine ⟨hfull.1,hfull.2.1,?_⟩
  intro t
  have hcost := hfull.2.2 t
  exact hcost.trans
      (mul_le_mul_of_nonneg_left (dense_source_four_terms n (by omega)) (by positivity))

end Qatlib.Concepts.WalkSearch.MainResults
