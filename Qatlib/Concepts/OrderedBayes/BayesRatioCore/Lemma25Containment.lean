/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.BayesTruthDefs
import Qatlib.Concepts.OrderedBayes.BayesRatioCore.BayesTruthRatioCrossingRightQuan
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs
set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

theorem nonuniform_initial_ratio :
    ∃ a : Fin 3 → ℝ, (∀ m, 0 < a m) ∧ (∑ m, a m) = 1 ∧ 1 < a 2 / a 1 := by
  refine ⟨fun m => if m.val = 2 then 4 / 5 else 1 / 10, ?_, ?_, ?_⟩
  · intro m
    (try dsimp only)
    split_ifs <;> norm_num
  · norm_num [Fin.sum_univ_succ]
  · norm_num

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
