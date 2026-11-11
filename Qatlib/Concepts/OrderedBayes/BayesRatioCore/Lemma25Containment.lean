/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.BayesTruthDefs
import Qatlib.Concepts.OrderedBayes.BayesRatioCore.BayesTruthRatioCrossingRightQuan
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs

/-!
# A nonuniform initial posterior ratio

This module constructs a strictly positive normalized prior on three ordered cells whose mass at
index 2 exceeds its mass at index 1. In the posterior-ratio setting of [BenOrHassidim2007],
`nonuniform_initial_ratio` records that such an initial ratio need not be at most one for a
general prior.

## Main statements

* `nonuniform_initial_ratio`: a positive normalized three-cell prior has `a 2 / a 1 > 1`.

## References

* [Ben-Or and Hassidim, 2007][BenOrHassidim2007]
-/

set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

/-- There exists a strictly positive normalized prior on three cells with the ratio of the
weight at index 2 to that at index 1 strictly greater than one. -/
theorem nonuniform_initial_ratio :
    ∃ a : Fin 3 → ℝ, (∀ m, 0 < a m) ∧ (∑ m, a m) = 1 ∧ 1 < a 2 / a 1 := by
  refine ⟨fun m => if m.val = 2 then 4 / 5 else 1 / 10, ?_, ?_, ?_⟩
  · intro m
    (try dsimp only)
    split_ifs <;> norm_num
  · norm_num [Fin.sum_univ_succ]
  · norm_num

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
