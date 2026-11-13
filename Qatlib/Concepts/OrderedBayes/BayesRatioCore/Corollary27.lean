/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
import Qatlib.Concepts.OrderedBayes.BayesRatioCore.ClassicalInfoLowerBound
import Mathlib.Tactic.NormNum

/-!
# Obstruction to a pointwise ordered search lower bound

This module proves `corollary2_7_obstruction`, the negation of `Corollary2_7Contract`, in the
ordered search setting of [BenOrHassidim2007]. A deterministic three-cell query tree has perfect
identification on comparison oracles but uses one query on the constant-false oracle,
contradicting the contract's universally quantified expected-query bound.

## Main statements

* `corollary2_7_obstruction`: the specified conjunction of query lower bounds cannot hold.

## References

* [Ben-Or and Hassidim, 2007][BenOrHassidim2007]
-/

set_option autoImplicit false
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore
open Qatlib

/-- The formal proposition `Corollary2_7Contract` is false, as witnessed by a three-cell query
tree evaluated on the constant-false oracle. -/
theorem corollary2_7_obstruction : ¬ Corollary2_7Contract := by
  intro h
  have hs : ∀ j : Fin 3, ENNReal.ofReal (1 - (0 : ℝ)) ≤
      Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb (PMF.pure threeCellTree) (fun c => c ≤ j) (fun out => out = j) := by
    intro j
    rw [threeCellTree_success]
    norm_num
  have hb := (h 3 0 (PMF.pure threeCellTree) (fun _ => false)
    (by decide) (by norm_num) (by norm_num) hs).1
  rw [threeCellTree_cost] at hb
  norm_num at hb
  have hb' : ENNReal.ofReal (Real.log 3 / Real.log 2) ≤ ENNReal.ofReal 1 := by
    simpa using hb
  have hr := (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 1)).mp hb'
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have ht := (div_le_iff₀ hl2).mp hr
  norm_num at ht
  exact (not_le_of_gt hl3) ht

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
