/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
import Mathlib.Tactic.FinCases
import Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma23Quan
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma23Quan
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore
open Qatlib

def threeCellTree : BoolQueryTree (Fin 3) (Fin 3) :=
  .ask 1 (.halt 0) (.ask 2 (.halt 1) (.halt 2))

theorem threeCellTree_success (j : Fin 3) :
    Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb (PMF.pure threeCellTree) (fun c => c ≤ j) (fun out => out = j) = 1 := by
  classical
  simp only [Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb,
      PMF.pure_apply, ite_mul, one_mul, zero_mul, tsum_ite_eq]
  have hrun : (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run (fun c => c ≤ j) threeCellTree).1 = j := by
    fin_cases j <;> rfl
  simp only [hrun, ite_true]

theorem threeCellTree_cost :
    Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.ExpectedQueries (PMF.pure threeCellTree) (fun _ => false) = 1 := by
  classical
  simp [Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.ExpectedQueries, PMF.pure_apply,
      threeCellTree, Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run]

theorem classicalInfoLowerBound_obstruction : ¬ ClassicalInfoLowerBoundContract := by
  intro h
  have hI : 0 < queryInfo (3 / 4) := by
    have hi := zoo_bayes_queryInfo_quadratic_lower (by norm_num : (1 / 2 : ℝ) < 3 / 4)
      (by norm_num : (3 / 4 : ℝ) < 1)
    norm_num at hi
    linarith
  have hI1 : queryInfo (3 / 4) < 1 := by
    rw [zoo_bayes_queryInfo_natural]
    have hh := Real.binEntropy_pos (by norm_num : (0 : ℝ) < 3 / 4)
      (by norm_num : (3 / 4 : ℝ) < 1)
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hd := div_pos hh hl2
    linarith
  have hs : ∀ j : Fin 3, ENNReal.ofReal (1 - (0 : ℝ)) ≤
      Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb (PMF.pure threeCellTree) (fun c => c ≤ j) (fun out => out = j) := by
    intro j
    rw [threeCellTree_success]
    norm_num
  have hb := h.1 3 0 (3 / 4) (PMF.pure threeCellTree) (fun _ => false)
    (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hI hs
  rw [threeCellTree_cost] at hb
  norm_num [binEntropy] at hb
  have hb' : ENNReal.ofReal ((Real.log 3 / Real.log 2) / queryInfo (3 / 4)) ≤ ENNReal.ofReal 1 := by
    simpa using hb
  have hr := (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 1)).mp hb'
  have ht := (div_le_iff₀ hI).mp hr
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have hL : 1 < Real.log 3 / Real.log 2 := (one_lt_div hl2).mpr hl3
  nlinarith

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
