/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
import Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma23Quan
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma23Quan

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore
open Qatlib

theorem recursiveRecoveryCost_obstruction : ¬ RecursiveRecoveryCostContract := by
  intro h
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hL : Real.log (16 : ℝ) / Real.log 2 = 4 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    field_simp
    norm_num
  have hcap : (1 / 10 : ℝ) ≤ Real.sqrt (1 / (24 * (Real.log (16 : ℝ) / Real.log 2))) := by
    rw [hL]
    apply (Real.le_sqrt (by norm_num) (by norm_num)).mpr
    norm_num
  have hI : 0 < queryInfo (3 / 4) := by
    have hi := zoo_bayes_queryInfo_quadratic_lower (by norm_num : (1 / 2 : ℝ) < 3 / 4)
      (by norm_num : (3 / 4 : ℝ) < 1)
    norm_num at hi
    linarith
  have hs := (h 16 (by decide) 0 (3 / 4) (1 / 10) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hcap (by norm_num) hI).1 0
  simp [runCostedFor, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_ret] at hs
  norm_num at hs

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
