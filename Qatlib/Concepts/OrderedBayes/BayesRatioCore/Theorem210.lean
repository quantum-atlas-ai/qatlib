/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
import Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma23Quan
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma23Quan

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore
open Qatlib

theorem theorem2_10_obstruction : ¬ Theorem2_10Contract := by
  intro h
  let p : Fin 2 → ℝ := fun h => if h = 0 then 3 / 4 else 1 / 4
  have hp : ∀ h, 0 < p h := by intro h; fin_cases h <;> norm_num [p]
  have hs : (∑ h, p h) = 1 := by
    change (∑ h : Fin 2, p h) = 1
    norm_num [p, Fin.sum_univ_two]
  have hl2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hIeq : multiInfo (k := 1) p = queryInfo (3 / 4) := by
    unfold multiInfo
    norm_num only [Nat.cast_one, one_add_one_eq_two]
    change Real.log (2 : ℝ) / Real.log 2 - (∑ h : Fin 2, -(p h * (Real.log (p h) / Real.log 2))) = _
    norm_num [p, Fin.sum_univ_two, queryInfo, binEntropy, hl2]
  have hI : 0 < multiInfo (k := 1) p := by
    rw [hIeq]
    have hi := zoo_bayes_queryInfo_quadratic_lower (by norm_num : (1 / 2 : ℝ) < 3 / 4)
      (by norm_num : (3 / 4 : ℝ) < 1)
    norm_num at hi
    linarith
  have hL : Real.log (16 : ℝ) / Real.log 2 = 4 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    field_simp
    norm_num
  have hsmall : ∀ m : Fin 16, 1 / (16 : ℝ) <
      (1 / (1 : ℝ)) * Real.sqrt (1 / (24 * (Real.log (16 : ℝ) / Real.log 2))) := by
    intro m
    rw [hL]
    simp only [div_self (by norm_num : (1 : ℝ) ≠ 0), one_mul]
    apply (Real.lt_sqrt (by norm_num)).mpr
    norm_num
  have ht := (h 1 16 p (1 / 2) (by decide) (by decide) (by norm_num) (by norm_num) hp hs hI
    (by decide) 0 (fun _ => 1 / 16) (fun _ => 8)
    (by intro m; norm_num) (by norm_num [Finset.sum_const, Finset.card_univ]) (by simpa only [Nat.cast_one, Nat.cast_ofNat] using hsmall)
    (by intro i i' hi; fin_cases i; fin_cases i'; exact False.elim (lt_irrefl _ hi))).1 0
  simp [runCostedFor, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_ret] at ht
  norm_num at ht

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
