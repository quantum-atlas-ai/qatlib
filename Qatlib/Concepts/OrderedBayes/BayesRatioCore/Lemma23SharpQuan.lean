/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma23SharpStat
import Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma23Quan
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma23Quan

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

theorem lemma2_3Sharp_answer : Lemma2_3Sharp := by
  intro n a i p ε hn hp hp1 hε hcap ha hsum hqlo hqhi
  let L : ℝ := Real.log n / Real.log 2
  let q := prefixMass a i
  let F := normFalse a i p
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 1 ≤ L := by
    apply (one_le_div hlog2).2
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hL0 : 0 < L := by linarith
  have hsqrt := Real.sq_sqrt (by positivity : 0 ≤ 1 / (24 * L))
  have hεsq : ε^2 ≤ 1 / (24 * L) := by
    nlinarith [Real.sqrt_nonneg (1 / (24 * L))]
  have hcap24 : 1 / (24 * L) ≤ (1 / 24 : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 24 * L)).2
    nlinarith
  have hεquarter : ε ≤ 1 / 4 := by nlinarith
  have hs0 : 0 ≤ 2 * p - 1 := by linarith
  have hsq : (q - 1 / 2)^2 ≤ ε^2 := by
    change 1 / 2 - ε ≤ q at hqlo
    change q < 1 / 2 at hqhi
    nlinarith
  have hF : F - 1 / 2 = (2 * p - 1) * (q - 1 / 2) := by dsimp [F, normFalse, q]; ring
  have hFhi : F ≤ 1 / 2 := by
    have hm := mul_nonneg hs0 (show 0 ≤ 1 / 2 - q by linarith)
    nlinarith
  have hFlo : 1 / 4 ≤ F := by
    have hm := mul_le_mul_of_nonneg_right (show 2 * p - 1 ≤ 1 by linarith)
      (show 0 ≤ 1 / 2 - q by linarith)
    nlinarith
  have hFp : (F - 1 / 2)^2 ≤ (2 * p - 1)^2 * ε^2 := by
    rw [hF, mul_pow]
    exact mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
  have hdeficit : queryInfo F ≤ 4 * ε ^ 2 * (1 - 2 * p) ^ 2 := by
    have hu := zoo_bayes_queryInfo_quadratic_upper hFlo hFhi
    nlinarith
  rw [zoo_bayes_expected_info_identity a i p ha hsum hp hp1]
  unfold queryInfo at hdeficit ⊢
  dsimp only [F] at hdeficit
  nlinarith

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
