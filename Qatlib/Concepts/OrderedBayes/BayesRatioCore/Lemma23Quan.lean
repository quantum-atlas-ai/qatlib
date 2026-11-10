/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma23Stat
set_option warningAsError false

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma23Quan

open scoped BigOperators NNReal ENNReal
open Qatlib.Concepts.OrderedBayes.BayesRatioCore

private theorem prefix_probability {n : ℕ} (a : Fin n → ℝ) (i : Fin n)
    (ha : ∀ j, 0 ≤ a j) (hsum : ∑ j, a j = 1) :
    0 ≤ prefixMass a i ∧ prefixMass a i ≤ 1 := by
  constructor
  · apply Finset.sum_nonneg
    intro j _hj
    (try dsimp [prefixMass])
    split_ifs
    · exact ha j
    · exact le_rfl
  · rw [← hsum]
    apply Finset.sum_le_sum
    intro j _hj
    by_cases h : j.val ≤ i.val <;> simp [h, ha j]

theorem zoo_bayes_answer_probabilities {n : ℕ} (a : Fin n → ℝ) (i : Fin n) (p : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hsum : ∑ j, a j = 1) (hp : 1 / 2 < p) (hp1 : p < 1) :
    0 < normFalse a i p ∧ 0 < normTrue a i p ∧ normFalse a i p + normTrue a i p = 1 := by
  obtain ⟨hq0, hq1⟩ := prefix_probability a i ha hsum
  have hfactor : 0 ≤ 2 * p - 1 := by linarith
  have hq : 0 ≤ (2 * p - 1) * prefixMass a i := mul_nonneg hfactor hq0
  have hqc : 0 ≤ (2 * p - 1) * (1 - prefixMass a i) :=
    mul_nonneg hfactor (sub_nonneg.mpr hq1)
  unfold normTrue normFalse
  constructor
  · nlinarith
  constructor
  · nlinarith
  · ring

private theorem false_weight_sum {n : ℕ} (a : Fin n → ℝ) (i : Fin n) (p : ℝ)
    (hsum : ∑ j, a j = 1) :
    (∑ j, if j.val ≤ i.val then p * a j else (1 - p) * a j) = normFalse a i p := by
  have heq (j : Fin n) : (if j.val ≤ i.val then p * a j else (1 - p) * a j) =
      (1 - p) * a j + (2 * p - 1) * (if j.val ≤ i.val then a j else 0) := by
    split_ifs <;> ring
  simp_rw [heq]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum]
  change (1 - p) * 1 + (2 * p - 1) * prefixMass a i = _
  unfold normFalse
  ring

private theorem true_weight_sum {n : ℕ} (a : Fin n → ℝ) (i : Fin n) (p : ℝ)
    (hsum : ∑ j, a j = 1) :
    (∑ j, if j.val ≤ i.val then (1 - p) * a j else p * a j) = normTrue a i p := by
  have heq (j : Fin n) : (if j.val ≤ i.val then (1 - p) * a j else p * a j) =
      p * a j + (1 - 2 * p) * (if j.val ≤ i.val then a j else 0) := by
    split_ifs <;> ring
  simp_rw [heq]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum]
  change p * 1 + (1 - 2 * p) * prefixMass a i = _
  unfold normTrue normFalse
  ring

theorem zoo_bayes_posterior_invariants {n : ℕ} (a : Fin n → ℝ) (i : Fin n) (p : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hsum : ∑ j, a j = 1) (hp : 1 / 2 < p) (hp1 : p < 1) :
    (∀ j, 0 ≤ updateFalse a i p j) ∧ (∑ j, updateFalse a i p j) = 1 ∧
    (∀ j, 0 ≤ updateTrue a i p j) ∧ (∑ j, updateTrue a i p j) = 1 := by
  obtain ⟨hF, hT, _⟩ := zoo_bayes_answer_probabilities a i p ha hsum hp hp1
  have hp0 : 0 < p := by linarith
  have hpc : 0 < 1 - p := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    unfold updateFalse
    split_ifs
    · exact div_nonneg (mul_nonneg hp0.le (ha j)) hF.le
    · exact div_nonneg (mul_nonneg hpc.le (ha j)) hF.le
  · simp only [updateFalse, ← Finset.sum_div]
    rw [false_weight_sum a i p hsum, div_self hF.ne']
  · intro j
    unfold updateTrue
    split_ifs
    · exact div_nonneg (mul_nonneg hpc.le (ha j)) hT.le
    · exact div_nonneg (mul_nonneg hp0.le (ha j)) hT.le
  · simp only [updateTrue, ← Finset.sum_div]
    rw [true_weight_sum a i p hsum, div_self hT.ne']

theorem zoo_bayes_entropy_nonnegative {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hsum : ∑ j, a j = 1) : 0 ≤ entropy a := by
  have hj1 (j : Fin n) : a j ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun i _hi => ha i) (Finset.mem_univ j)
  unfold entropy
  apply neg_nonneg.mpr
  apply Finset.sum_nonpos
  intro j _hj
  exact mul_nonpos_of_nonneg_of_nonpos (ha j)
    (div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos (ha j) (hj1 j))
      (Real.log_pos (by norm_num)).le)

theorem zoo_bayes_answer_clamp {n : ℕ} (a : Fin n → ℝ) (i : Fin n) (p : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hsum : ∑ j, a j = 1) (hp : 1 / 2 < p) (hp1 : p < 1) :
    ((clampProb (normTrue a i p) : ℝ≥0) : ℝ) = normTrue a i p := by
  obtain ⟨hF, hT, heq⟩ := zoo_bayes_answer_probabilities a i p ha hsum hp hp1
  have hT1 : normTrue a i p ≤ 1 := by linarith
  change max 0 (min (normTrue a i p) 1) = normTrue a i p
  rw [min_eq_left hT1, max_eq_right hT.le]

private theorem weighted_entropy_update {n : ℕ} (a c : Fin n → ℝ) (d : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hc : ∀ j, 0 < c j) (hd : 0 < d) :
    d * entropy (fun j => c j * a j / d) =
      -(∑ j, c j * a j *
        (Real.log (c j) / Real.log 2 + Real.log (a j) / Real.log 2 - Real.log d / Real.log 2)) := by
  unfold entropy
  rw [mul_neg, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _hj
  rcases eq_or_lt_of_le (ha j) with hz | hx
  · simp [← hz]
  · rw [Real.log_div (mul_ne_zero (hc j).ne' hx.ne') hd.ne',
      Real.log_mul (hc j).ne' hx.ne']
    field_simp [hd.ne', (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']

theorem zoo_bayes_expected_info_identity {n : ℕ} (a : Fin n → ℝ) (i : Fin n) (p : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hsum : ∑ j, a j = 1) (hp : 1 / 2 < p) (hp1 : p < 1) :
    normFalse a i p * (postInfo (updateFalse a i p) - postInfo a) +
      normTrue a i p * (postInfo (updateTrue a i p) - postInfo a) =
        binEntropy (normFalse a i p) - binEntropy p := by
  obtain ⟨hF, hT, _⟩ := zoo_bayes_answer_probabilities a i p ha hsum hp hp1
  let cF : Fin n → ℝ := fun j => if j.val ≤ i.val then p else 1 - p
  let cT : Fin n → ℝ := fun j => if j.val ≤ i.val then 1 - p else p
  have hcF : ∀ j, 0 < cF j := by intro j; dsimp [cF]; split_ifs <;> linarith
  have hcT : ∀ j, 0 < cT j := by intro j; dsimp [cT]; split_ifs <;> linarith
  have hUF : updateFalse a i p = fun j => cF j * a j / normFalse a i p := by
    ext j
    dsimp [updateFalse, cF]
    split_ifs <;> rfl
  have hUT : updateTrue a i p = fun j => cT j * a j / normTrue a i p := by
    ext j
    dsimp [updateTrue, cT]
    split_ifs <;> rfl
  have hFs : ∑ j, cF j * a j = normFalse a i p := by
    simpa [cF, ite_mul] using false_weight_sum a i p hsum
  have hTs : ∑ j, cT j * a j = normTrue a i p := by
    simpa [cT, ite_mul] using true_weight_sum a i p hsum
  have hrow (j : Fin n) :
      cF j * a j * (Real.log (cF j) / Real.log 2 + Real.log (a j) / Real.log 2 -
          Real.log (normFalse a i p) / Real.log 2) +
        cT j * a j * (Real.log (cT j) / Real.log 2 + Real.log (a j) / Real.log 2 -
          Real.log (normTrue a i p) / Real.log 2) =
      a j * (Real.log (a j) / Real.log 2) +
        a j * (p * (Real.log p / Real.log 2) + (1 - p) * (Real.log (1 - p) / Real.log 2)) -
        (cF j * a j) * (Real.log (normFalse a i p) / Real.log 2) -
        (cT j * a j) * (Real.log (normTrue a i p) / Real.log 2) := by
    dsimp [cF, cT]
    split_ifs <;> ring
  have hraw : normFalse a i p * entropy (updateFalse a i p) +
      normTrue a i p * entropy (updateTrue a i p) =
        entropy a + binEntropy p - binEntropy (normFalse a i p) := by
    rw [hUF, hUT, weighted_entropy_update a cF _ ha hcF hF,
      weighted_entropy_update a cT _ ha hcT hT, ← neg_add, ← Finset.sum_add_distrib]
    simp_rw [hrow]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, hsum, hFs, hTs]
    unfold entropy binEntropy
    rw [show normTrue a i p = 1 - normFalse a i p from rfl]
    ring
  unfold postInfo
  rw [show normTrue a i p = 1 - normFalse a i p from rfl] at hraw ⊢
  linear_combination -hraw

theorem zoo_bayes_queryInfo_natural (p : ℝ) :
    queryInfo p = 1 - Real.binEntropy p / Real.log 2 := by
  simp only [queryInfo, binEntropy, Real.binEntropy, Real.log_inv]
  ring

private noncomputable def infoCorrection (c x : ℝ) : ℝ :=
  1 - Real.binEntropy x / Real.log 2 - c * (x - 1 / 2)^2

private noncomputable def infoCorrectionD (c x : ℝ) : ℝ :=
  (Real.log x - Real.log (1 - x)) / Real.log 2 - 2 * c * (x - 1 / 2)

private noncomputable def infoCorrectionDD (c x : ℝ) : ℝ :=
  1 / (x * (1 - x) * Real.log 2) - 2 * c

private theorem correction_deriv (c x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt (infoCorrection c) (infoCorrectionD c x) x := by
  have h := ((hasDerivAt_const x (1 : ℝ)).sub
    ((Real.hasDerivAt_binEntropy hx.ne' (ne_of_lt hx1)).div_const (Real.log 2))).sub
      ((((hasDerivAt_id x).sub_const (1 / 2)).pow 2).const_mul c)
  convert! h using 1
  (try dsimp [infoCorrectionD])
  ring

private theorem correction_second_deriv (c x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt (infoCorrectionD c) (infoCorrectionDD c x) x := by
  have hlog := Real.hasDerivAt_log hx.ne'
  have hlogc := (Real.hasDerivAt_log (sub_pos.mpr hx1).ne').comp x
    ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x))
  have h := ((hlog.sub hlogc).div_const (Real.log 2)).sub
    (((hasDerivAt_id x).sub_const (1 / 2)).const_mul (2 * c))
  convert! h using 1
  (try dsimp [infoCorrectionDD])
  field_simp [hx.ne', (sub_pos.mpr hx1).ne',
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  ring

private theorem correction_half (c : ℝ) : infoCorrection c (1 / 2) = 0 := by
  simp [infoCorrection, (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']

private theorem correction_half_deriv (c : ℝ) : HasDerivAt (infoCorrection c) 0 (1 / 2) := by
  have hh : infoCorrectionD c (1 / 2) = 0 := by
    dsimp only [infoCorrectionD]
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
    simp
  have h := correction_deriv c (1 / 2) (by norm_num) (by norm_num)
  rw [hh] at h
  exact h

theorem zoo_bayes_queryInfo_quadratic_lower {p : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) :
    2 * (p - 1 / 2)^2 ≤ queryInfo p := by
  have hcv : ConvexOn ℝ (Set.Icc (1 / 2 : ℝ) 1) (infoCorrection 2) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (f' := infoCorrectionD 2) (f'' := infoCorrectionDD 2)
    · unfold infoCorrection
      fun_prop
    · intro x hx
      simp only [interior_Icc, Set.mem_Ioo] at hx
      exact (correction_deriv 2 x (by linarith) hx.2).hasDerivWithinAt
    · intro x hx
      simp only [interior_Icc, Set.mem_Ioo] at hx
      exact (correction_second_deriv 2 x (by linarith) hx.2).hasDerivWithinAt
    · intro x hx
      simp only [interior_Icc, Set.mem_Ioo] at hx
      have hxx : 0 < x * (1 - x) := mul_pos (by linarith) (by linarith)
      have hprod : x * (1 - x) * Real.log 2 ≤ 1 / 4 := by
        have hlog : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
        have hm := mul_le_mul_of_nonneg_left hlog hxx.le
        nlinarith [sq_nonneg (x - 1 / 2)]
      have hd : 0 < x * (1 - x) * Real.log 2 := mul_pos hxx (Real.log_pos (by norm_num))
      unfold infoCorrectionDD
      apply sub_nonneg.mpr
      apply (le_div_iff₀ hd).2
      nlinarith
  have hs := hcv.le_slope_of_hasDerivAt (by norm_num) ⟨hp.le, hp1.le⟩ hp (correction_half_deriv 2)
  rw [slope_def_field, correction_half, sub_zero] at hs
  have hf : 0 ≤ infoCorrection 2 p := by
    have h := (le_div_iff₀ (show 0 < p - 1 / 2 by linarith)).mp hs
    simpa using h
  rw [zoo_bayes_queryInfo_natural]
  dsimp [infoCorrection] at hf
  linarith

theorem zoo_bayes_queryInfo_quadratic_upper {p : ℝ}
    (hp : 1 / 4 ≤ p) (hp1 : p ≤ 1 / 2) : queryInfo p ≤ 4 * (p - 1 / 2)^2 := by
  have hcc : ConcaveOn ℝ (Set.Icc (1 / 4 : ℝ) (1 / 2)) (infoCorrection 4) := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
      (f' := infoCorrectionD 4) (f'' := infoCorrectionDD 4)
    · unfold infoCorrection
      fun_prop
    · intro x hx
      simp only [interior_Icc, Set.mem_Ioo] at hx
      exact (correction_deriv 4 x (by linarith) (by linarith)).hasDerivWithinAt
    · intro x hx
      simp only [interior_Icc, Set.mem_Ioo] at hx
      exact (correction_second_deriv 4 x (by linarith) (by linarith)).hasDerivWithinAt
    · intro x hx
      simp only [interior_Icc, Set.mem_Ioo] at hx
      have hxx : 0 < x * (1 - x) := mul_pos (by linarith) (by linarith)
      have hprod : 1 / 8 ≤ x * (1 - x) * Real.log 2 := by
        have hlog : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
        have hm := mul_le_mul_of_nonneg_left hlog hxx.le
        have haux := mul_nonneg (show 0 ≤ x - 1 / 4 by linarith)
          (show 0 ≤ 3 / 4 - x by linarith)
        nlinarith
      have hd : 0 < x * (1 - x) * Real.log 2 := mul_pos hxx (Real.log_pos (by norm_num))
      unfold infoCorrectionDD
      apply sub_nonpos.mpr
      apply (div_le_iff₀ hd).2
      nlinarith
  have hf : infoCorrection 4 p ≤ 0 := by
    rcases eq_or_lt_of_le hp1 with heq | hlt
    · rw [heq, correction_half]
    · have hs := hcc.le_slope_of_hasDerivAt ⟨hp, hp1⟩ (by norm_num) hlt (correction_half_deriv 4)
      rw [slope_def_field, correction_half, zero_sub] at hs
      have h := (le_div_iff₀ (show 0 < 1 / 2 - p by linarith)).mp hs
      linarith
  rw [zoo_bayes_queryInfo_natural]
  dsimp [infoCorrection] at hf
  linarith

theorem zoo_bayes_expected_info_rise : Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma2_3 := by
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
  have hpinsker := zoo_bayes_queryInfo_quadratic_lower hp hp1
  have hp2 : (2 * p - 1)^2 ≤ 2 * queryInfo p := by nlinarith
  have hdeficit : queryInfo F ≤ queryInfo p / (3 * L) := by
    calc
      _ ≤ 4 * (F - 1 / 2)^2 := zoo_bayes_queryInfo_quadratic_upper hFlo hFhi
      _ ≤ 4 * ((2 * p - 1)^2 * ε^2) := by gcongr
      _ ≤ 4 * ((2 * p - 1)^2 * (1 / (24 * L))) := by gcongr
      _ = (2 * p - 1)^2 / (6 * L) := by field_simp; ring
      _ ≤ (2 * queryInfo p) / (6 * L) := div_le_div_of_nonneg_right hp2 (by positivity)
      _ = queryInfo p / (3 * L) := by field_simp; ring
  rw [zoo_bayes_expected_info_identity a i p ha hsum hp hp1]
  change queryInfo p * (1 - 1 / (3 * L)) ≤ _
  rw [div_eq_mul_inv] at hdeficit
  unfold queryInfo at hdeficit ⊢
  dsimp only [F] at hdeficit
  simp only [one_div]
  nlinarith

end Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma23Quan
