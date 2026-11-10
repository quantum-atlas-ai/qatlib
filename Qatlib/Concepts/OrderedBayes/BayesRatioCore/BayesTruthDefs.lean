/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.FiniteStoppingTail
import Qatlib.Concepts.OrderedBayes.BayesRatioCore.BayesLearner
set_option warningAsError false
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped ENNReal NNReal BigOperators Classical

open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

noncomputable def truthAnswerProb {n : ℕ} (j c : Fin n) (p : ℝ) : ℝ≥0 :=
  clampProb (if (c : ℕ) ≤ (j : ℕ) then p else 1 - p)

noncomputable def trueLearnerNext {n : ℕ} (hn : 0 < n) (j : Fin n) (p ε : ℝ) :
    (Fin n → ℝ) → PMF (Configuration (Fin n → ℝ) (Fin n → ℝ)) :=
  fun a =>
    if _h : ∃ i : Fin n, ε ≤ a i then PMF.pure (Sum.inl a)
    else
      (PMF.bernoulli (truthAnswerProb j (stageTwoCut hn a ε) p) (clampProb_le _)).bind
        fun b =>
          PMF.pure (Sum.inr
            (if b then updateTrue a (stageTwoCut hn a ε) p
                  else updateFalse a (stageTwoCut hn a ε) p))

def configPosterior {n : ℕ} (cfg : Configuration (Fin n → ℝ) (Fin n → ℝ)) :
    Fin n → ℝ := Sum.elim id id cfg

noncomputable def crossingAbsorbNext {n : ℕ} (hn : 0 < n) (j : Fin n) (p ε R : ℝ)
    (u v : Fin n) : (Fin n → ℝ) → PMF (Configuration (Fin n → ℝ) (Fin n → ℝ)) :=
  fun a => if R * a v ≤ a u then PMF.pure (Sum.inl a) else trueLearnerNext hn j p ε a

section TruthSemantics

open scoped Classical

theorem clampProb_eq {x : ℝ} (h1 : 0 ≤ x) (h2 : x ≤ 1) : (clampProb x : ℝ) = x := by
  show (NNReal.toReal (clampProb x)) = x
  simp only [clampProb]
  norm_num [min_eq_left h2, max_eq_right h1]
  rfl

theorem clampProb_eq_toNNReal {x : ℝ} (h1 : 0 ≤ x) (h2 : x ≤ 1) :
    clampProb x = Real.toNNReal x := by
  apply NNReal.coe_injective
  show ((clampProb x : ℝ≥0) : ℝ) = ((Real.toNNReal x : ℝ≥0) : ℝ)
  rw [clampProb_eq h1 h2, Real.coe_toNNReal x h1]

theorem zoo_bayes_truth_halt {n : ℕ} (hn : 0 < n) (j : Fin n) (p ε : ℝ) (a : Fin n → ℝ)
    (ha : ∃ i : Fin n, ε ≤ a i) :
    trueLearnerNext hn j p ε a = PMF.pure (Sum.inl a) := by
  simp only [trueLearnerNext, dif_pos ha]

theorem zoo_bayes_truth_norms_positive {n : ℕ} (a : Fin n → ℝ) (c : Fin n) (p : ℝ)
    (hp : 1 / 2 < p) (hp1 : p < 1) (ha0 : ∀ m, 0 ≤ a m) (hsum : (∑ m, a m) ≤ 1) :
    0 < normFalse a c p ∧ normFalse a c p < 1 ∧ 0 < normTrue a c p ∧ normTrue a c p < 1 := by
  have hq0 : 0 ≤ prefixMass a c := Finset.sum_nonneg fun m _ => by
    by_cases hm : (m : ℕ) ≤ (c : ℕ) <;> simp [hm, ha0 m]
  have hqS : prefixMass a c ≤ ∑ m, a m := Finset.sum_le_sum fun m _ => by
    by_cases hm : (m : ℕ) ≤ (c : ℕ) <;> simp [hm, ha0 m]
  have hq1 : prefixMass a c ≤ 1 := hqS.trans hsum
  have hexpF : normFalse a c p = (1 - p) + (2 * p - 1) * prefixMass a c := by
    unfold normFalse; ring
  have h0F : 0 < normFalse a c p := by
    rw [hexpF]
    have hm := mul_nonneg (show (0 : ℝ) ≤ 2 * p - 1 by linarith) hq0
    linarith
  have h1F : normFalse a c p < 1 := by
    rw [hexpF]
    have hm := mul_le_mul_of_nonneg_left hq1 (show (0 : ℝ) ≤ 2 * p - 1 by linarith)
    linarith
  refine ⟨h0F, h1F, ?_, ?_⟩
  · have hT : normTrue a c p = 1 - normFalse a c p := rfl
    rw [hT]; linarith
  · have hT : normTrue a c p = 1 - normFalse a c p := rfl
    rw [hT]; linarith

theorem zoo_bayes_truth_update_positivity {n : ℕ} (a : Fin n → ℝ) (c : Fin n) (p : ℝ)
    (hp : 1 / 2 < p) (hp1 : p < 1) (hpos : ∀ m, 0 < a m) (hsum : (∑ m, a m) ≤ 1) :
    (∀ m, 0 < updateFalse a c p m) ∧ (∀ m, 0 < updateTrue a c p m) := by
  have ha0 : ∀ m, 0 ≤ a m := fun m => le_of_lt (hpos m)
  obtain ⟨hF0, hF1, hT0, hT1⟩ := zoo_bayes_truth_norms_positive a c p hp hp1 ha0 hsum
  refine ⟨fun m => ?_, fun m => ?_⟩
  · simp only [updateFalse]
    by_cases hm : (m : ℕ) ≤ (c : ℕ)
    · rw [if_pos hm]
      exact div_pos (mul_pos (show (0:ℝ) < p by linarith) (hpos m)) hF0
    · rw [if_neg hm]
      exact div_pos (mul_pos (by linarith) (hpos m)) hF0
  · simp only [updateTrue]
    by_cases hm : (m : ℕ) ≤ (c : ℕ)
    · rw [if_pos hm]
      exact div_pos (mul_pos (by linarith) (hpos m)) hT0
    · rw [if_neg hm]
      exact div_pos (mul_pos (show (0:ℝ) < p by linarith) (hpos m)) hT0

theorem zoo_bayes_update_ratio_same_side {n : ℕ} (a : Fin n → ℝ) (c u v : Fin n) (p : ℝ)
    (hside : ((u : ℕ) ≤ (c : ℕ)) = ((v : ℕ) ≤ (c : ℕ))) :
    updateFalse a c p u * a v = updateFalse a c p v * a u ∧
      updateTrue a c p u * a v = updateTrue a c p v * a u := by
  constructor
  · simp only [updateFalse]
    by_cases hu : (u : ℕ) ≤ (c : ℕ)
    · have hv : (v : ℕ) ≤ (c : ℕ) := hside ▸ hu
      rw [if_pos hu, if_pos hv]
      by_cases h : normFalse a c p = 0
      · simp [h]
      · field_simp
    · have hv : ¬ ((v : ℕ) ≤ (c : ℕ)) := fun hcon => hu (hside ▸ hcon)
      rw [if_neg hu, if_neg hv]
      by_cases h : normFalse a c p = 0
      · simp [h]
      · field_simp
  · simp only [updateTrue]
    by_cases hu : (u : ℕ) ≤ (c : ℕ)
    · have hv : (v : ℕ) ≤ (c : ℕ) := hside ▸ hu
      rw [if_pos hu, if_pos hv]
      by_cases h : normTrue a c p = 0
      · simp [h]
      · field_simp
    · have hv : ¬ ((v : ℕ) ≤ (c : ℕ)) := fun hcon => hu (hside ▸ hcon)
      rw [if_neg hu, if_neg hv]
      by_cases h : normTrue a c p = 0
      · simp [h]
      · field_simp

theorem zoo_bayes_update_ratio_across_false {n : ℕ} (a : Fin n → ℝ) (c u v : Fin n) (p : ℝ)
    (hu : (u : ℕ) ≤ (c : ℕ)) (hv : (c : ℕ) < (v : ℕ)) :
    p * (updateFalse a c p v * a u) = (1 - p) * (a v * updateFalse a c p u) := by
  simp only [updateFalse]
  rw [if_neg (Nat.not_le.mpr hv), if_pos hu]
  by_cases h : normFalse a c p = 0
  · simp [h]
  · field_simp

theorem zoo_bayes_update_ratio_across_true {n : ℕ} (a : Fin n → ℝ) (c u v : Fin n) (p : ℝ)
    (hu : (u : ℕ) ≤ (c : ℕ)) (hv : (c : ℕ) < (v : ℕ)) :
    (1 - p) * (updateTrue a c p v * a u) = p * (a v * updateTrue a c p u) := by
  simp only [updateTrue]
  rw [if_neg (Nat.not_le.mpr hv), if_pos hu]
  by_cases h : normTrue a c p = 0
  · simp [h]
  · field_simp

theorem zoo_bayes_truth_window_light_cell {n : ℕ} (a : Fin n → ℝ) (I : Fin n) (l : ℕ)
    (hl : 0 < l) (hIl : l ≤ (I : ℕ)) (ha0 : ∀ m, 0 ≤ a m) (hsum : (∑ m, a m) = 1) :
    ∃ k : Fin n, ((I : ℕ) - l ≤ (k : ℕ) ∧ (k : ℕ) < (I : ℕ)) ∧ a k ≤ 1 / (l : ℝ) := by
  classical
  by_contra hcon
  push Not at hcon
  set W : Finset (Fin n) :=
    Finset.univ.filter fun k => (I : ℕ) - l ≤ (k : ℕ) ∧ (k : ℕ) < (I : ℕ) with hWdef
  have hcard : W.card = l := by
    have himg : W.image Fin.val = Finset.Ico ((I : ℕ) - l) (I : ℕ) := by
      ext m
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_Ico, hWdef]
      constructor
      · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
        exact ⟨hk1, hk2⟩
      · intro ⟨hm1, hm2⟩
        exact ⟨⟨m, lt_trans hm2 (Fin.isLt I)⟩, ⟨hm1, hm2⟩, rfl⟩
    rw [← Finset.card_image_of_injOn (fun x _ y _ h => Fin.val_injective h), himg, Nat.card_Ico,
      Nat.sub_sub_self hIl]
  have hWne : W.Nonempty := Finset.card_pos.mp (by rw [hcard]; omega)
  have hone : (1 : ℝ) = ∑ k ∈ W, 1 / (l : ℝ) := by
    have h1 : (∑ k ∈ W, 1 / (l : ℝ)) = (∑ _k ∈ W, (1 : ℝ)) / (l : ℝ) :=
      (Finset.sum_div _ _ _).symm
    have h2 : (∑ _k ∈ W, (1 : ℝ)) = (W.card : ℝ) := by
      rw [Finset.sum_const, Nat.smul_one_eq_cast]
    have hlR : ((l : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hl)
    rw [h1, h2, hcard, div_self hlR]
  have hlt : ∑ k ∈ W, 1 / (l : ℝ) < ∑ k ∈ W, a k := by
    refine Finset.sum_lt_sum_of_nonempty hWne fun k hk => ?_
    simp only [hWdef, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact hcon k hk
  have hle : ∑ k ∈ W, a k ≤ ∑ m, a m := by
    apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun m _ _ => ha0 m)
    rw [hWdef]
    exact Finset.filter_subset _ _
  linarith

theorem zoo_bayes_truth_answer_prob {n : ℕ} (j c : Fin n) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (truthAnswerProb j c p : ℝ) = if (c : ℕ) ≤ (j : ℕ) then p else 1 - p := by
  simp only [truthAnswerProb]
  by_cases h : (c : ℕ) ≤ (j : ℕ)
  · rw [if_pos h]; exact clampProb_eq hp0 hp1
  · rw [if_neg h]; exact clampProb_eq (by linarith) (by linarith)

theorem zoo_bayes_unrestricted_answer_prob_false :
    ¬ (∀ {n : ℕ} (j c : Fin n) (p : ℝ),
      (truthAnswerProb j c p : ℝ) = if (c : ℕ) ≤ (j : ℕ) then p else 1 - p) := by
  intro h
  have hx := h (0 : Fin 1) (0 : Fin 1) 5
  norm_num [truthAnswerProb,clampProb] at hx
  change (1 : ℝ) = 5 at hx
  norm_num at hx

theorem truthAnswerProb_eq {n : ℕ} (j c : Fin n) {p : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) :
    (truthAnswerProb j c p : ℝ) = if (c : ℕ) ≤ (j : ℕ) then p else 1 - p :=
  zoo_bayes_truth_answer_prob j c p (by linarith) (le_of_lt hp1)

end TruthSemantics

section Invariant

def truthInv {n : ℕ} (a : Fin n → ℝ) : Prop := (∀ m, 0 < a m) ∧ (∑ m, a m) ≤ 1

theorem sum_scale_split {n : ℕ} (a : Fin n → ℝ) (c : Fin n) (r s : ℝ) :
    (∑ m : Fin n, if (m : ℕ) ≤ (c : ℕ) then r * a m else s * a m)
      = r * prefixMass a c + s * ((∑ m, a m) - prefixMass a c) := by
  have hrest : (∑ m : Fin n, if (m : ℕ) ≤ (c : ℕ) then (0 : ℝ) else a m)
      = (∑ m, a m) - prefixMass a c := by
    have hpre0 : prefixMass a c
        = ∑ m : Fin n, if (m : ℕ) ≤ (c : ℕ) then a m else (0 : ℝ) := rfl
    have hsplit : ((∑ m : Fin n, if (m : ℕ) ≤ (c : ℕ) then a m else (0 : ℝ))
        + ∑ m : Fin n, if (m : ℕ) ≤ (c : ℕ) then (0 : ℝ) else a m) = ∑ m, a m := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun m _ => by
        by_cases hm : (m : ℕ) ≤ (c : ℕ) <;> simp [hm]
    linarith [hpre0]
  have hleft : (∑ m : Fin n, if (m : ℕ) ≤ (c : ℕ) then r * a m else s * a m)
      = r * (∑ m : Fin n, if (m : ℕ) ≤ (c : ℕ) then a m else (0 : ℝ))
        + s * (∑ m : Fin n, if (m : ℕ) ≤ (c : ℕ) then (0 : ℝ) else a m) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by
      by_cases hm : (m : ℕ) ≤ (c : ℕ) <;> simp [hm]
  have hpre : prefixMass a c
      = ∑ m : Fin n, if (m : ℕ) ≤ (c : ℕ) then a m else (0 : ℝ) := rfl
  rw [hleft, hrest, hpre]

theorem updateFalse_sum_le {n : ℕ} (a : Fin n → ℝ) (c : Fin n) {p : ℝ} (hp : 1 / 2 < p)
    (hp1 : p < 1) (ha0 : ∀ m, 0 ≤ a m) (hsum : (∑ m, a m) ≤ 1) :
    (∑ m, updateFalse a c p m) ≤ 1 := by
  obtain ⟨hF0, hF1, hT0, hT1⟩ := zoo_bayes_truth_norms_positive a c p hp hp1 ha0 hsum
  have h1 : (∑ m, updateFalse a c p m)
      = ((∑ m : Fin n, if (m : ℕ) ≤ (c : ℕ) then p * a m else (1 - p) * a m)) / normFalse a c p := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun m _ => rfl
  have h2 := sum_scale_split a c p (1 - p)
  have h3 : normFalse a c p = p * prefixMass a c + (1 - p) * (1 - prefixMass a c) := rfl
  rw [h1, h2, div_le_one hF0]
  have hk : (1 - p) * ((∑ m, a m) - prefixMass a c) ≤ (1 - p) * (1 - prefixMass a c) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith

theorem updateTrue_sum_le {n : ℕ} (a : Fin n → ℝ) (c : Fin n) {p : ℝ} (hp : 1 / 2 < p)
    (hp1 : p < 1) (ha0 : ∀ m, 0 ≤ a m) (hsum : (∑ m, a m) ≤ 1) :
    (∑ m, updateTrue a c p m) ≤ 1 := by
  obtain ⟨hF0, hF1, hT0, hT1⟩ := zoo_bayes_truth_norms_positive a c p hp hp1 ha0 hsum
  have h1 : (∑ m, updateTrue a c p m)
      = ((∑ m : Fin n, if (m : ℕ) ≤ (c : ℕ) then (1 - p) * a m else p * a m)) / normTrue a c p := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun m _ => rfl
  have h2 := sum_scale_split a c (1 - p) p
  have h3 : normTrue a c p = (1 - p) * prefixMass a c + p * (1 - prefixMass a c) := by
    unfold normTrue normFalse
    ring
  rw [h1, h2, div_le_one hT0]
  have hk : p * ((∑ m, a m) - prefixMass a c) ≤ p * (1 - prefixMass a c) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith

theorem crossingAbsorb_support_inv {n : ℕ} (hn : 0 < n) (j : Fin n) (p ε R : ℝ) (u v : Fin n)
    (hp : 1 / 2 < p) (hp1 : p < 1) (a : Fin n → ℝ) (ha : truthInv a) :
    ∀ cfg ∈ (crossingAbsorbNext hn j p ε R u v a).support, truthInv (configPosterior cfg) := by
  intro cfg hcfg
  by_cases habs : R * a v ≤ a u
  · simp only [crossingAbsorbNext, if_pos habs] at hcfg
    obtain rfl := (PMF.mem_support_pure_iff _ _).mp hcfg
    exact ha
  · simp only [crossingAbsorbNext, if_neg habs] at hcfg
    by_cases hhalt : ∃ m : Fin n, ε ≤ a m
    · simp only [trueLearnerNext, dif_pos hhalt] at hcfg
      obtain rfl := (PMF.mem_support_pure_iff _ _).mp hcfg
      exact ha
    · simp only [trueLearnerNext, dif_neg hhalt] at hcfg
      obtain ⟨b, hb, hEq⟩ := (PMF.mem_support_bind_iff _ _ cfg).mp hcfg
      rw [PMF.mem_support_pure_iff _ _] at hEq
      obtain rfl := hEq
      have ha0 : ∀ m, 0 ≤ a m := fun m => le_of_lt (ha.1 m)
      obtain ⟨hposF, hposT⟩ :=
        zoo_bayes_truth_update_positivity a (stageTwoCut hn a ε) p hp hp1 ha.1 ha.2
      rcases b
      · exact ⟨hposF, updateFalse_sum_le a (stageTwoCut hn a ε) hp hp1 ha0 ha.2⟩
      · exact ⟨hposT, updateTrue_sum_le a (stageTwoCut hn a ε) hp hp1 ha0 ha.2⟩

end Invariant

section Ville

noncomputable def ratioPotential {n : ℕ} (u v : Fin n)
    (cfg : Configuration (Fin n → ℝ) (Fin n → ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal (configPosterior cfg u / configPosterior cfg v)

theorem expectation_charge_fst {α : Type} (m : ℕ) (q : CostedLaw α) (g : α → ℝ≥0∞) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge m q) (fun y => g y.1) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation q (fun y => g y.1) := by
  rw [show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge m q = PMF.map (fun x => (x.1, m + x.2)) q from rfl,
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]

theorem expectation_le_of_forall_mem {α : Type} {p : PMF α} {f g : α → ℝ≥0∞}
    (h : ∀ a ∈ p.support, f a ≤ g a) : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p f ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p g := by
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases ha : a ∈ p.support
  · exact mul_le_mul_right (h a ha) _
  · have hpa : p a = 0 := by simpa [PMF.mem_support_iff] using ha
    simp [hpa]

theorem expectation_bernoulli_branches {q : ℝ≥0} (hq : q ≤ 1) {α : Type} (F : Bool → α)
    (g : α → ℝ≥0∞) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation ((PMF.bernoulli q hq).bind fun b => PMF.pure (F b)) g =
      (q : ℝ≥0∞) * g (F true) + ((1 - q : ℝ≥0) : ℝ≥0∞) * g (F false) := by
  classical
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind,
    Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr fun b => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure (F b) g]
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
  rw [tsum_fintype, Fintype.sum_bool]
  simp only [PMF.bernoulli_apply, Bool.cond_true, Bool.cond_false]

theorem ofReal_split_le {u v r : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1) :
    ENNReal.ofReal (u * r) + ENNReal.ofReal (v * r) ≤ ENNReal.ofReal r := by
  by_cases hr : 0 ≤ r
  · rw [← ENNReal.ofReal_add (mul_nonneg hu hr) (mul_nonneg hv hr), ← add_mul, huv, one_mul]
  · have hr' : r < 0 := by linarith
    have h1 : u * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu (le_of_lt hr')
    have h2 : v * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hv (le_of_lt hr')
    rw [ENNReal.ofReal_eq_zero.mpr h1, ENNReal.ofReal_eq_zero.mpr h2, add_zero,
      ENNReal.ofReal_eq_zero.mpr (by linarith)]

theorem truthAnswerProb_weights {n : ℕ} (j c : Fin n) {p : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) :
    (truthAnswerProb j c p : ℝ≥0∞) = ENNReal.ofReal (if (c : ℕ) ≤ (j : ℕ) then p else 1 - p) ∧
      ((1 - truthAnswerProb j c p : ℝ≥0) : ℝ≥0∞)
        = ENNReal.ofReal (if (c : ℕ) ≤ (j : ℕ) then 1 - p else p) := by
  have hp0 : (0 : ℝ) ≤ p := by linarith
  have hX : (0 : ℝ) ≤ if (c : ℕ) ≤ (j : ℕ) then p else 1 - p := by
    by_cases h : (c : ℕ) ≤ (j : ℕ) <;> simp [h] <;> linarith
  have hX1 : (if (c : ℕ) ≤ (j : ℕ) then p else 1 - p) ≤ 1 := by
    by_cases h : (c : ℕ) ≤ (j : ℕ) <;> simp [h] <;> linarith
  have hY : (0 : ℝ) ≤ if (c : ℕ) ≤ (j : ℕ) then 1 - p else p := by
    by_cases h : (c : ℕ) ≤ (j : ℕ) <;> simp [h] <;> linarith
  have ew : truthAnswerProb j c p
      = Real.toNNReal (if (c : ℕ) ≤ (j : ℕ) then p else 1 - p) := by
    apply NNReal.coe_injective
    rw [truthAnswerProb_eq j c hp hp1, Real.coe_toNNReal _ hX]
  have e2 : (1 - Real.toNNReal (if (c : ℕ) ≤ (j : ℕ) then p else 1 - p) : ℝ≥0)
      = Real.toNNReal (if (c : ℕ) ≤ (j : ℕ) then 1 - p else p) := by
    apply NNReal.coe_injective
    have hc1 : ((Real.toNNReal (if (c : ℕ) ≤ (j : ℕ) then p else 1 - p) : ℝ≥0) : ℝ)
        = if (c : ℕ) ≤ (j : ℕ) then p else 1 - p := Real.coe_toNNReal _ hX
    have hq1 : Real.toNNReal (if (c : ℕ) ≤ (j : ℕ) then p else 1 - p) ≤ 1 := by
      refine NNReal.coe_le_coe.mp ?_
      rw [hc1, NNReal.coe_one]
      exact hX1
    show ((1 - Real.toNNReal (if (c : ℕ) ≤ (j : ℕ) then p else 1 - p) : ℝ≥0) : ℝ)
      = ((Real.toNNReal (if (c : ℕ) ≤ (j : ℕ) then 1 - p else p) : ℝ≥0) : ℝ)
    rw [NNReal.coe_sub hq1, hc1, NNReal.coe_one, Real.coe_toNNReal _ hY]
    by_cases h : (c : ℕ) ≤ (j : ℕ) <;> simp [h]
  rw [ew]
  exact ⟨ENNReal.ofNNReal_toNNReal _, by
    rw [e2]; exact ENNReal.ofNNReal_toNNReal _⟩

theorem same_side_potential_le {n : ℕ} (a : Fin n → ℝ) (c u v : Fin n) (p : ℝ)
    (hside : ((u : ℕ) ≤ (c : ℕ)) = ((v : ℕ) ≤ (c : ℕ))) :
    ENNReal.ofReal (updateTrue a c p u / updateTrue a c p v) ≤ ENNReal.ofReal (a u / a v) ∧
      ENNReal.ofReal (updateFalse a c p u / updateFalse a c p v) ≤ ENNReal.ofReal (a u / a v) := by
  obtain ⟨hFe, hTe⟩ := zoo_bayes_update_ratio_same_side a c u v p hside
  constructor
  · by_cases h0 : updateTrue a c p v = 0
    · rw [h0, div_zero, ENNReal.ofReal_zero]
      simp
    · have h1 : a v ≠ 0 := fun h => h0 (by simp [updateTrue, h])
      exact le_of_eq (congrArg ENNReal.ofReal (by
        rw [div_eq_div_iff h0 h1]; linear_combination hTe))
  · by_cases h0 : updateFalse a c p v = 0
    · rw [h0, div_zero, ENNReal.ofReal_zero]
      simp
    · have h1 : a v ≠ 0 := fun h => h0 (by simp [updateFalse, h])
      exact le_of_eq (congrArg ENNReal.ofReal (by
        rw [div_eq_div_iff h0 h1]; linear_combination hFe))

theorem across_one_step_le {n : ℕ} (a : Fin n → ℝ) (c num den : Fin n) {p w w' : ℝ}
    (hw1 : 0 < w) (_hw2 : w < 1) (hw3 : 0 < w') (hww' : w + w' = 1)
    (hT : w * (updateTrue a c p num * a den) = w' * (a num * updateTrue a c p den))
    (hF : w' * (updateFalse a c p num * a den) = w * (a num * updateFalse a c p den)) :
    ENNReal.ofReal w * ENNReal.ofReal (updateTrue a c p num / updateTrue a c p den)
      + ENNReal.ofReal w' * ENNReal.ofReal (updateFalse a c p num / updateFalse a c p den)
      ≤ ENNReal.ofReal (a num / a den) := by
  have keyT : ENNReal.ofReal w * ENNReal.ofReal (updateTrue a c p num / updateTrue a c p den)
      ≤ ENNReal.ofReal (w' * (a num / a den)) := by
    by_cases h0 : updateTrue a c p den = 0
    · rw [h0, div_zero, ENNReal.ofReal_zero, mul_zero]
      simp
    · have h1 : a den ≠ 0 := fun h => h0 (by simp [updateTrue, h])
      have heq : w * (updateTrue a c p num / updateTrue a c p den)
          = w' * (a num / a den) := by
        rw [← mul_div_assoc, ← mul_div_assoc, div_eq_div_iff h0 h1]
        linear_combination hT
      rw [← ENNReal.ofReal_mul (le_of_lt hw1)]
      rw [heq]
  have keyF : ENNReal.ofReal w' * ENNReal.ofReal (updateFalse a c p num / updateFalse a c p den)
      ≤ ENNReal.ofReal (w * (a num / a den)) := by
    by_cases h0 : updateFalse a c p den = 0
    · rw [h0, div_zero, ENNReal.ofReal_zero, mul_zero]
      simp
    · have h1 : a den ≠ 0 := fun h => h0 (by simp [updateFalse, h])
      have heq : w' * (updateFalse a c p num / updateFalse a c p den)
          = w * (a num / a den) := by
        rw [← mul_div_assoc, ← mul_div_assoc, div_eq_div_iff h0 h1]
        linear_combination hF
      rw [← ENNReal.ofReal_mul (le_of_lt hw3)]
      rw [heq]
  calc ENNReal.ofReal w * ENNReal.ofReal (updateTrue a c p num / updateTrue a c p den)
        + ENNReal.ofReal w' * ENNReal.ofReal (updateFalse a c p num / updateFalse a c p den)
      ≤ ENNReal.ofReal (w' * (a num / a den))
        + ENNReal.ofReal (w * (a num / a den)) := add_le_add keyT keyF
    _ ≤ ENNReal.ofReal (a num / a den) :=
        ofReal_split_le (le_of_lt hw3) (le_of_lt hw1) (by rw [add_comm]; exact hww')

theorem bernoulli_weights_add {q : ℝ≥0} (hq : q ≤ 1) :
    ((q : ℝ≥0∞) + ((1 - q : ℝ≥0) : ℝ≥0∞)) = 1 := by
  have h : (q + (1 - q : ℝ≥0)) = (1 : ℝ≥0) := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add, NNReal.coe_sub hq, NNReal.coe_one]
    ring
  exact_mod_cast h

theorem same_side_step_bound {q : ℝ≥0} (hq : q ≤ 1) (VT VF V : ℝ≥0∞) (hT : VT ≤ V)
    (hF : VF ≤ V) :
    (q : ℝ≥0∞) * VT + ((1 - q : ℝ≥0) : ℝ≥0∞) * VF ≤ V := by
  calc (q : ℝ≥0∞) * VT + ((1 - q : ℝ≥0) : ℝ≥0∞) * VF
      ≤ (q : ℝ≥0∞) * V + ((1 - q : ℝ≥0) : ℝ≥0∞) * V :=
        add_le_add (mul_le_mul_right hT _) (mul_le_mul_right hF _)
    _ = ((q : ℝ≥0∞) + ((1 - q : ℝ≥0) : ℝ≥0∞)) * V := (add_mul _ _ _).symm
    _ = V := by rw [bernoulli_weights_add hq, one_mul]

theorem crossingAbsorb_one_step_right {n : ℕ} (hn : 0 < n) (j k i : Fin n) {p ε R : ℝ}
    (hp : 1 / 2 < p) (hp1 : p < 1) (hjk : (j : ℕ) < (k : ℕ)) (hki : (k : ℕ) < (i : ℕ))
    (a : Fin n → ℝ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (crossingAbsorbNext hn j p ε R i k a)
        (ratioPotential i k) ≤ ratioPotential i k (Sum.inr a) := by
  by_cases habs : R * a k ≤ a i
  · simp only [crossingAbsorbNext, if_pos habs, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure]
    exact le_rfl
  · simp only [crossingAbsorbNext, if_neg habs]
    by_cases hhalt : ∃ m : Fin n, ε ≤ a m
    · simp only [trueLearnerNext, dif_pos hhalt, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure]
      exact le_rfl
    · simp only [trueLearnerNext, dif_neg hhalt]
      have hbr := expectation_bernoulli_branches
        (q := truthAnswerProb j (stageTwoCut hn a ε) p)
        (clampProb_le (if (stageTwoCut hn a ε : ℕ) ≤ (j : ℕ) then p else 1 - p))
        (fun b => Sum.inr
          (if b then updateTrue a (stageTwoCut hn a ε) p
            else updateFalse a (stageTwoCut hn a ε) p))
        (ratioPotential i k)
      rw [hbr]
      simp only [ratioPotential, configPosterior, Sum.elim_inr, id_eq]
      rcases Classical.em ((i : ℕ) ≤ (stageTwoCut hn a ε : ℕ)) with hic | hic
      · have hside : ((i : ℕ) ≤ (stageTwoCut hn a ε : ℕ))
          = ((k : ℕ) ≤ (stageTwoCut hn a ε : ℕ)) := by
          simp [hic, le_trans (le_of_lt hki) hic]
        exact same_side_step_bound
          (q := truthAnswerProb j (stageTwoCut hn a ε) p)
          (clampProb_le (if (stageTwoCut hn a ε : ℕ) ≤ (j : ℕ) then p else 1 - p)) _ _ _
          (same_side_potential_le a _ i k p hside).1 (same_side_potential_le a _ i k p hside).2
      · rcases Classical.em ((k : ℕ) ≤ (stageTwoCut hn a ε : ℕ)) with hkc | hkc
        · have hcj : ¬ ((stageTwoCut hn a ε : ℕ) ≤ (j : ℕ)) := by omega
          obtain ⟨hw1, hw2⟩ := truthAnswerProb_weights j (stageTwoCut hn a ε) hp hp1
          rw [hw1, hw2]
          simp only [if_neg hcj]
          exact across_one_step_le a (stageTwoCut hn a ε) i k (by linarith) (by linarith)
            (by linarith) (by ring)
            (zoo_bayes_update_ratio_across_true a _ k i p hkc (by omega))
            (zoo_bayes_update_ratio_across_false a _ k i p hkc (by omega))
        · have hside : ((i : ℕ) ≤ (stageTwoCut hn a ε : ℕ))
            = ((k : ℕ) ≤ (stageTwoCut hn a ε : ℕ)) := by
            simp [hic, hkc]
          exact same_side_step_bound
            (q := truthAnswerProb j (stageTwoCut hn a ε) p)
            (clampProb_le (if (stageTwoCut hn a ε : ℕ) ≤ (j : ℕ) then p else 1 - p)) _ _ _
            (same_side_potential_le a _ i k p hside).1 (same_side_potential_le a _ i k p hside).2

theorem crossingAbsorb_one_step_left {n : ℕ} (hn : 0 < n) (k i j : Fin n) {p ε R : ℝ}
    (hp : 1 / 2 < p) (hp1 : p < 1) (hki : (k : ℕ) < (i : ℕ)) (hij : (i : ℕ) < (j : ℕ))
    (a : Fin n → ℝ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (crossingAbsorbNext hn j p ε R k i a)
        (ratioPotential k i) ≤ ratioPotential k i (Sum.inr a) := by
  by_cases habs : R * a i ≤ a k
  · simp only [crossingAbsorbNext, if_pos habs, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure]
    exact le_rfl
  · simp only [crossingAbsorbNext, if_neg habs]
    by_cases hhalt : ∃ m : Fin n, ε ≤ a m
    · simp only [trueLearnerNext, dif_pos hhalt, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure]
      exact le_rfl
    · simp only [trueLearnerNext, dif_neg hhalt]
      have hbr := expectation_bernoulli_branches
        (q := truthAnswerProb j (stageTwoCut hn a ε) p)
        (clampProb_le (if (stageTwoCut hn a ε : ℕ) ≤ (j : ℕ) then p else 1 - p))
        (fun b => Sum.inr
          (if b then updateTrue a (stageTwoCut hn a ε) p
            else updateFalse a (stageTwoCut hn a ε) p))
        (ratioPotential k i)
      rw [hbr]
      simp only [ratioPotential, configPosterior, Sum.elim_inr, id_eq]
      rcases Classical.em ((i : ℕ) ≤ (stageTwoCut hn a ε : ℕ)) with hic | hic
      · have hside : ((k : ℕ) ≤ (stageTwoCut hn a ε : ℕ))
          = ((i : ℕ) ≤ (stageTwoCut hn a ε : ℕ)) := by
          simp [hic, le_trans (le_of_lt hki) hic]
        exact same_side_step_bound
          (q := truthAnswerProb j (stageTwoCut hn a ε) p)
          (clampProb_le (if (stageTwoCut hn a ε : ℕ) ≤ (j : ℕ) then p else 1 - p)) _ _ _
          (same_side_potential_le a _ k i p hside).1 (same_side_potential_le a _ k i p hside).2
      · rcases Classical.em ((k : ℕ) ≤ (stageTwoCut hn a ε : ℕ)) with hkc | hkc
        · have hcj : (stageTwoCut hn a ε : ℕ) ≤ (j : ℕ) := by omega
          obtain ⟨hw1, hw2⟩ := truthAnswerProb_weights j (stageTwoCut hn a ε) hp hp1
          rw [hw1, hw2]
          simp only [if_pos hcj]
          refine across_one_step_le a (stageTwoCut hn a ε) k i (by linarith) (by linarith)
            (by linarith) (by ring) ?_ ?_
          · calc p * (updateTrue a (stageTwoCut hn a ε) p k * a i)
                = p * (a i * updateTrue a (stageTwoCut hn a ε) p k) := by ring
              _ = (1 - p) * (updateTrue a (stageTwoCut hn a ε) p i * a k) :=
                  (zoo_bayes_update_ratio_across_true a _ k i p hkc (by omega)).symm
              _ = (1 - p) * (a k * updateTrue a (stageTwoCut hn a ε) p i) := by ring
          · calc (1 - p) * (updateFalse a (stageTwoCut hn a ε) p k * a i)
                = (1 - p) * (a i * updateFalse a (stageTwoCut hn a ε) p k) := by ring
              _ = p * (updateFalse a (stageTwoCut hn a ε) p i * a k) :=
                  (zoo_bayes_update_ratio_across_false a _ k i p hkc (by omega)).symm
              _ = p * (a k * updateFalse a (stageTwoCut hn a ε) p i) := by ring
        · have hside : ((k : ℕ) ≤ (stageTwoCut hn a ε : ℕ))
            = ((i : ℕ) ≤ (stageTwoCut hn a ε : ℕ)) := by
            simp [hic, hkc]
          exact same_side_step_bound
            (q := truthAnswerProb j (stageTwoCut hn a ε) p)
            (clampProb_le (if (stageTwoCut hn a ε : ℕ) ≤ (j : ℕ) then p else 1 - p)) _ _ _
            (same_side_potential_le a _ k i p hside).1 (same_side_potential_le a _ k i p hside).2

theorem ville_event_bound {S A : Type} (kn : S → PMF (Configuration S A))
    (V : Configuration S A → ℝ≥0∞) (Q : Configuration S A → Prop)
    (Inv : Configuration S A → Prop) (r : ℝ≥0∞) (hr0 : r ≠ 0) (hrT : r ≠ ⊤)
    (hstep : ∀ s, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (kn s) V ≤ V (Sum.inr s))
    (hinv : ∀ s, Inv (Sum.inr s) → ∀ c ∈ (kn s).support, Inv c)
    (hpoint : ∀ cfg, Inv cfg → Q cfg → r ≤ V cfg) :
    ∀ (fuel : ℕ) (cfg : Configuration S A), Inv cfg →
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor kn fuel cfg) (fun x => Q x.1) ≤ V cfg / r := by
  intro fuel
  induction fuel with
  | zero =>
      intro cfg hI
      rw [runFor_zero, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_ret]
      by_cases hQ : Q cfg
      · rw [if_pos hQ]
        exact (ENNReal.le_div_iff_mul_le (Or.inl hr0) (Or.inl hrT)).mpr
          (by rw [one_mul]; exact hpoint cfg hI hQ)
      · rw [if_neg hQ]
        simp
  | succ fuel ih =>
      intro cfg hI
      cases cfg with
      | inl out =>
          rw [runFor_halted, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_ret]
          by_cases hQ : Q (Sum.inl out)
          · rw [if_pos hQ]
            exact (ENNReal.le_div_iff_mul_le (Or.inl hr0) (Or.inl hrT)).mpr
              (by rw [one_mul]; exact hpoint _ hI hQ)
          · rw [if_neg hQ]
            simp
      | inr s =>
          have hunfold : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor kn (fuel + 1) (Sum.inr s)) (fun x => Q x.1)
              = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (kn s)
                  (fun c => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor kn fuel c) (fun x => Q x.1)) := by
            rw [show runFor kn (fuel + 1) (Sum.inr s)
                  = PMF.bind (tick kn (Sum.inr s))
                      fun x => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge x.2 (runFor kn fuel x.1) from rfl,
              Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_bind_general,
              show tick kn (Sum.inr s) = PMF.map (fun c => (c, 1)) (kn s) from rfl,
              Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
            exact Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr fun c =>
              Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_charge_general 1 (runFor kn fuel c) (fun x => Q x.1)
          rw [hunfold]
          calc Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (kn s)
                (fun c => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (runFor kn fuel c) (fun x => Q x.1))
              ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (kn s) (fun c => V c / r) :=
                expectation_le_of_forall_mem fun c hc => ih c (hinv s hI c hc)
            _ = r⁻¹ * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (kn s) V := by
                rw [← Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_const_mul (kn s) r⁻¹ V]
                exact Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr fun c => by
                  rw [div_eq_mul_inv]
                  exact mul_comm _ _
            _ ≤ r⁻¹ * V (Sum.inr s) := mul_le_mul_right (hstep s) _
            _ = V (Sum.inr s) / r := by rw [div_eq_mul_inv, mul_comm]

end Ville

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
