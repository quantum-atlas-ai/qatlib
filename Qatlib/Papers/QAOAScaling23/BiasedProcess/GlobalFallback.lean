/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.BiasedProcess.ClassMass
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
open scoped Classical
open Qatlib.Papers.QAOAScaling23.BiasedProcess
open Qatlib.Papers.QAOAScaling23.WeightedCost
namespace Qatlib.Papers.QAOAScaling23.BiasedProcess.Outside
variable {I : Type} [Fintype I]

theorem prefix_after_classes (cost : I→ℝ) (p : PMF I) (k : ℕ)
    (hk : (costLevels cost).card≤k) : prefixSum (Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.weights cost p) k=1 := by
  have he : prefixSum (Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.weights cost p) (costLevels cost).card=
      prefixSum (Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.weights cost p) k := by
    unfold prefixSum
    apply Finset.sum_subset (Finset.range_mono hk)
    intro j _ hj
    exact dif_neg (by simpa only [Finset.mem_range] using hj)
  rw [← he,Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.weights_normalized]

def classRep (cost : I→ℝ) (j : Fin (costLevels cost).card) : I :=
  Classical.choose (costRank_surjective cost j)

theorem classRep_rank (cost : I→ℝ) (j : Fin (costLevels cost).card) :
    costRank cost (classRep cost j)=j := Classical.choose_spec (costRank_surjective cost j)

def fallbackRow (cost : I→ℝ) (p : PMF I) (r : ℕ) (h : (costLevels cost).card≤r+1) : Row r where
  outcomes := (costLevels cost).card
  law := costClassLaw cost p
  next a := ⟨a.val,lt_of_lt_of_le a.isLt h⟩
  charge _ := 0
  bad _ := false

theorem fallback_candidate_rank (cost : I→ℝ) (p : PMF I) (r : ℕ)
    (h : (costLevels cost).card≤r+1) (a : Fin (fallbackRow cost p r h).outcomes) :
    (costRank cost (classRep cost a)).val=((fallbackRow cost p r h).next a).val := by
  exact congrArg Fin.val (classRep_rank cost a)

theorem fallback_row_law (cost : I→ℝ) (p : PMF I) (r : ℕ)
    (h : (costLevels cost).card≤r+1) (j : Fin (r+1)) :
    (∑a,if (fallbackRow cost p r h).next a=j then ((fallbackRow cost p r h).law a).toReal else 0)=
      Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.weights cost p j.val/prefixSum (Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.weights cost p) (r+1) := by
  rw [prefix_after_classes cost p (r+1) h,div_one]
  change (∑a : Fin (costLevels cost).card,
    if (⟨a.val,lt_of_lt_of_le a.isLt h⟩ : Fin (r+1))=j then (costClassLaw cost p a).toReal else 0)=_
  by_cases hj : j.val<(costLevels cost).card
  · rw [Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.weights,dif_pos hj]
    rw [Finset.sum_eq_single (⟨j.val,hj⟩ : Fin (costLevels cost).card)]
    · simp
    · intro a _ ha
      have hn : (⟨a.val,lt_of_lt_of_le a.isLt h⟩ : Fin (r+1))≠j := by
        intro he
        apply ha
        apply Fin.ext
        exact congrArg (fun z : Fin (r+1)=>z.val) he
      exact if_neg hn
    · simp
  · rw [Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.weights,dif_neg hj]
    apply Finset.sum_eq_zero
    intro a _
    have hn : (⟨a.val,lt_of_lt_of_le a.isLt h⟩ : Fin (r+1))≠j := by
      intro he
      have hv := congrArg Fin.val he
      exact hj (by rw [← hv];exact a.isLt)
    exact if_neg hn

theorem fallback_charge (cost : I→ℝ) (p : PMF I) (r : ℕ)
    (h : (costLevels cost).card≤r+1) :
    (∑a,((fallbackRow cost p r h).law a).toReal*((fallbackRow cost p r h).charge a:ℝ))=0 := by
  simp [fallbackRow]

theorem fallback_bad (cost : I→ℝ) (p : PMF I) (r : ℕ)
    (h : (costLevels cost).card≤r+1) :
    (∑a,((fallbackRow cost p r h).law a).toReal*(if (fallbackRow cost p r h).bad a then 1 else 0))=0 := by
  simp [fallbackRow]

end Qatlib.Papers.QAOAScaling23.BiasedProcess.Outside
