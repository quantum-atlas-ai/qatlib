/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.BiasedProcess.BornMass
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open scoped Classical ENNReal
open Qatlib.Papers.QAOAScaling23.CausalSearch
open Qatlib.Papers.QAOAScaling23.BiasedProcess
open Qatlib.Papers.QAOAScaling23.WeightedCost
namespace Qatlib.Papers.QAOAScaling23.BiasedProcess.Born
variable {I : Type} [Fintype I]

theorem lower_weights_sum (cost : I → ℝ) (p : PMF I) (k : ℕ)
    (hk : k ≤ (costLevels cost).card) (hpos : 0 < prefixSum (weights cost p) k) :
    (∑ j : Fin k, (costClassLaw cost p ⟨j.val,lt_of_lt_of_le j.isLt hk⟩).toReal / prefixSum (weights cost p) k) = 1 := by
  rw [← Finset.sum_div,← prefix_fin cost p k hk,div_self hpos.ne']

def lowerClassLaw (cost : I → ℝ) (p : PMF I) (k : ℕ)
    (hk : k ≤ (costLevels cost).card) (hpos : 0 < prefixSum (weights cost p) k) : PMF (Fin k) :=
  PMF.ofFintype (fun j => ENNReal.ofReal ((costClassLaw cost p ⟨j.val,lt_of_lt_of_le j.isLt hk⟩).toReal / prefixSum (weights cost p) k)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => div_nonneg ENNReal.toReal_nonneg hpos.le),lower_weights_sum cost p k hk hpos,ENNReal.ofReal_one])

theorem lowerClassLaw_real (cost : I → ℝ) (p : PMF I) (k : ℕ)
    (hk : k ≤ (costLevels cost).card) (hpos : 0 < prefixSum (weights cost p) k) (j : Fin k) :
    (lowerClassLaw cost p k hk hpos j).toReal = weights cost p j.val / prefixSum (weights cost p) k := by
  change (ENNReal.ofReal _).toReal = _
  rw [ENNReal.toReal_ofReal (div_nonneg ENNReal.toReal_nonneg hpos.le)]
  simp only [weights,dif_pos (lt_of_lt_of_le j.isLt hk)]

def lowerRank (cost : I → ℝ) (k : ℕ) (i : I) : Option (Fin k) :=
  if h : (costRank cost i).val < k then some ⟨(costRank cost i).val,h⟩ else none

theorem lowerRank_some (cost : I → ℝ) (k : ℕ) (i : I) (j : Fin k) :
    lowerRank cost k i = some j ↔ (costRank cost i).val = j.val := by
  unfold lowerRank
  split_ifs with h
  · simp only [Option.some.injEq,Fin.ext_iff]
  · simp only [false_iff]
    intro he
    exact h (he ▸ j.isLt)

def lowerInputLaw (cost : I → ℝ) (p : PMF I) (k : ℕ)
    (hk : k ≤ (costLevels cost).card) (hpos : 0 < prefixSum (weights cost p) k) : PMF I :=
  PMF.ofFintype (fun i => ENNReal.ofReal (if (costRank cost i).val < k then (p i).toReal / prefixSum (weights cost p) k else 0)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by split_ifs <;> positivity)]
    have he : (∑ i, if (costRank cost i).val < k then (p i).toReal / prefixSum (weights cost p) k else 0) = 1 := by
      simp_rw [show ∀i, (if (costRank cost i).val < k then (p i).toReal / prefixSum (weights cost p) k else 0) = (if (costRank cost i).val < k then (p i).toReal else 0) / prefixSum (weights cost p) k by intro i;split_ifs <;> simp]
      rw [← Finset.sum_div,← prefix_labels cost p k hk,div_self hpos.ne']
    rw [he,ENNReal.ofReal_one])
end Qatlib.Papers.QAOAScaling23.BiasedProcess.Born
