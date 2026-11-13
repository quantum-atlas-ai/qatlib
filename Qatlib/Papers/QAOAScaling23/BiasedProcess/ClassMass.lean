/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.BiasedProcess.CostClasses
import Qatlib.Papers.QAOAScaling23.BiasedProcess.WeightedVisits

/-!
# Cost-class weights and cumulative mass

This module extends the real cost-class masses to a sequence `weights` and relates its prefixes
to sums over candidate labels. It proves normalization and optimal-class lower bounds for the
weighted descent model associated with [ShaydulinEtAl2024].

## Main statements

* `prefix_labels`: A cost-class weight prefix equals the total real probability of candidate
  labels with ranks below its endpoint.
* `weights_normalized`: The prefix containing every cost class has total weight one.
* `optimal_le_prefix`: Every positive-length weight prefix is at least the optimal-class weight.

## References

* [Shaydulin et al., 2024][ShaydulinEtAl2024]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open scoped Classical ENNReal
open Qatlib.Papers.QAOAScaling23.BiasedProcess
open Qatlib.Papers.QAOAScaling23.WeightedCost
namespace Qatlib.Papers.QAOAScaling23.BiasedProcess.Born
variable {I : Type} [Fintype I]

/-- The real mass of cost class `j`, extended by zero beyond the finite set of cost classes. -/
def weights (cost : I → ℝ) (p : PMF I) (j : ℕ) : ℝ :=
  if h : j < (costLevels cost).card then (costClassLaw cost p ⟨j,h⟩).toReal else 0

/-- Every cost-class weight is nonnegative. -/
theorem weights_nonneg (cost : I → ℝ) (p : PMF I) (j : ℕ) : 0 ≤ weights cost p j := by
  unfold weights
  split_ifs <;> positivity

/-- The number of distinct cost classes is at most the number of candidates. -/
theorem classes_card_le (cost : I → ℝ) : (costLevels cost).card ≤ Fintype.card I := by
  exact (Finset.card_image_le).trans_eq (Finset.card_univ)

/-- The existence of a current candidate makes the number of cost classes positive. -/
theorem classes_pos (cost : I → ℝ) (current : I) : 0 < (costLevels cost).card :=
  Finset.card_pos.2 ⟨cost current,by simp [costLevels]⟩

/-- A weight prefix within the class range equals the sum of the corresponding real cost-class
probabilities. -/
theorem prefix_fin (cost : I → ℝ) (p : PMF I) (k : ℕ) (hk : k ≤ (costLevels cost).card) :
    prefixSum (weights cost p) k = ∑ j : Fin k, (costClassLaw cost p ⟨j.val,lt_of_lt_of_le j.isLt hk⟩).toReal := by
  rw [prefixSum,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp only [weights,dif_pos (lt_of_lt_of_le j.isLt hk)]

/-- Summing rank fibers below `k` equals summing labels whose rank is below `k`. -/
theorem lower_fiber_sum {L k : ℕ} (hk : k ≤ L) (f : I → Fin L) (g : I → ℝ) :
    (∑ j : Fin k, ∑ i, if f i = ⟨j.val,lt_of_lt_of_le j.isLt hk⟩ then g i else 0) =
      ∑ i, if (f i).val < k then g i else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (f i).val < k
  · rw [if_pos hi]
    rw [Finset.sum_eq_single (⟨(f i).val,hi⟩ : Fin k)]
    · simp
    · intro b _ hb
      have hn : f i ≠ ⟨b.val,lt_of_lt_of_le b.isLt hk⟩ := by
        intro he
        apply hb
        apply Fin.ext
        exact (congrArg Fin.val he).symm
      simp only [if_neg hn]
    · simp
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro b _
    have hn : f i ≠ ⟨b.val,lt_of_lt_of_le b.isLt hk⟩ := by
      intro he
      exact hi (by rw [he];exact b.isLt)
    simp only [if_neg hn]

/-- A cost-class weight prefix equals the total real probability of candidate labels with ranks
below its endpoint. -/
theorem prefix_labels (cost : I → ℝ) (p : PMF I) (k : ℕ) (hk : k ≤ (costLevels cost).card) :
    prefixSum (weights cost p) k = ∑ i, if (costRank cost i).val < k then (p i).toReal else 0 := by
  rw [prefix_fin cost p k hk]
  simp_rw [costClassLaw_real_fiber]
  exact lower_fiber_sum hk (costRank cost) (fun i => (p i).toReal)

/-- The prefix containing every cost class has total weight one. -/
theorem weights_normalized (cost : I → ℝ) (p : PMF I) :
    prefixSum (weights cost p) (costLevels cost).card = 1 := by
  rw [prefix_labels cost p _ le_rfl]
  simp only [Fin.is_lt,ite_true]
  rw [← ENNReal.toReal_sum (fun i _ => PMF.apply_ne_top p i)]
  simpa only [tsum_fintype,ENNReal.toReal_one] using congrArg ENNReal.toReal p.tsum_coe

/-- Every positive-length weight prefix is at least the optimal-class weight. -/
theorem optimal_le_prefix (cost : I → ℝ) (p : PMF I) (k : ℕ) (hk : 0 < k) :
    weights cost p 0 ≤ prefixSum (weights cost p) k := by
  exact Finset.single_le_sum (fun j _ => weights_nonneg cost p j) (by simpa using hk)
end Qatlib.Papers.QAOAScaling23.BiasedProcess.Born
