/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.OrderedBayes.BayesRatioCore.LearnerCutBridgeQuan
public import Mathlib.Tactic.FinCases

@[expose] public section

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Qatlib.Concepts.OrderedBayes.BayesRatioCore
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma23Quan

namespace Qatlib.Papers.OrderedList07.MainResults

/-!
# A concrete Bayesian learner step for ordered search

The abstract prefix theorem in Lemma 2.1 is consumed here on a genuinely finite instance.
For four equally likely cells and threshold `1 / 3`, the selected stage-two cut is the first
cell, its inclusive mass is `1 / 4`, and both noisy posterior updates are normalized at the
interior noise parameter `p = 3 / 4`.  The hypotheses are discharged by arithmetic, so this
module exercises the learner definitions rather than an unconstrained proposition.
-/

/-- The four-cell uniform learner selects the first cell at threshold `1 / 3`. -/
theorem uniform_four_stage_two_cut :
    stageTwoCut (n := 4) (by norm_num) (fun _ : Fin 4 => (1 / 4 : ℝ)) (1 / 3 : ℝ) =
      (⟨0, by norm_num⟩ : Fin 4) := by
  classical
  let a : Fin 4 → ℝ := fun _ => (1 / 4 : ℝ)
  let ε : ℝ := 1 / 3
  have hcut : (cutSet a ε).Nonempty := by
    refine ⟨⟨0, by norm_num⟩, ?_⟩
    simp only [cutSet, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold prefixMass a
    norm_num [Fin.sum_univ_succ]
  unfold stageTwoCut
  rw [dite_eq_left hcut]
  apply (Finset.min'_eq_iff _ hcut (⟨0, by norm_num⟩ : Fin 4)).2
  constructor
  · simp only [cutSet, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold prefixMass a
    norm_num [Fin.sum_univ_succ]
  · intro b hb
    exact Fin.zero_le b

/-- The selected cut in the four-cell instance has inclusive posterior mass `1 / 4`. -/
theorem uniform_four_selected_mass :
    prefixMass (fun _ : Fin 4 => (1 / 4 : ℝ))
        (stageTwoCut (n := 4) (by norm_num) (fun _ : Fin 4 => (1 / 4 : ℝ)) (1 / 3 : ℝ)) =
      (1 / 4 : ℝ) := by
  rw [uniform_four_stage_two_cut]
  unfold prefixMass
  norm_num [Fin.sum_univ_succ]

/-- Both posterior branches of the concrete four-cell learner are normalized. -/
theorem uniform_four_posterior_normalization :
    (∑ j : Fin 4,
      updateFalse (fun _ : Fin 4 => (1 / 4 : ℝ))
        (stageTwoCut (n := 4) (by norm_num) (fun _ : Fin 4 => (1 / 4 : ℝ)) (1 / 3 : ℝ))
        (3 / 4 : ℝ) j) = 1 ∧
    (∑ j : Fin 4,
      updateTrue (fun _ : Fin 4 => (1 / 4 : ℝ))
        (stageTwoCut (n := 4) (by norm_num) (fun _ : Fin 4 => (1 / 4 : ℝ)) (1 / 3 : ℝ))
        (3 / 4 : ℝ) j) = 1 := by
  rw [uniform_four_stage_two_cut]
  have hnonneg : ∀ j : Fin 4, 0 ≤ (fun _ : Fin 4 => (1 / 4 : ℝ)) j := by
    intro j
    norm_num
  have hsum : (∑ j : Fin 4, (fun _ : Fin 4 => (1 / 4 : ℝ)) j) = 1 := by
    norm_num [Fin.sum_univ_succ]
  have h := zoo_bayes_posterior_invariants
    (fun _ : Fin 4 => (1 / 4 : ℝ)) (⟨0, by norm_num⟩ : Fin 4) (3 / 4 : ℝ)
    hnonneg hsum (by norm_num) (by norm_num)
  exact ⟨h.2.1, h.2.2.2⟩

/-- The concrete four-cell learner's two posterior branches are the displayed non-uniform
probability vectors. -/
theorem uniform_four_branch_values :
    updateFalse (fun _ : Fin 4 => (1 / 4 : ℝ))
        (stageTwoCut (n := 4) (by norm_num) (fun _ : Fin 4 => (1 / 4 : ℝ)) (1 / 3 : ℝ))
        (3 / 4 : ℝ) =
      ![(1 / 2 : ℝ), 1 / 6, 1 / 6, 1 / 6] ∧
    updateTrue (fun _ : Fin 4 => (1 / 4 : ℝ))
        (stageTwoCut (n := 4) (by norm_num) (fun _ : Fin 4 => (1 / 4 : ℝ)) (1 / 3 : ℝ))
        (3 / 4 : ℝ) =
      ![(1 / 10 : ℝ), 3 / 10, 3 / 10, 3 / 10] := by
  rw [uniform_four_stage_two_cut]
  constructor <;> funext j <;> fin_cases j <;>
    norm_num [updateFalse, updateTrue, normFalse, normTrue, prefixMass,
      Fin.sum_univ_succ]

end Qatlib.Papers.OrderedList07.MainResults
