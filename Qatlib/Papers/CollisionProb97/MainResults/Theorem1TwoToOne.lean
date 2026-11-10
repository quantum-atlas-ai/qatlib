/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionProb97.MainResults.CollisionCounting
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CollisionProb97.MainResults

open scoped BigOperators

universe u

theorem twoToOne_count_and_budget (l : ℝ) (hl : 1 < l) (hl4 : l < 4 / 3) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X Y : Type u} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
        (F : X → Y) (K : Finset X),
        0 < Fintype.card X →
        RToOne F 2 →
        1 ≤ K.card → K.card ≤ Fintype.card X →
        Set.InjOn F (K : Set X) →
        (collisionCandidates F K).card = K.card ∧
        (∀ x1 ∈ collisionCandidates F K, ∃ x0 ∈ K, x0 ≠ x1 ∧ F x0 = F x1) ∧
        proposedCollisionBudget (groverCoefficient l) (Fintype.card X)
            (collisionCandidates F K).card K.card
          ≤ C * (K.card + Real.sqrt ((Fintype.card X : ℝ) / K.card)) ∧
        proposedRecordCount K.card = K.card := by
  refine ⟨groverCoefficient l + 2, by
    have h := groverCoefficient_pos l hl hl4
    linarith, ?_⟩
  intro X Y _ _ _ _ F K hN hF hk hkN hinj
  have hcount : (collisionCandidates F K).card = K.card := by
    have h := collisionCandidates_card F 2 hF K hinj
    simpa using h
  refine ⟨hcount, ?_, ?_, proposedRecordCount_eq K.card⟩
  · intro x1 hx1
    exact collisionCandidates_spec F K hx1
  · rw [hcount]
    have hk1 : (1 : ℝ) ≤ (K.card : ℝ) := by exact_mod_cast hk
    have hg : 0 < groverCoefficient l := groverCoefficient_pos l hl hl4
    have hgk : 0 ≤ groverCoefficient l * (K.card : ℝ) :=
      mul_nonneg hg.le (by linarith)
    have hs : 0 ≤ Real.sqrt ((Fintype.card X : ℝ) / K.card) := Real.sqrt_nonneg _
    unfold proposedCollisionBudget
    nlinarith

theorem twoToOne_cubeRoot {N k : ℝ} (hk : 1 ≤ k) (hcube : k ^ 3 = N) :
    k + Real.sqrt (N / k) = 2 * k := by
  have hkpos : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hNk : N / k = k ^ 2 := by
    rw [← hcube]
    field_simp
  rw [hNk, Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith)]
  ring

theorem twoToOne_real_cube_budget (l : ℝ) (hl : 1 < l) (hl4 : l < 4 / 3)
    {N k : ℝ} (hk : 1 ≤ k) (hcube : k ^ 3 = N) :
    proposedCollisionBudget (groverCoefficient l) N k k
      ≤ (groverCoefficient l + 2) * k := by
  have hg : 0 < groverCoefficient l := groverCoefficient_pos l hl hl4
  have hs : Real.sqrt (N / k) = k := by
    have h := twoToOne_cubeRoot hk hcube
    linarith
  unfold proposedCollisionBudget
  rw [hs]
  nlinarith

end Qatlib.Papers.CollisionProb97.MainResults
