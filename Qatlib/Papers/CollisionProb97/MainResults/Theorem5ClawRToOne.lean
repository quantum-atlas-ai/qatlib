/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionProb97.MainResults.Theorem2RToOne
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CollisionProb97.MainResults

open scoped BigOperators

universe u

theorem rToOneClaw_count_and_budget (l : ℝ) (hl : 1 < l) (hl4 : l < 4 / 3) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X Y Z : Type u} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
        [Fintype Z] [DecidableEq Z]
        (F : X → Z) (G : Y → Z) (K : Finset X) (r : ℕ),
        RToOne F r → RToOne G r → 2 ≤ r →
        Fintype.card X = r * Fintype.card Z →
        Fintype.card Y = r * Fintype.card Z →
        0 < Fintype.card Z →
        (K.image F).card = K.card → 1 ≤ K.card → 2 * K.card ≤ Fintype.card Z →
        (clawCandidates G (K.image F)).card = r * K.card ∧
        (∀ y ∈ clawCandidates G (K.image F), ∃ x0 ∈ K, F x0 = G y) ∧
        proposedClawBudget (groverCoefficient l) (Fintype.card Y) ((r : ℝ) * K.card)
          ≤ C * Real.sqrt ((Fintype.card Y : ℝ) / ((r : ℝ) * K.card)) ∧
        (K.card : ℝ) ≤ (proposedThreeK K.card : ℝ) ∧
        (proposedThreeK K.card : ℝ) ≤ 3 * K.card ∧
        proposedRecordCount K.card = K.card := by
  refine ⟨groverCoefficient l, groverCoefficient_pos l hl hl4, ?_⟩
  intro X Y Z _ _ _ _ _ _ F G K r hF hG hr hXZ hYZ hZ hKcard hk hkZ
  have hrpos : 0 < r := by omega
  have hImgG : Finset.image G (Finset.univ : Finset Y) = Finset.univ :=
    image_eq_univ_of_rToOne G r hrpos hG hYZ
  have hcount : (clawCandidates G (K.image F)).card = r * K.card := by
    have h := clawCandidates_card G r hG (K.image F)
      (by rw [hImgG]; exact Finset.subset_univ _)
    rw [hKcard] at h
    simpa [Nat.mul_comm] using h
  refine ⟨hcount, ?_, ?_, ?_, ?_, proposedRecordCount_eq K.card⟩
  · intro y hy
    exact clawCandidates_spec F G K hy
  · unfold proposedClawBudget
    exact le_rfl
  · unfold proposedThreeK
    push_cast
    have hknn : (0 : ℝ) ≤ (K.card : ℝ) := Nat.cast_nonneg K.card
    linarith
  · unfold proposedThreeK
    push_cast
    linarith

theorem rToOneClaw_real_cube_budget (l : ℝ) (hl : 1 < l) (hl4 : l < 4 / 3)
    {N k : ℝ} {r : ℕ} (hr : 0 < r) (hk : 1 ≤ k) (hcube : k ^ 3 = N / (r : ℝ)) :
    proposedClawBudget (groverCoefficient l) N ((r : ℝ) * k)
      ≤ groverCoefficient l * k := by
  have hg : 0 < groverCoefficient l := groverCoefficient_pos l hl hl4
  have h := rToOne_cubeRoot hr hk hcube
  have hs : Real.sqrt (N / ((r : ℝ) * k)) = k := by linarith
  unfold proposedClawBudget
  rw [hs]

end Qatlib.Papers.CollisionProb97.MainResults
