/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionProb97.MainResults.Theorem1TwoToOne

/-!
# Injective claw counts and scalar budgets

This module proves the candidate and scalar budget statements associated with Theorem 4 of
[BrassardHoyerTapp1998Collision]. For injective `F` and `G`, with the domain of `G` as large as
its codomain, each distinct table value gives one claw candidate.

The theorem `bijectionClaw_real_cube_budget` simplifies the proposed claw search budget at an
exact real cube-root table size.

## Main statements

* `rToOne_one_of_injective`: An injective function has fibers of cardinality one over its image.
* `bijectionClaw_count_and_budget`: Under injectivity and the cardinality hypothesis making `G`
  surjective, proves the claw candidate count, witnesses, scalar search bound, and table and
  record counts associated with Theorem 4 of [BrassardHoyerTapp1998Collision].
* `bijectionClaw_real_cube_budget`: At `k³ = N` with `k ≥ 1`, the proposed claw search budget is
  at most `groverCoefficient l * k`.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Collision]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CollisionProb97.MainResults

open scoped BigOperators

universe u

/-- An injective function has fibers of cardinality one over its image. -/
theorem rToOne_one_of_injective {Y Z : Type u} [Fintype Y] [DecidableEq Y]
    [DecidableEq Z] (G : Y → Z) (hG : Function.Injective G) : RToOne G 1 := by
  classical
  intro z hz
  obtain ⟨y0, -, hy0⟩ := Finset.mem_image.mp hz
  have hset : (Finset.univ.filter (fun y => G y = z)) = {y0} := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hy
      exact hG (by rw [hy, hy0])
    · intro h
      rw [h]
      exact hy0
  rw [hset, Finset.card_singleton]

/-- Under injectivity and the cardinality hypothesis making `G` surjective, proves the claw
candidate count, witnesses, scalar search bound, and table and record counts associated with
Theorem 4 of [BrassardHoyerTapp1998Collision]. -/
theorem bijectionClaw_count_and_budget (l : ℝ) (hl : 1 < l) (hl4 : l < 4 / 3) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X Y Z : Type u} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
        [Fintype Z] [DecidableEq Z]
        (F : X → Z) (G : Y → Z) (K : Finset X),
        Function.Injective F → Function.Injective G →
        Fintype.card Y = Fintype.card Z →
        1 ≤ K.card → K.card ≤ Fintype.card X →
        (clawCandidates G (K.image F)).card = K.card ∧
        (∀ y ∈ clawCandidates G (K.image F), ∃ x0 ∈ K, F x0 = G y) ∧
        proposedClawBudget (groverCoefficient l) (Fintype.card Y)
            (clawCandidates G (K.image F)).card
          ≤ C * Real.sqrt ((Fintype.card Y : ℝ) / K.card) ∧
        (tableEntryCount K.card : ℝ) = K.card ∧
        proposedRecordCount K.card = K.card := by
  refine ⟨groverCoefficient l, groverCoefficient_pos l hl hl4, ?_⟩
  intro X Y Z _ _ _ _ _ _ F G K hF hG hYZ hk hkN
  have hG1 : RToOne G 1 := rToOne_one_of_injective G hG
  have hImgG : Finset.image G (Finset.univ : Finset Y) = Finset.univ :=
    image_eq_univ_of_rToOne G 1 Nat.zero_lt_one hG1 (by simpa using hYZ)
  have hcardK : (K.image F).card = K.card :=
    Finset.card_image_of_injOn (fun x _ y _ h => hF h)
  have hcount : (clawCandidates G (K.image F)).card = K.card := by
    have h := clawCandidates_card G 1 hG1 (K.image F)
      (by rw [hImgG]; exact Finset.subset_univ _)
    rw [hcardK] at h
    simpa using h
  refine ⟨hcount, ?_, ?_, rfl, proposedRecordCount_eq K.card⟩
  · intro y hy
    exact clawCandidates_spec F G K hy
  · rw [hcount]
    exact le_rfl

/-- At `k³ = N` with `k ≥ 1`, the proposed claw search budget is at most `groverCoefficient l *
k`. -/
theorem bijectionClaw_real_cube_budget (l : ℝ) (hl : 1 < l) (hl4 : l < 4 / 3)
    {N k : ℝ} (hk : 1 ≤ k) (hcube : k ^ 3 = N) :
    proposedClawBudget (groverCoefficient l) N k ≤ groverCoefficient l * k := by
  have hg : 0 < groverCoefficient l := groverCoefficient_pos l hl hl4
  have h := twoToOne_cubeRoot hk hcube
  have hs : Real.sqrt (N / k) = k := by linarith
  unfold proposedClawBudget
  rw [hs]

end Qatlib.Papers.CollisionProb97.MainResults
