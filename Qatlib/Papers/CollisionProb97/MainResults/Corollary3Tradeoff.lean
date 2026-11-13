/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionProb97.MainResults.Theorem2RToOne

/-!
# Scalar space and query tradeoff

This module proves the scalar budget estimate underlying Corollary 3 of
[BrassardHoyerTapp1998Collision]. The theorem `scalar_space_query_tradeoff` bounds the proposed
collision budget by a constant multiple of `T` under `1 ≤ S ≤ T` and `M ≤ S * T²`.

The identity `corollary3_theorem2_quantity` relates the domain size of a regular function to its
image size.

## Main statements

* `scalar_space_query_tradeoff`: For `1 < l < 4 / 3`, there is a positive constant bounding the
  proposed scalar collision budget by `C * T` whenever `0 < M`, `1 ≤ S ≤ T`, and `M ≤ S * T²`,
  as required by Corollary 3 of [BrassardHoyerTapp1998Collision].
* `corollary3_theorem2_quantity`: Expresses the domain cardinality of an `r`-to-one function as
  `r` times its image cardinality, viewed in the real numbers.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Collision]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CollisionProb97.MainResults

open scoped BigOperators

universe u

/-- For `1 < l < 4 / 3`, there is a positive constant bounding the proposed scalar collision
budget by `C * T` whenever `0 < M`, `1 ≤ S ≤ T`, and `M ≤ S * T²`, as required by Corollary
3 of [BrassardHoyerTapp1998Collision]. -/
theorem scalar_space_query_tradeoff (l : ℝ) (hl : 1 < l) (hl4 : l < 4 / 3) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M S T : ℝ), 0 < M → 1 ≤ S → S ≤ T → M ≤ S * T ^ 2 →
        proposedCollisionBudget (groverCoefficient l) M S S ≤ C * T := by
  refine ⟨groverCoefficient l + 2, by
    have h := groverCoefficient_pos l hl hl4
    linarith, ?_⟩
  intro M S T hM hS hST hMT
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have hT1 : (1 : ℝ) ≤ T := le_trans hS hST
  have hTpos : 0 < T := by linarith
  have hMS : M / S ≤ T ^ 2 := by
    rw [div_le_iff₀ hSpos]
    nlinarith
  have hs : Real.sqrt (M / S) ≤ T := by
    have h := Real.sqrt_le_sqrt hMS
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hTpos.le] at h
    exact h
  have hg : 0 < groverCoefficient l := groverCoefficient_pos l hl hl4
  have hgs : groverCoefficient l * Real.sqrt (M / S) ≤ groverCoefficient l * T :=
    mul_le_mul_of_nonneg_left hs hg.le
  unfold proposedCollisionBudget
  nlinarith [hgs]

/-- Expresses the domain cardinality of an `r`-to-one function as `r` times its image
cardinality, viewed in the real numbers. -/
theorem corollary3_theorem2_quantity {X Y : Type u} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (F : X → Y) (r : ℕ) (hF : RToOne F r) :
    (Fintype.card X : ℝ) = (r : ℝ) *
      ((Finset.image F (Finset.univ : Finset X)).card : ℝ) := by
  have h := card_eq_image_card_mul F r hF
  have h' : (Fintype.card X : ℝ) =
      ((Finset.image F (Finset.univ : Finset X)).card : ℝ) * (r : ℝ) := by
    exact_mod_cast h
  rw [h', mul_comm]

end Qatlib.Papers.CollisionProb97.MainResults
