/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionProb97.MainResults.CollisionDefs

/-!
# Counting collision and claw candidates

This module counts fibers and marked candidates for the collision and claw constructions in
[BrassardHoyerTapp1998Collision]. The predicate `RToOne` gives exact fiber sizes on the image,
yielding domain cardinality identities and candidate counts.

The results `collisionCandidates_spec` and `clawCandidates_spec` recover witnesses from marked
inputs.

## Main statements

* `collisionCandidates_card`: If `F` is injective on the table inputs `K`, the number of
  external collision candidates is `(r - 1) * K.card`.
* `clawCandidates_card`: For an `r`-to-one function `G`, the number of claw candidates over a
  subset `T` of its image is `T.card * r`.
* `collisionCandidates_spec`: Every collision candidate has a distinct table input with the same
  function value.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Collision]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CollisionProb97.MainResults

open scoped BigOperators

universe u

/-- For an `r`-to-one function, the preimage of a finite subset of its image has cardinality
`T.card * r`. -/
theorem card_univ_filter_fiber_mem {X Y : Type u} [Fintype X] [DecidableEq X]
    [DecidableEq Y] (F : X → Y) (r : ℕ) (hF : RToOne F r) {T : Finset Y}
    (hT : T ⊆ Finset.image F (Finset.univ : Finset X)) :
    (Finset.univ.filter (fun x => F x ∈ T)).card = T.card * r := by
  classical
  rw [← Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset X) T F]
  rw [Finset.sum_congr rfl (fun y hy => hF y (hT hy))]
  exact Finset.sum_const_nat (fun _ _ => rfl)

/-- The domain cardinality of an `r`-to-one function equals its image cardinality multiplied by
`r`. -/
theorem card_eq_image_card_mul {X Y : Type u} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (F : X → Y) (r : ℕ) (hF : RToOne F r) :
    Fintype.card X = (Finset.image F (Finset.univ : Finset X)).card * r := by
  classical
  have h := Finset.card_eq_sum_card_image F (Finset.univ : Finset X)
  rw [Finset.card_univ] at h
  rw [h]
  rw [Finset.sum_congr rfl (fun y hy => hF y hy)]
  exact Finset.sum_const_nat (fun _ _ => rfl)

/-- An `r`-to-one function with positive `r` is surjective when its domain cardinality is `r`
times its codomain cardinality. -/
theorem image_eq_univ_of_rToOne {X Y : Type u} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (F : X → Y) (r : ℕ) (hr : 0 < r)
    (hF : RToOne F r) (hcard : Fintype.card X = r * Fintype.card Y) :
    Finset.image F (Finset.univ : Finset X) = Finset.univ := by
  classical
  have hsum : Fintype.card X =
      (Finset.image F (Finset.univ : Finset X)).card * r :=
    card_eq_image_card_mul F r hF
  have hcardImg : (Finset.image F (Finset.univ : Finset X)).card = Fintype.card Y := by
    have hmul : (Finset.image F (Finset.univ : Finset X)).card * r =
        Fintype.card Y * r := by
      rw [← hsum, hcard, Nat.mul_comm]
    exact Nat.eq_of_mul_eq_mul_right hr hmul
  exact Finset.eq_univ_of_card _ hcardImg

/-- If `F` is injective on the table inputs `K`, the number of external collision candidates is
`(r - 1) * K.card`. -/
theorem collisionCandidates_card {X Y : Type u} [Fintype X] [DecidableEq X]
    [DecidableEq Y] (F : X → Y) (r : ℕ) (hF : RToOne F r) (K : Finset X)
    (hinj : Set.InjOn F (K : Set X)) :
    (collisionCandidates F K).card = (r - 1) * K.card := by
  classical
  have hTsub : K.image F ⊆ Finset.image F (Finset.univ : Finset X) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
  have hA : (Finset.univ.filter (fun x => F x ∈ K.image F)).card = K.card * r := by
    have h := card_univ_filter_fiber_mem F r hF hTsub
    rwa [Finset.card_image_of_injOn hinj] at h
  have hsub : K ⊆ Finset.univ.filter (fun x => F x ∈ K.image F) := by
    intro x hx
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  have heq : collisionCandidates F K =
      Finset.univ.filter (fun x => F x ∈ K.image F) \ K := by
    ext x
    simp only [collisionCandidates, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff, and_comm]
  rw [heq, Finset.card_sdiff_of_subset hsub, hA]
  have harith : K.card * r - K.card = (r - 1) * K.card := by
    have h1 : (r - 1) * K.card = r * K.card - 1 * K.card := Nat.sub_mul r 1 K.card
    rw [h1, Nat.one_mul, Nat.mul_comm r K.card]
  exact harith

/-- For an `r`-to-one function `G`, the number of claw candidates over a subset `T` of its image
is `T.card * r`. -/
theorem clawCandidates_card {Y Z : Type u} [Fintype Y] [DecidableEq Y] [DecidableEq Z]
    (G : Y → Z) (r : ℕ) (hG : RToOne G r) (T : Finset Z)
    (hT : T ⊆ Finset.image G (Finset.univ : Finset Y)) :
    (clawCandidates G T).card = T.card * r :=
  card_univ_filter_fiber_mem G r hG hT

/-- Every collision candidate has a distinct table input with the same function value. -/
theorem collisionCandidates_spec {X Y : Type u} [Fintype X] [DecidableEq X]
    [DecidableEq Y] (F : X → Y) (K : Finset X) {x1 : X}
    (hx : x1 ∈ collisionCandidates F K) :
    ∃ x0 ∈ K, x0 ≠ x1 ∧ F x0 = F x1 := by
  classical
  simp only [collisionCandidates, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  obtain ⟨hxK, hximg⟩ := hx
  obtain ⟨x0, hx0, hFx0⟩ := Finset.mem_image.mp hximg
  refine ⟨x0, hx0, ?_, hFx0⟩
  intro h
  exact hxK (h ▸ hx0)

/-- Every claw candidate for the table image `K.image F` has a matching input in `K`. -/
theorem clawCandidates_spec {X Y Z : Type u} [Fintype Y] [DecidableEq Y]
    [DecidableEq X] [DecidableEq Z]
    (F : X → Z) (G : Y → Z) (K : Finset X) {y : Y}
    (hy : y ∈ clawCandidates G (K.image F)) : ∃ x0 ∈ K, F x0 = G y := by
  classical
  simp only [clawCandidates, Finset.mem_filter, Finset.mem_univ, true_and] at hy
  exact Finset.mem_image.mp hy

end Qatlib.Papers.CollisionProb97.MainResults
