/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.SpinorSampling.Matching.RestrictedOccupancyTail

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Matched Restricted Bridge

Matched Restricted Bridge constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched
noncomputable section
open scoped BigOperators
open Qatlib

variable {S : Type} [DecidableEq S]

/-- The right-array sites that belong to the shifted left occupied set are exactly the images
under `τ` of the matched sites. -/
theorem restricted_occupied_shifted_image (τ : Equiv.Perm S) {n m : ℕ}
    (J : Fin n → S) (K : Fin m → S) :
    restrictedOccupied ((occupiedSites J).image τ) K = (matchedSites J K τ).image τ := by
  ext y
  simp only [restrictedOccupied, matchedSites, Finset.mem_inter, Finset.mem_image,
    Finset.mem_filter]
  constructor
  · rintro ⟨hyK,x,hxJ,hxy⟩
    refine ⟨x,⟨hxJ,?_⟩,hxy⟩
    rwa [hxy]
  · rintro ⟨x,⟨hxJ,hxK⟩,hxy⟩
    refine ⟨?_,x,hxJ,hxy⟩
    rwa [← hxy]

/-- Counting the right occupied sites in the image of the left occupied set gives the
matched-set count because the shift is a permutation. -/
theorem restricted_occupied_shifted_card (τ : Equiv.Perm S) {n m : ℕ}
    (J : Fin n → S) (K : Fin m → S) :
    (restrictedOccupied ((occupiedSites J).image τ) K).card = (matchedSites J K τ).card := by
  rw [restricted_occupied_shifted_image]
  exact Finset.card_image_of_injective _ τ.injective

variable [Fintype S] [Nonempty S]

/-- Fix the left array with `a` occupied sites. For `m ≤ |S|` independent uniform right draws,
fewer than `r = m*a/(8*|S|)` sites match under the permutation with probability at most
`exp (-r)`. -/
theorem matched_card_conditional_lower_tail (τ : Equiv.Perm S) {n m : ℕ}
    (J : Fin n → S) (hm : m ≤ Fintype.card S) :
    (cohortLaw (uniformLaw S) m).expect (fun K =>
      if ((matchedSites J K τ).card : ℝ) <
        (m : ℝ)*((occupiedSites J).card : ℝ)/(8*(Fintype.card S : ℝ)) then 1 else 0) ≤
      Real.exp (-(m : ℝ)*((occupiedSites J).card : ℝ)/(8*(Fintype.card S : ℝ))) := by
  have h := restricted_occupancy_lower_tail ((occupiedSites J).image τ) m hm
  unfold restrictedHitBadMass at h
  simp_rw [restricted_occupied_shifted_card] at h
  have hc : ((occupiedSites J).image τ).card = (occupiedSites J).card :=
    Finset.card_image_of_injective _ τ.injective
  simpa only [hc] using h

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.restricted_occupied_shifted_image
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.restricted_occupied_shifted_card
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.matched_card_conditional_lower_tail
