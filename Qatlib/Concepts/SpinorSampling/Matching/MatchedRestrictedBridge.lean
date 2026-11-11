/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.RestrictedOccupancyTail

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

/-- Complete original `restricted_occupied_shifted_image` guarantee for `MatchedRestrictedBridge`; all source hypotheses and output obligations are retained. -/
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

/-- Complete original `restricted_occupied_shifted_card` guarantee for `MatchedRestrictedBridge`; all source hypotheses and output obligations are retained. -/
theorem restricted_occupied_shifted_card (τ : Equiv.Perm S) {n m : ℕ}
    (J : Fin n → S) (K : Fin m → S) :
    (restrictedOccupied ((occupiedSites J).image τ) K).card = (matchedSites J K τ).card := by
  rw [restricted_occupied_shifted_image]
  exact Finset.card_image_of_injective _ τ.injective

variable [Fintype S] [Nonempty S]

/-- Complete original `matched_card_conditional_lower_tail` guarantee for `MatchedRestrictedBridge`; all source hypotheses and output obligations are retained. -/
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
