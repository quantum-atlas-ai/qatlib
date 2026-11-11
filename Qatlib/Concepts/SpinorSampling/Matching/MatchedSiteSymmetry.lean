/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.MatchedRecords
import Qatlib.Concepts.SpinorSampling.Matching.UniformMatchedSampling

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Matched Site Symmetry

Matched Site Symmetry constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched
noncomputable section

variable {S : Type} [DecidableEq S]

/-- Complete original `occupied_sites_perm_image` guarantee for `MatchedSiteSymmetry`; all source hypotheses and output obligations are retained. -/
theorem occupied_sites_perm_image [Fintype S] (σ : Equiv.Perm S)
    {n : ℕ} (J : Fin n → S) :
    occupiedSites (σ ∘ J)=(occupiedSites J).image σ := by
  ext x
  simp [occupiedSites]

/-- Complete original `occupied_sites_perm_card` guarantee for `MatchedSiteSymmetry`; all source hypotheses and output obligations are retained. -/
theorem occupied_sites_perm_card [Fintype S] (σ : Equiv.Perm S)
    {n : ℕ} (J : Fin n → S) :
    (occupiedSites (σ ∘ J)).card=(occupiedSites J).card := by
  rw [occupied_sites_perm_image]
  exact Finset.card_image_iff.mpr σ.injective.injOn

/-- Complete original `occupied_sites_perm_mem` guarantee for `MatchedSiteSymmetry`; all source hypotheses and output obligations are retained. -/
theorem occupied_sites_perm_mem [Fintype S] (σ : Equiv.Perm S)
    {n : ℕ} (J : Fin n → S) (x : S) :
    x ∈ occupiedSites (σ ∘ J) ↔ σ.symm x ∈ occupiedSites J := by
  rw [occupied_sites_perm_image]
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨y,hy,hxy⟩
    have hsymm : σ.symm x=y := σ.injective (by simp [hxy])
    simpa [hsymm] using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨σ.symm x,hx,σ.apply_symm_apply x⟩

/-- Complete original `uniform_cohort_address_prob` guarantee for `MatchedSiteSymmetry`; all source hypotheses and output obligations are retained. -/
theorem uniform_cohort_address_prob [Fintype S] [Nonempty S]
    {n : ℕ} (J : Fin n → S) :
    (cohortLaw (uniformLaw S) n).prob J=
      (1/(Fintype.card S : ℝ))^n := by
  change (∏ i : Fin n, (uniformLaw S).prob (J i))=
    (1/(Fintype.card S : ℝ))^n
  simp only [uniformLaw, Finset.prod_const]
  rw [Finset.card_univ, Fintype.card_fin]

/-- Complete original `uniform_cohort_address_perm_invariant` guarantee for `MatchedSiteSymmetry`; all source hypotheses and output obligations are retained. -/
theorem uniform_cohort_address_perm_invariant [Fintype S] [Nonempty S]
    (σ : Equiv.Perm S) {n : ℕ} (J : Fin n → S) :
    (cohortLaw (uniformLaw S) n).prob (σ ∘ J)=
      (cohortLaw (uniformLaw S) n).prob J := by
  rw [uniform_cohort_address_prob,uniform_cohort_address_prob]

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.occupied_sites_perm_image
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.occupied_sites_perm_card
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.occupied_sites_perm_mem
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.uniform_cohort_address_prob
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.uniform_cohort_address_perm_invariant
