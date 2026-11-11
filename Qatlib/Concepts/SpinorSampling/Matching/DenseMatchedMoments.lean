/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.OccupiedAddressMoments
import Qatlib.Concepts.SpinorSampling.Matching.MatchedSiteSymmetry
import Qatlib.Concepts.SpinorSampling.Matching.SelectedSignProducts

set_option backward.isDefEq.respectTransparency false

/-!
# Dense Matched Moments

Dense Matched Moments constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched
noncomputable section
open scoped BigOperators Classical

variable {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]

/-- Construction for occupied Site Mass in the dense matched moments model. -/
def occupiedSiteMass (n : ℕ) (x : S) : ℝ :=
  (cohortLaw (uniformLaw S) n).expect (fun J => if x∈occupiedSites J then 1 else 0)

/-- Complete original `uniform_cohort_relabel_expect` guarantee for `DenseMatchedMoments`; all source hypotheses and output obligations are retained. -/
theorem uniform_cohort_relabel_expect (n : ℕ) (σ : Equiv.Perm S) (f : (Fin n → S) → ℝ) :
    (cohortLaw (uniformLaw S) n).expect (fun J => f (σ ∘ J))=
      (cohortLaw (uniformLaw S) n).expect f := by
  let e : (Fin n → S) ≃ (Fin n → S) := Equiv.piCongrRight (fun _ => σ)
  have he (J : Fin n → S) : e J=σ ∘ J := rfl
  have h := e.sum_comp (fun J => (cohortLaw (uniformLaw S) n).prob J*f J)
  simp_rw [he,uniform_cohort_address_perm_invariant] at h
  exact h

/-- Complete original `occupied_site_mass_constant` guarantee for `DenseMatchedMoments`; all source hypotheses and output obligations are retained. -/
theorem occupied_site_mass_constant (n : ℕ) (x y : S) :
    occupiedSiteMass n x=occupiedSiteMass n y := by
  have h := uniform_cohort_relabel_expect n (Equiv.swap x y)
    (fun J => if x∈occupiedSites J then (1 : ℝ) else 0)
  simp only [occupied_sites_perm_mem,Equiv.symm_swap,Equiv.swap_apply_left] at h
  exact h.symm

/-- Complete original `occupied_site_mass_formula` guarantee for `DenseMatchedMoments`; all source hypotheses and output obligations are retained. -/
theorem occupied_site_mass_formula (n : ℕ) (x : S) :
    occupiedSiteMass n x=expectedOccupied (S:=S) n/(Fintype.card S : ℝ) := by
  have hcount (J : Fin n → S) : occupiedCount J=∑ y : S,if y∈occupiedSites J then (1 : ℝ) else 0 := by
    rw [sum_mem_indicator]
    simp [occupiedCount]
  have hsum : expectedOccupied (S:=S) n=(Fintype.card S : ℝ)*occupiedSiteMass n x := by
    change (cohortLaw (uniformLaw S) n).expect (fun J => occupiedCount J)=_
    simp_rw [hcount,finite_expect_sum]
    change (∑ y : S,occupiedSiteMass n y)=_
    simp_rw [occupied_site_mass_constant n _ x]
    simp
  have hM : (Fintype.card S : ℝ)≠0 := by exact_mod_cast Fintype.card_pos.ne'
  rw [hsum,mul_div_cancel_left₀ _ hM]

/-- Construction for matched Address Count in the dense matched moments model. -/
def matchedAddressCount {n m : ℕ} (τ : S → S) (J : Fin n → S) (L : Fin m → S) : ℝ :=
  (matchedSites J L τ).card

/-- Complete original `matched_address_mean` guarantee for `DenseMatchedMoments`; all source hypotheses and output obligations are retained. -/
theorem matched_address_mean (τ : S → S) (n m : ℕ) :
    (productLaw (cohortLaw (uniformLaw S) n) (cohortLaw (uniformLaw S) m)).expect
      (fun z => matchedAddressCount τ z.1 z.2)=
        ∑ x : S,occupiedSiteMass n x*occupiedSiteMass m (τ x) := by
  have hcount (J : Fin n → S) (L : Fin m → S) :
      matchedAddressCount τ J L=
        ∑ x : S,(if x∈occupiedSites J then (1 : ℝ) else 0)*
          (if τ x∈occupiedSites L then 1 else 0) := by
    have hc : matchedAddressCount τ J L=
        ∑ x : S,if x∈matchedSites J L τ then (1 : ℝ) else 0 := by
      rw [sum_mem_indicator]; simp [matchedAddressCount]
    rw [hc]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x∈occupiedSites J <;> by_cases hy : τ x∈occupiedSites L <;>
      simp [mem_matched_sites,hx,hy]
  have hinner (J : Fin n → S) :
      (cohortLaw (uniformLaw S) m).expect (fun L => matchedAddressCount τ J L)=
        ∑ x : S,(if x∈occupiedSites J then (1 : ℝ) else 0)*occupiedSiteMass m (τ x) := by
    simp_rw [hcount,finite_expect_sum,finite_expect_mul]
    rfl
  rw [product_law_expect]
  simp_rw [hinner,finite_expect_sum]
  apply Finset.sum_congr rfl
  intro x _
  have hf (J : Fin n → S) :
      (if x∈occupiedSites J then (1 : ℝ) else 0)*occupiedSiteMass m (τ x)=
        occupiedSiteMass m (τ x)*(if x∈occupiedSites J then 1 else 0) := by ring
  simp_rw [hf,finite_expect_mul]
  exact mul_comm _ _

/-- Complete original `matched_dense_mean_lower` guarantee for `DenseMatchedMoments`; all source hypotheses and output obligations are retained. -/
theorem matched_dense_mean_lower (τ : S → S) :
    (Fintype.card S : ℝ)/4≤
      (productLaw (cohortLaw (uniformLaw S) (Fintype.card S))
        (cohortLaw (uniformLaw S) (Fintype.card S))).expect
          (fun z => matchedAddressCount τ z.1 z.2) := by
  have hM : (0 : ℝ)<Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hhalf (x : S) : (1 : ℝ)/2≤occupiedSiteMass (Fintype.card S) x := by
    rw [occupied_site_mass_formula]
    apply (le_div_iff₀ hM).mpr
    nlinarith [expected_occupied_half (S:=S) (Fintype.card S) (le_refl _)]
  rw [matched_address_mean τ (Fintype.card S) (Fintype.card S)]
  calc
    _ = ∑ _x : S,(1 : ℝ)/4 := by simp; ring
    _ ≤ _ := Finset.sum_le_sum fun x _ => by
      nlinarith [hhalf x,hhalf (τ x),
        mul_nonneg (sub_nonneg.mpr (hhalf x)) (sub_nonneg.mpr (hhalf (τ x)))]

omit [Fintype S] [Nonempty S] in
/-- Complete original `matched_count_left_coordinate` guarantee for `DenseMatchedMoments`; all source hypotheses and output obligations are retained. -/
theorem matched_count_left_coordinate {n m : ℕ} (τ : S → S)
    (J J' : Fin n → S) (L : Fin m → S) (i : Fin n)
    (h : ∀ j,j≠i → J j=J' j) :
    |matchedAddressCount τ J L-matchedAddressCount τ J' L|≤1 := by
  have hsub (A B : Fin n → S) (hAB : ∀ j,j≠i → A j=B j) :
      matchedSites A L τ⊆insert (A i) (matchedSites B L τ) := by
    intro x hx
    rcases (mem_matched_sites A L τ x).mp hx with ⟨hx,hy⟩
    rcases Finset.mem_image.mp hx with ⟨j,_,hj⟩
    by_cases hi : j=i
    · subst j
      rw [← hj]
      exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      apply (mem_matched_sites B L τ x).mpr
      exact ⟨Finset.mem_image.mpr ⟨j,Finset.mem_univ _,(hAB j hi).symm.trans hj⟩,hy⟩
  have hab := (Finset.card_le_card (hsub J J' h)).trans (Finset.card_insert_le _ _)
  have hba := (Finset.card_le_card (hsub J' J (fun j hj => (h j hj).symm))).trans
    (Finset.card_insert_le _ _)
  have habR : matchedAddressCount τ J L≤matchedAddressCount τ J' L+1 := by
    dsimp [matchedAddressCount]; exact_mod_cast hab
  have hbaR : matchedAddressCount τ J' L≤matchedAddressCount τ J L+1 := by
    dsimp [matchedAddressCount]; exact_mod_cast hba
  exact abs_le.mpr ⟨by linarith,by linarith⟩

omit [Fintype S] [Nonempty S] in
/-- Complete original `matched_count_swap` guarantee for `DenseMatchedMoments`; all source hypotheses and output obligations are retained. -/
theorem matched_count_swap {n m : ℕ} (τ : Equiv.Perm S) (J : Fin n → S) (L : Fin m → S) :
    matchedAddressCount τ J L=matchedAddressCount τ.symm L J := by
  have hs : (matchedSites J L τ).image τ=matchedSites L J τ.symm := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨y,hy,rfl⟩
      exact (mem_matched_sites L J τ.symm _).mpr
        ⟨((mem_matched_sites J L τ y).mp hy).2,
          by simpa using ((mem_matched_sites J L τ y).mp hy).1⟩
    · intro hx
      rcases (mem_matched_sites L J τ.symm x).mp hx with ⟨hx,hy⟩
      exact Finset.mem_image.mpr ⟨τ.symm x,
        (mem_matched_sites J L τ _).mpr ⟨hy,by simpa using hx⟩,τ.apply_symm_apply x⟩
  have hc := congrArg Finset.card hs
  rw [Finset.card_image_iff.mpr τ.injective.injOn] at hc
  dsimp [matchedAddressCount]
  exact_mod_cast hc

omit [Fintype S] [Nonempty S] in
/-- Complete original `matched_count_right_coordinate` guarantee for `DenseMatchedMoments`; all source hypotheses and output obligations are retained. -/
theorem matched_count_right_coordinate {n m : ℕ} (τ : Equiv.Perm S)
    (J : Fin n → S) (L L' : Fin m → S) (i : Fin m)
    (h : ∀ j,j≠i → L j=L' j) :
    |matchedAddressCount τ J L-matchedAddressCount τ J L'|≤1 := by
  rw [matched_count_swap τ J L,matched_count_swap τ J L']
  exact matched_count_left_coordinate τ.symm L L' J i h

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.occupied_site_mass_formula
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.matched_address_mean
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.matched_dense_mean_lower
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.matched_count_left_coordinate
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.matched_count_right_coordinate
