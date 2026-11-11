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
# Matched Event Symmetry

Matched Event Symmetry constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched
noncomputable section

variable {S : Type} [Fintype S] [DecidableEq S]

omit [Fintype S] in
/-- Complete original `occupied_sites_perm_mem_local` guarantee for `MatchedEventSymmetry`; all source hypotheses and output obligations are retained. -/
theorem occupied_sites_perm_mem_local (σ : Equiv.Perm S)
    {n : ℕ} (J : Fin n → S) (x : S) :
    x ∈ occupiedSites (σ ∘ J) ↔ σ.symm x ∈ occupiedSites J := by
  simp only [occupiedSites, Finset.mem_image, Finset.mem_univ, true_and,
    Function.comp_apply]
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a, by simpa using congrArg σ.symm ha⟩
  · rintro ⟨a,ha⟩
    exact ⟨a, by simpa using congrArg σ ha⟩

omit [Fintype S] in
/-- Complete original `matched_sites_perm_conjugate` guarantee for `MatchedEventSymmetry`; all source hypotheses and output obligations are retained. -/
theorem matched_sites_perm_conjugate [Nonempty S]
    (σ τ : Equiv.Perm S) {n m : ℕ} (J : Fin n → S) (K : Fin m → S) :
    matchedSites (σ ∘ J) (σ ∘ K) (σ ∘ τ ∘ σ.symm) =
      (matchedSites J K τ).image σ := by
  classical
  ext x
  simp only [matchedSites, Finset.mem_filter, Finset.mem_image]
  simp only [occupiedSites, Finset.mem_image,
    Finset.mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨⟨i,hi⟩,⟨j,hj⟩⟩
    refine ⟨J i, ⟨⟨i,rfl⟩,⟨j,?_⟩⟩,hi⟩
    have hj' : K j=τ (σ.symm x) := σ.injective hj
    have hi' : J i=σ.symm x := by simpa using congrArg σ.symm hi
    simpa [hi'] using hj'
  · rintro ⟨a,⟨⟨i,hia⟩,⟨j,hja⟩⟩,ha⟩
    refine ⟨⟨i,?_⟩,⟨j,?_⟩⟩
    · simpa [hia] using ha
    · have hax : σ.symm x=a := by
        apply σ.injective
        simpa using ha.symm
      simpa [hax] using congrArg σ hja

/-- Complete original `uniform_pair_address_perm_invariant` guarantee for `MatchedEventSymmetry`; all source hypotheses and output obligations are retained. -/
theorem uniform_pair_address_perm_invariant [Nonempty S]
    (σ : Equiv.Perm S) {n m : ℕ} (J : Fin n → S) (K : Fin m → S) :
    (cohortLaw (uniformLaw S) n).prob (σ ∘ J) *
        (cohortLaw (uniformLaw S) m).prob (σ ∘ K) =
      (cohortLaw (uniformLaw S) n).prob J *
        (cohortLaw (uniformLaw S) m).prob K := by
  have hJ : (cohortLaw (uniformLaw S) n).prob (σ ∘ J) =
      (cohortLaw (uniformLaw S) n).prob J := by
    change (∏ i : Fin n, (uniformLaw S).prob ((σ ∘ J) i)) =
      ∏ i : Fin n, (uniformLaw S).prob (J i)
    simp only [uniformLaw, Finset.prod_const]
  have hK : (cohortLaw (uniformLaw S) m).prob (σ ∘ K) =
      (cohortLaw (uniformLaw S) m).prob K := by
    change (∏ i : Fin m, (uniformLaw S).prob ((σ ∘ K) i)) =
      ∏ i : Fin m, (uniformLaw S).prob (K i)
    simp only [uniformLaw, Finset.prod_const]
  rw [hJ,hK]

/-- Complete original `uniform_pair_address_independent_perm_invariant` guarantee for `MatchedEventSymmetry`; all source hypotheses and output obligations are retained. -/
theorem uniform_pair_address_independent_perm_invariant [Nonempty S]
    (σ ρ : Equiv.Perm S) {n m : ℕ} (J : Fin n → S) (K : Fin m → S) :
    (cohortLaw (uniformLaw S) n).prob (σ ∘ J) *
        (cohortLaw (uniformLaw S) m).prob (ρ ∘ K) =
      (cohortLaw (uniformLaw S) n).prob J *
        (cohortLaw (uniformLaw S) m).prob K := by
  have hJ : (cohortLaw (uniformLaw S) n).prob (σ ∘ J) =
      (cohortLaw (uniformLaw S) n).prob J := by
    change (∏ i : Fin n, (uniformLaw S).prob ((σ ∘ J) i)) =
      ∏ i : Fin n, (uniformLaw S).prob (J i)
    simp only [uniformLaw, Finset.prod_const]
  have hK : (cohortLaw (uniformLaw S) m).prob (ρ ∘ K) =
      (cohortLaw (uniformLaw S) m).prob K := by
    change (∏ i : Fin m, (uniformLaw S).prob ((ρ ∘ K) i)) =
      ∏ i : Fin m, (uniformLaw S).prob (K i)
    simp only [uniformLaw, Finset.prod_const]
  rw [hJ,hK]

omit [Fintype S] in
/-- Complete original `exists_perm_map_finset` guarantee for `MatchedEventSymmetry`; all source hypotheses and output obligations are retained. -/
theorem exists_perm_map_finset (A B : Finset S)
    (hcard : A.card=B.card) : ∃ σ : Equiv.Perm S, A.image σ=B := by
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_map_finset_eq A B hcard
  exact ⟨σ, by simpa [Finset.map_eq_image] using hσ⟩

omit [Fintype S] in
/-- Complete original `matched_sites_perm_fixed_shift` guarantee for `MatchedEventSymmetry`; all source hypotheses and output obligations are retained. -/
theorem matched_sites_perm_fixed_shift [Nonempty S]
    (σ τ : Equiv.Perm S) {n m : ℕ} (J : Fin n → S) (K : Fin m → S) :
    matchedSites (σ ∘ J) ((τ ∘ σ ∘ τ.symm) ∘ K) τ =
      (matchedSites J K τ).image σ := by
  classical
  ext x
  rw [mem_matched_sites (σ ∘ J) ((τ ∘ σ ∘ τ.symm) ∘ K) τ x]
  simp only [matchedSites, Finset.mem_filter, Finset.mem_image,
    occupiedSites, Finset.mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨⟨i,hi⟩,⟨j,hj⟩⟩
    refine ⟨J i, ⟨⟨i,rfl⟩,⟨j,?_⟩⟩,hi⟩
    have hj0 : σ (τ.symm (K j))=x := τ.injective hj
    have hj1 : τ.symm (K j)=σ.symm x := σ.injective (by simpa using hj0)
    have hj' : K j=τ (σ.symm x) := by
      simpa using congrArg τ hj1
    have hi' : J i=σ.symm x := by simpa using congrArg σ.symm hi
    simpa [hi'] using hj'
  · rintro ⟨a,⟨⟨i,hia⟩,⟨j,hja⟩⟩,ha⟩
    refine ⟨⟨i,?_⟩,⟨j,?_⟩⟩
    · simpa [hia] using ha
    ·
      have hax : σ.symm x=a := by
        apply σ.injective
        simpa using ha.symm
      simpa [hja, hax] using ha

/-- Construction for fixed Shift Address Equiv in the matched event symmetry model. -/
def fixedShiftAddressEquiv [Nonempty S]
    (σ τ : Equiv.Perm S) (n m : ℕ) :
    ((Fin n → S) × (Fin m → S)) ≃ ((Fin n → S) × (Fin m → S)) where
  toFun z := (σ ∘ z.1,(τ ∘ σ ∘ τ.symm) ∘ z.2)
  invFun z := (σ.symm ∘ z.1,(τ ∘ σ.symm ∘ τ.symm) ∘ z.2)
  left_inv z := by
    rcases z with ⟨J,K⟩
    apply Prod.ext
    · funext i
      simp [Function.comp_apply]
    · funext i
      simp [Function.comp_apply]
  right_inv z := by
    rcases z with ⟨J,K⟩
    apply Prod.ext
    · funext i
      simp [Function.comp_apply]
    · funext i
      simp [Function.comp_apply]

omit [Fintype S] in
/-- Complete original `matched_card_fixed_shift_invariant` guarantee for `MatchedEventSymmetry`; all source hypotheses and output obligations are retained. -/
theorem matched_card_fixed_shift_invariant [Nonempty S]
    (σ τ : Equiv.Perm S) {n m : ℕ} (J : Fin n → S) (K : Fin m → S) :
    (matchedSites (σ ∘ J) ((τ ∘ σ ∘ τ.symm) ∘ K) τ).card =
      (matchedSites J K τ).card := by
  rw [matched_sites_perm_fixed_shift]
  exact Finset.card_image_iff.mpr σ.injective.injOn

/-- Construction for matched Fiber Predicate in the matched event symmetry model. -/
def matchedFiberPredicate (τ : Equiv.Perm S) (A : Finset S) {n m : ℕ}
    (z : (Fin n → S) × (Fin m → S)) : Prop :=
  matchedSites z.1 z.2 τ=A

/-- Typeclass instance for matched Fiber Fintype in the matched event symmetry model. -/
instance matchedFiberFintype (τ : Equiv.Perm S) (A : Finset S)
    {n m : ℕ} : Fintype {z : (Fin n → S) × (Fin m → S) // matchedFiberPredicate τ A z} :=
  Fintype.ofFinite _

omit [Fintype S] in
/-- Construction for fixed shift fiber equiv in the matched event symmetry model. -/
def fixed_shift_fiber_equiv [Nonempty S]
    (σ τ : Equiv.Perm S) {n m : ℕ} (A B : Finset S)
    (hAB : A.image σ=B) :
    {z : (Fin n → S) × (Fin m → S) // matchedFiberPredicate τ A z} ≃
      {z : (Fin n → S) × (Fin m → S) // matchedFiberPredicate τ B z} := by
  have hBA : B.image σ.symm=A := by
    rw [← hAB, Finset.image_image]
    simp
  apply (fixedShiftAddressEquiv σ τ n m).subtypeEquiv
  intro z
  constructor
  · intro hz
    change matchedSites (σ ∘ z.1) ((τ ∘ σ ∘ τ.symm) ∘ z.2) τ=B
    rw [matched_sites_perm_fixed_shift, hz, hAB]
  · intro hz
    change matchedSites (σ ∘ z.1) ((τ ∘ σ ∘ τ.symm) ∘ z.2) τ=B at hz
    rw [matched_sites_perm_fixed_shift] at hz
    change matchedSites z.1 z.2 τ=A
    rw [← hBA, ← hz]
    simp only [Finset.image_image]
    simp

/-- Construction for pair Address Mass in the matched event symmetry model. -/
def pairAddressMass [Nonempty S]
    {n m : ℕ} (z : (Fin n → S) × (Fin m → S)) : ℝ :=
  (cohortLaw (uniformLaw S) n).prob z.1 *
    (cohortLaw (uniformLaw S) m).prob z.2

/-- Complete original `pairAddressMass_fixed_shift` guarantee for `MatchedEventSymmetry`; all source hypotheses and output obligations are retained. -/
theorem pairAddressMass_fixed_shift [Nonempty S]
    (σ τ : Equiv.Perm S) {n m : ℕ} (z : (Fin n → S) × (Fin m → S)) :
    pairAddressMass ((fixedShiftAddressEquiv σ τ n m) z) = pairAddressMass z := by
  rcases z with ⟨J,K⟩
  exact uniform_pair_address_independent_perm_invariant σ
    (τ.symm.trans (σ.trans τ)) J K

/-- Complete original `matched_fiber_mass_equal` guarantee for `MatchedEventSymmetry`; all source hypotheses and output obligations are retained. -/
theorem matched_fiber_mass_equal [Nonempty S]
    (σ τ : Equiv.Perm S) {n m : ℕ} (A B : Finset S)
    (hAB : A.image σ=B) :
    (∑ z : {z : (Fin n → S) × (Fin m → S) // matchedFiberPredicate τ A z},
      pairAddressMass z.1) =
    (∑ z : {z : (Fin n → S) × (Fin m → S) // matchedFiberPredicate τ B z},
      pairAddressMass z.1) := by
  let e : {z : (Fin n → S) × (Fin m → S) // matchedFiberPredicate τ A z} ≃
      {z : (Fin n → S) × (Fin m → S) // matchedFiberPredicate τ B z} :=
    fixed_shift_fiber_equiv σ τ A B hAB
  apply Fintype.sum_equiv e
  intro z
  change pairAddressMass z.1 = pairAddressMass ((fixedShiftAddressEquiv σ τ n m) z.1)
  exact (pairAddressMass_fixed_shift σ τ z.1).symm

/-- Complete original `matched_fiber_mass_card_invariant` guarantee for `MatchedEventSymmetry`; all source hypotheses and output obligations are retained. -/
theorem matched_fiber_mass_card_invariant [Nonempty S]
    (τ : Equiv.Perm S) {n m : ℕ} (A B : Finset S)
    (hcard : A.card=B.card) :
    (∑ z : {z : (Fin n → S) × (Fin m → S) // matchedFiberPredicate τ A z},
      pairAddressMass z.1) =
    (∑ z : {z : (Fin n → S) × (Fin m → S) // matchedFiberPredicate τ B z},
      pairAddressMass z.1) := by
  obtain ⟨σ,hσ⟩ := exists_perm_map_finset A B hcard
  exact matched_fiber_mass_equal σ τ A B hσ

/-- Complete original `matched_card_event_mass_decomposition` guarantee for `MatchedEventSymmetry`; all source hypotheses and output obligations are retained. -/
theorem matched_card_event_mass_decomposition [Nonempty S]
    (τ : Equiv.Perm S) {n m k : ℕ} :
    (∑ A ∈ (Finset.univ : Finset S).powersetCard k,
      ∑ z ∈ (Finset.univ : Finset ((Fin n → S) × (Fin m → S))).filter
        (fun z => matchedSites z.1 z.2 τ=A), pairAddressMass z) =
    ∑ z ∈ (Finset.univ : Finset ((Fin n → S) × (Fin m → S))).filter
      (fun z => (matchedSites z.1 z.2 τ) ∈
        (Finset.univ : Finset S).powersetCard k), pairAddressMass z := by
  simpa only [Finset.sum_filter] using
    (Finset.sum_fiberwise_eq_sum_filter
      (s := (Finset.univ : Finset ((Fin n → S) × (Fin m → S))))
      (t := (Finset.univ : Finset S).powersetCard k)
      (g := fun z => matchedSites z.1 z.2 τ) (f := pairAddressMass))

/-- Complete original `matched_card_event_mass_const` guarantee for `MatchedEventSymmetry`; all source hypotheses and output obligations are retained. -/
theorem matched_card_event_mass_const [Nonempty S]
    (τ : Equiv.Perm S) {n m k : ℕ} (c : ℝ)
    (hc : ∀ A ∈ (Finset.univ : Finset S).powersetCard k,
      (∑ z ∈ (Finset.univ : Finset ((Fin n → S) × (Fin m → S))).filter
        (fun z => matchedSites z.1 z.2 τ=A), pairAddressMass z)=c) :
    (∑ z ∈ (Finset.univ : Finset ((Fin n → S) × (Fin m → S))).filter
      (fun z => (matchedSites z.1 z.2 τ) ∈
        (Finset.univ : Finset S).powersetCard k), pairAddressMass z) =
      ((Fintype.card S).choose k : ℝ)*c := by
  rw [← matched_card_event_mass_decomposition τ]
  calc
    _ = ∑ A ∈ (Finset.univ : Finset S).powersetCard k, c := by
      apply Finset.sum_congr rfl
      intro A hA
      exact hc A hA
    _ = (((Finset.univ : Finset S).powersetCard k).card : ℝ)*c := by
      simp
    _ = ((Fintype.card S).choose k : ℝ)*c := by
      rw [Finset.card_powersetCard, Finset.card_univ]

/-- Complete original `matched_fiber_filter_mass_equal` guarantee for `MatchedEventSymmetry`; all source hypotheses and output obligations are retained. -/
theorem matched_fiber_filter_mass_equal [Nonempty S]
    (σ τ : Equiv.Perm S) {n m : ℕ} (A B : Finset S)
    (hAB : A.image σ=B) :
    (∑ z ∈ (Finset.univ : Finset ((Fin n → S) × (Fin m → S))).filter
      (fun z => matchedSites z.1 z.2 τ=A), pairAddressMass z) =
    (∑ z ∈ (Finset.univ : Finset ((Fin n → S) × (Fin m → S))).filter
      (fun z => matchedSites z.1 z.2 τ=B), pairAddressMass z) := by
  let e := fixedShiftAddressEquiv σ τ n m
  let ei := e.symm
  have hBA : B.image σ.symm=A := by
    rw [← hAB, Finset.image_image]
    simp
  apply Finset.sum_bij' (fun z _ => e z) (fun z _ => ei z)
  · intro z hz
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    have hzA := (Finset.mem_filter.mp hz).2
    have heq := matched_sites_perm_fixed_shift σ τ z.1 z.2
    simpa [e, fixedShiftAddressEquiv, Function.comp_apply, hzA, hAB] using heq
  · intro z hz
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    have hzB := (Finset.mem_filter.mp hz).2
    have heq := matched_sites_perm_fixed_shift σ τ (ei z).1 (ei z).2
    have heq' : (matchedSites (ei z).1 (ei z).2 τ).image σ=B := by
      simpa [e, ei, fixedShiftAddressEquiv, Function.comp_apply, Function.comp_def,
        Equiv.apply_symm_apply, Equiv.symm_apply_apply, hzB] using heq.symm
    have himage : (matchedSites (ei z).1 (ei z).2 τ).image σ = A.image σ :=
      heq'.trans hAB.symm
    exact Finset.image_injective σ.injective himage
  · intro z hz
    simp [e, ei]
  · intro z hz
    simp [e, ei]
  · intro z hz
    exact (pairAddressMass_fixed_shift σ τ z).symm

omit [DecidableEq S] in
/-- Complete original `univ_powersetCard_card` guarantee for `MatchedEventSymmetry`; all source hypotheses and output obligations are retained. -/
theorem univ_powersetCard_card (k : ℕ) :
    ((Finset.univ : Finset S).powersetCard k).card =
      (Fintype.card S).choose k := by
  rw [Finset.card_powersetCard, Finset.card_univ]

omit [DecidableEq S] in
/-- Complete original `univ_powersetCard_nonempty` guarantee for `MatchedEventSymmetry`; all source hypotheses and output obligations are retained. -/
theorem univ_powersetCard_nonempty (k : ℕ) (hk : k ≤ Fintype.card S) :
    (Finset.univ : Finset S).powersetCard k |>.Nonempty := by
  exact Finset.powersetCard_nonempty.mpr (by simpa using hk)

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.occupied_sites_perm_mem_local
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.matched_sites_perm_conjugate
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.uniform_pair_address_perm_invariant
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.uniform_pair_address_independent_perm_invariant
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.exists_perm_map_finset
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.matched_sites_perm_fixed_shift
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.fixedShiftAddressEquiv
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.matched_card_fixed_shift_invariant
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.matched_fiber_mass_equal
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.matched_fiber_mass_card_invariant
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.matched_card_event_mass_decomposition
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.matched_fiber_filter_mass_equal
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.univ_powersetCard_card
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.univ_powersetCard_nonempty
