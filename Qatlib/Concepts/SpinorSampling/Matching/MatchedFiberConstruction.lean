/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.MatchedRecords

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Matched Fiber Construction

Matched Fiber Construction constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched
noncomputable section

variable {S : Type} [Fintype S] [DecidableEq S]

omit [Fintype S] in
/-- Complete original `occupied_sites_finset_equiv` guarantee for `MatchedFiberConstruction`; all source hypotheses and output obligations are retained. -/
theorem occupied_sites_finset_equiv (A : Finset S) {k : ℕ}
    (hcard : A.card=k) :
    ∃ J : Fin k → S, occupiedSites J=A := by
  let e : Fin k ≃ A := (Equiv.cast (congrArg Fin hcard.symm)).trans A.equivFin.symm
  refine ⟨fun i => (e i : S), ?_⟩
  ext x
  simp only [occupiedSites, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i,rfl⟩
    exact (e i).property
  · intro hx
    obtain ⟨i,hi⟩ := e.surjective ⟨x,hx⟩
    exact ⟨i, congrArg Subtype.val hi⟩

omit [Fintype S] in
/-- Complete original `saturated_matched_fiber_nonempty` guarantee for `MatchedFiberConstruction`; all source hypotheses and output obligations are retained. -/
theorem saturated_matched_fiber_nonempty [Nonempty S]
    (τ : Equiv.Perm S) (A : Finset S) {k : ℕ}
    (hcard : A.card=k) :
    ∃ J K : Fin k → S, matchedSites J K τ=A := by
  obtain ⟨J,hJ⟩ := occupied_sites_finset_equiv A hcard
  refine ⟨J,τ ∘ J,?_⟩
  ext x
  rw [mem_matched_sites]
  constructor
  · rintro ⟨hx,hτx⟩
    simpa [hJ] using hx
  · intro hx
    refine ⟨?_,?_⟩
    · simpa [hJ] using hx
    · have hxJ : x ∈ occupiedSites J := by simpa [hJ] using hx
      obtain ⟨i,hi⟩ := Finset.mem_image.mp hxJ
      simp only [occupiedSites, Finset.mem_image, Finset.mem_univ, true_and,
        Function.comp_apply]
      exact ⟨i, by simp [hi]⟩

/-- Construction for pad Address in the matched fiber construction model. -/
def padAddress {k n : ℕ} (J : Fin k → S) (_hk : k ≤ n) (hk0 : 0 < k) : Fin n → S :=
  fun i => if hi : i.val < k then J ⟨i.val,hi⟩ else J ⟨0,Nat.zero_lt_of_lt hk0⟩

omit [Fintype S] in
/-- Complete original `occupied_sites_padAddress` guarantee for `MatchedFiberConstruction`; all source hypotheses and output obligations are retained. -/
theorem occupied_sites_padAddress {k n : ℕ} (J : Fin k → S)
    (hk : k ≤ n) (hk0 : 0 < k) :
    occupiedSites (padAddress J hk hk0)=occupiedSites J := by
  ext x
  simp only [occupiedSites, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i,rfl⟩
    by_cases hi : i.val < k
    · exact ⟨⟨i.val,hi⟩,by simp [padAddress,hi]⟩
    · exact ⟨⟨0,Nat.zero_lt_of_lt hk0⟩,by simp [padAddress,hi]⟩
  · rintro ⟨j,rfl⟩
    refine ⟨Fin.castLE hk j,by simp [padAddress,j.isLt]⟩

omit [Fintype S] in
/-- Complete original `padded_matched_fiber_nonempty` guarantee for `MatchedFiberConstruction`; all source hypotheses and output obligations are retained. -/
theorem padded_matched_fiber_nonempty [Nonempty S]
    (τ : Equiv.Perm S) (A : Finset S) {k n m : ℕ}
    (hcard : A.card=k) (hk0 : 0 < k) (hkn : k ≤ n) (hkm : k ≤ m) :
    ∃ J : Fin n → S, ∃ K : Fin m → S, matchedSites J K τ=A := by
  obtain ⟨J0,K0,h0⟩ := saturated_matched_fiber_nonempty τ A hcard
  refine ⟨padAddress J0 hkn hk0,padAddress K0 hkm hk0,?_⟩
  ext x
  rw [mem_matched_sites]
  have h0x : x ∈ occupiedSites J0 ∧ τ x ∈ occupiedSites K0 ↔ x ∈ A := by
    rw [← mem_matched_sites J0 K0 τ x, h0]
  simp only [occupied_sites_padAddress] at *
  exact h0x

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.occupied_sites_finset_equiv
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.saturated_matched_fiber_nonempty
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.occupied_sites_padAddress
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.padded_matched_fiber_nonempty
