/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.MatchedMassPositivity

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Matched Conditional Law

Matched Conditional Law constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched
noncomputable section
open scoped BigOperators

variable {S : Type} [Fintype S] [DecidableEq S]

/-- Construction for matched Card Event Mass in the matched conditional law model. -/
def matchedCardEventMass [Nonempty S]
    (τ : Equiv.Perm S) (n m k : ℕ) : ℝ :=
  ∑ z ∈ (Finset.univ : Finset ((Fin n → S) × (Fin m → S))).filter
    (fun z => (matchedSites z.1 z.2 τ).card=k), pairAddressMass z

/-- Construction for matched Set Conditional Mass in the matched conditional law model. -/
def matchedSetConditionalMass [Nonempty S]
    (τ : Equiv.Perm S) {n m k : ℕ} (A : Finset S) : ℝ :=
  (∑ z ∈ (Finset.univ : Finset ((Fin n → S) × (Fin m → S))).filter
    (fun z => matchedSites z.1 z.2 τ=A), pairAddressMass z) /
    matchedCardEventMass τ n m k

/-- Complete original `conditional_matched_set_uniform` guarantee for `MatchedConditionalLaw`; all source hypotheses and output obligations are retained. -/
theorem conditional_matched_set_uniform [Nonempty S]
    (τ : Equiv.Perm S) {n m k : ℕ} (A : Finset S)
    (hA : A.card=k) (hk0 : 0<k) (hkn : k≤n) (hkm : k≤m) :
    matchedSetConditionalMass τ (n:=n) (m:=m) (k:=k) A =
      1/(Fintype.card S).choose k := by
  let c := ∑ z ∈ (Finset.univ : Finset ((Fin n → S) × (Fin m → S))).filter
    (fun z => matchedSites z.1 z.2 τ=A), pairAddressMass z
  have hcpos : 0<c := by
    dsimp [c]
    exact matched_fiber_filter_mass_pos τ A hA hk0 hkn hkm
  have hc : ∀ B ∈ (Finset.univ : Finset S).powersetCard k,
      (∑ z ∈ (Finset.univ : Finset ((Fin n → S) × (Fin m → S))).filter
        (fun z => matchedSites z.1 z.2 τ=B), pairAddressMass z)=c := by
    intro B hB
    obtain ⟨hsub,hBk⟩ := Finset.mem_powersetCard.mp hB
    have hperm : ∃ σ : Equiv.Perm S, A.image σ=B :=
      exists_perm_map_finset A B (hA.trans hBk.symm)
    obtain ⟨σ,hσ⟩ := hperm
    exact (matched_fiber_filter_mass_equal σ τ A B hσ).symm.trans (by rfl)
  have hevent : matchedCardEventMass τ n m k=
      ((Fintype.card S).choose k : ℝ)*c := by
    have hfilters :
        (Finset.univ : Finset ((Fin n → S) × (Fin m → S))).filter
          (fun z => (matchedSites z.1 z.2 τ).card=k) =
        (Finset.univ : Finset ((Fin n → S) × (Fin m → S))).filter
          (fun z => (matchedSites z.1 z.2 τ) ∈
            (Finset.univ : Finset S).powersetCard k) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_powersetCard]
      constructor
      · intro h
        exact ⟨Finset.subset_univ _,h⟩
      · exact And.right
    unfold matchedCardEventMass
    rw [hfilters]
    apply matched_card_event_mass_const τ c hc
  have hchoose : 0 < (Fintype.card S).choose k := by
    apply Nat.choose_pos
    exact hA ▸ A.card_le_univ
  unfold matchedSetConditionalMass
  rw [hevent]
  have hAmem : A ∈ (Finset.univ : Finset S).powersetCard k :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hA⟩
  rw [hc A hAmem]
  field_simp [ne_of_gt hcpos]

/-- Construction for matched Conditional Set Expectation in the matched conditional law model. -/
def matchedConditionalSetExpectation [Nonempty S]
    (τ : Equiv.Perm S) {n m k : ℕ} (F : Finset S → ℝ) : ℝ :=
  ∑ A ∈ (Finset.univ : Finset S).powersetCard k,
    matchedSetConditionalMass τ (n:=n) (m:=m) (k:=k) A * F A

/-- Complete original `matchedConditionalSetExpectation_uniform` guarantee for `MatchedConditionalLaw`; all source hypotheses and output obligations are retained. -/
theorem matchedConditionalSetExpectation_uniform [Nonempty S]
    (τ : Equiv.Perm S) {n m k : ℕ} (F : Finset S → ℝ)
    (hk0 : 0<k) (hkn : k≤n) (hkm : k≤m) :
    matchedConditionalSetExpectation τ (n:=n) (m:=m) (k:=k) F =
      (1/(Fintype.card S).choose k : ℝ) *
        (∑ A ∈ (Finset.univ : Finset S).powersetCard k, F A) := by
  unfold matchedConditionalSetExpectation
  calc
    _ = ∑ A ∈ (Finset.univ : Finset S).powersetCard k,
        (1/(Fintype.card S).choose k : ℝ) * F A := by
      apply Finset.sum_congr rfl
      intro A hA
      have hcard := (Finset.mem_powersetCard.mp hA).2
      rw [conditional_matched_set_uniform τ A hcard hk0 hkn hkm]
    _ = _ := by rw [Finset.mul_sum]

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.matchedConditionalSetExpectation_uniform

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.conditional_matched_set_uniform
