/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.WithoutReplacementSetLaw
import Qatlib.Concepts.SpinorSampling.Matching.OrderedSetAverageBridge
import Qatlib.Concepts.SpinorSampling.Matching.MatchedConditionalLaw

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Matched Population Tail

Matched Population Tail constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched
noncomputable section
open scoped BigOperators
open Qatlib

variable {S : Type} [Fintype S] [DecidableEq S]

/-- Complete original `matched_conditional_set_expectation_pair` guarantee for `MatchedPopulationTail`; all source hypotheses and output obligations are retained. -/
theorem matched_conditional_set_expectation_pair [Nonempty S]
    (τ : Equiv.Perm S) {n m k : ℕ} (F : Finset S → ℝ) :
    matchedConditionalSetExpectation τ (n:=n) (m:=m) (k:=k) F =
    (∑ z ∈ (Finset.univ : Finset ((Fin n → S) × (Fin m → S))).filter
      (fun z => (matchedSites z.1 z.2 τ).card = k),
      pairAddressMass z * F (matchedSites z.1 z.2 τ)) / matchedCardEventMass τ n m k := by
  classical
  have hrow (A : Finset S) :
      (∑ z ∈ (Finset.univ : Finset ((Fin n → S) × (Fin m → S))).filter
        (fun z => matchedSites z.1 z.2 τ = A),
        pairAddressMass z * F (matchedSites z.1 z.2 τ)) =
      (∑ z ∈ (Finset.univ : Finset ((Fin n → S) × (Fin m → S))).filter
        (fun z => matchedSites z.1 z.2 τ = A), pairAddressMass z) * F A := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro z hz
    rw [(Finset.mem_filter.mp hz).2]
  calc
    _ = (∑ A ∈ (Finset.univ : Finset S).powersetCard k,
        ∑ z ∈ (Finset.univ : Finset ((Fin n → S) × (Fin m → S))).filter
          (fun z => matchedSites z.1 z.2 τ = A),
          pairAddressMass z * F (matchedSites z.1 z.2 τ)) / matchedCardEventMass τ n m k := by
      unfold matchedConditionalSetExpectation matchedSetConditionalMass
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro A _
      rw [hrow]
      ring
    _ = (∑ z ∈ (Finset.univ : Finset ((Fin n → S) × (Fin m → S))).filter
        (fun z => matchedSites z.1 z.2 τ ∈ (Finset.univ : Finset S).powersetCard k),
        pairAddressMass z * F (matchedSites z.1 z.2 τ)) / matchedCardEventMass τ n m k := by
      rw [Finset.sum_fiberwise_eq_sum_filter]
    _ = _ := by
      congr 2
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
        Finset.subset_univ, true_and]

/-- Complete original `without_replacement_set_average_expectation` guarantee for `MatchedPopulationTail`; all source hypotheses and output obligations are retained. -/
theorem without_replacement_set_average_expectation
    (R : Finset S) {k : ℕ} (hk : k ≤ R.card) (f : S → ℝ) (G : ℝ → ℝ) :
    (1 / (R.card.choose k : ℝ)) *
      (∑ A ∈ R.powersetCard k, G (setAverage A f)) =
    (withoutReplacementLaw R k hk).expect (fun ω => G (FinDist.avg f ω)) := by
  rw [← without_replacement_set_expectation R (fun A => G (setAverage A f))]
  change (∑ ω : Fin k → S,
    withoutReplacementMass R k ω * G (setAverage (occupiedSites ω) f)) =
    ∑ ω : Fin k → S, withoutReplacementMass R k ω * G (FinDist.avg f ω)
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hzero : withoutReplacementMass R k ω = 0
  · simp [hzero]
  · have hpos : 0 < withoutReplacementMass R k ω :=
      lt_of_le_of_ne (without_replacement_mass_nonneg R k ω) (Ne.symm hzero)
    rw [occupied_set_average_eq_ordered_average ω
      (without_replacement_mass_pos_injective R k ω hpos)]

/-- Complete original `matched_conditional_population_expectation` guarantee for `MatchedPopulationTail`; all source hypotheses and output obligations are retained. -/
theorem matched_conditional_population_expectation [Nonempty S]
    (τ : Equiv.Perm S) {n m k : ℕ} (hk0 : 0 < k) (hkn : k ≤ n) (hkm : k ≤ m)
    (hkS : k ≤ Fintype.card S) (f : S → ℝ) (G : ℝ → ℝ) :
    matchedConditionalSetExpectation τ (n:=n) (m:=m) (k:=k)
      (fun A => G (setAverage A f)) =
    (withoutReplacementLaw (Finset.univ : Finset S) k
      (by simpa using hkS)).expect (fun ω => G (FinDist.avg f ω)) := by
  rw [matchedConditionalSetExpectation_uniform τ _ hk0 hkn hkm]
  have he := without_replacement_set_average_expectation
    (Finset.univ : Finset S) (by simpa using hkS) f G
  simpa only [Finset.card_univ] using he

/-- Complete original `matched_conditional_population_tail` guarantee for `MatchedPopulationTail`; all source hypotheses and output obligations are retained. -/
theorem matched_conditional_population_tail [Nonempty S]
    (τ : Equiv.Perm S) {n m k : ℕ} (hk0 : 0 < k) (hkn : k ≤ n) (hkm : k ≤ m)
    (hkS : k ≤ Fintype.card S) (f : S → ℝ) (hf : ∀ x, |f x| ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    matchedConditionalSetExpectation τ (n:=n) (m:=m) (k:=k)
      (fun A => if ε < |setAverage A f - setAverage Finset.univ f| then 1 else 0) ≤
        2 * Real.exp (-(k : ℝ)*ε^2/2) := by
  classical
  rw [matched_conditional_population_expectation τ hk0 hkn hkm hkS f
    (fun v => if ε < |v - setAverage Finset.univ f| then 1 else 0)]
  rw [finite_bad_indicator_mean]
  exact without_replacement_average_tail Finset.univ k (by simpa using hkS)
    hk0 f (fun x _ => hf x) ε hε

/-- Complete original `matched_address_pair_conditional_population_tail` guarantee for `MatchedPopulationTail`; all source hypotheses and output obligations are retained. -/
theorem matched_address_pair_conditional_population_tail [Nonempty S]
    (τ : Equiv.Perm S) {n m k : ℕ} (hk0 : 0 < k) (hkn : k ≤ n) (hkm : k ≤ m)
    (hkS : k ≤ Fintype.card S) (f : S → ℝ) (hf : ∀ x, |f x| ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    (∑ z ∈ (Finset.univ : Finset ((Fin n → S) × (Fin m → S))).filter
      (fun z => (matchedSites z.1 z.2 τ).card = k), pairAddressMass z *
        (if ε < |setAverage (matchedSites z.1 z.2 τ) f - setAverage Finset.univ f|
          then 1 else 0)) / matchedCardEventMass τ n m k ≤
      2 * Real.exp (-(k : ℝ)*ε^2/2) := by
  classical
  rw [← matched_conditional_set_expectation_pair τ
    (fun A => if ε < |setAverage A f - setAverage Finset.univ f| then 1 else 0)]
  exact matched_conditional_population_tail τ hk0 hkn hkm hkS f hf ε hε

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.without_replacement_set_average_expectation
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.matched_conditional_population_expectation
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.matched_conditional_population_tail

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.matched_conditional_set_expectation_pair
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.matched_address_pair_conditional_population_tail
