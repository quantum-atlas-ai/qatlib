/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.MatchedRecordConditionalTail
import Qatlib.Concepts.SpinorSampling.Matching.CohortRecordPairs

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Matched Signed Conditional Tail

Matched Signed Conditional Tail constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched
noncomputable section
open scoped BigOperators
open Qatlib

variable {S : Type} [Fintype S] [Nonempty S] [DecidableEq S]

/-- Complete original `signed_pair_matched_card_expectation` guarantee for `MatchedSignedConditionalTail`; all source hypotheses and output obligations are retained. -/
theorem signed_pair_matched_card_expectation
    (τ : Equiv.Perm S) {n m k : ℕ} (a b : S → ℝ)
    (ha : ∀ x, |a x| ≤ 1) (hb : ∀ x, |b x| ≤ 1)
    (G : ((Fin n → S × Bool) × (Fin m → S × Bool)) → ℝ) :
    (productLaw (cohortLaw (signedRecordLaw a ha) n)
      (cohortLaw (signedRecordLaw b hb) m)).expect
      (fun z => if (matchedSites (fun i => (z.1 i).1) (fun i => (z.2 i).1) τ).card=k
        then G z else 0) =
    ∑ z ∈ (Finset.univ : Finset ((Fin n → S) × (Fin m → S))).filter
      (fun z => (matchedSites z.1 z.2 τ).card=k), pairAddressMass z *
      (productLaw (conditionalSigns a ha z.1) (conditionalSigns b hb z.2)).expect
        (fun q => G (fun i => (z.1 i,q.1 i),fun i => (z.2 i,q.2 i))) := by
  classical
  rw [signed_pair_disintegration a b ha hb]
  calc
    _ = (productLaw (cohortLaw (uniformLaw S) n) (cohortLaw (uniformLaw S) m)).expect
        (fun z => if (matchedSites z.1 z.2 τ).card=k then
          (productLaw (conditionalSigns a ha z.1) (conditionalSigns b hb z.2)).expect
            (fun q => G (fun i => (z.1 i,q.1 i),fun i => (z.2 i,q.2 i))) else 0) := by
      rw [product_law_expect]
      congr 1
      funext J
      congr 1
      funext K
      by_cases h : (matchedSites J K τ).card=k
      · simp only [h, ite_true]
      · simp only [h, ite_false, finite_expect_const]
    _ = _ := by
      unfold FinDist.expect
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro z _
      by_cases h : (matchedSites z.1 z.2 τ).card=k
      · simp only [h, ite_true]
        rfl
      · simp only [h, ite_false, mul_zero]

/-- Complete original `signed_pair_matched_card_mass` guarantee for `MatchedSignedConditionalTail`; all source hypotheses and output obligations are retained. -/
theorem signed_pair_matched_card_mass
    (τ : Equiv.Perm S) {n m k : ℕ} (a b : S → ℝ)
    (ha : ∀ x, |a x| ≤ 1) (hb : ∀ x, |b x| ≤ 1) :
    (productLaw (cohortLaw (signedRecordLaw a ha) n)
      (cohortLaw (signedRecordLaw b hb) m)).expect
      (fun z => if (matchedSites (fun i => (z.1 i).1) (fun i => (z.2 i).1) τ).card=k
        then 1 else 0) = matchedCardEventMass τ n m k := by
  rw [signed_pair_matched_card_expectation τ a b ha hb (fun _ => 1)]
  simp only [finite_expect_const, mul_one, matchedCardEventMass]

/-- Construction for signed Matched Conditional Bad Mass in the matched signed conditional tail model. -/
def signedMatchedConditionalBadMass
    (τ : Equiv.Perm S) {n m k : ℕ} (a b : S → ℝ)
    (ha : ∀ x, |a x| ≤ 1) (hb : ∀ x, |b x| ≤ 1) (μ ε : ℝ) : ℝ :=
  let p := productLaw (cohortLaw (signedRecordLaw a ha) n)
    (cohortLaw (signedRecordLaw b hb) m)
  p.expect (fun z =>
    if (matchedSites (fun i => (z.1 i).1) (fun i => (z.2 i).1) τ).card=k then
      (if ε < |(matchedStatisticQ z.1 z.2 τ : ℝ)-μ| then 1 else 0) else 0) /
  p.expect (fun z =>
    if (matchedSites (fun i => (z.1 i).1) (fun i => (z.2 i).1) τ).card=k then 1 else 0)

/-- Complete original `signed_matched_conditional_bad_mass_eq` guarantee for `MatchedSignedConditionalTail`; all source hypotheses and output obligations are retained. -/
theorem signed_matched_conditional_bad_mass_eq
    (τ : Equiv.Perm S) {n m k : ℕ} (a b : S → ℝ)
    (ha : ∀ x, |a x| ≤ 1) (hb : ∀ x, |b x| ≤ 1) (μ ε : ℝ) :
    signedMatchedConditionalBadMass τ (n:=n) (m:=m) (k:=k) a b ha hb μ ε =
      matchedRecordConditionalBadMass τ (n:=n) (m:=m) (k:=k) a b ha hb μ ε := by
  classical
  unfold signedMatchedConditionalBadMass
  dsimp only
  rw [signed_pair_matched_card_mass τ a b ha hb,
    signed_pair_matched_card_expectation τ a b ha hb]
  unfold matchedRecordConditionalBadMass
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  have hcast : (fun q : (Fin n → Bool) × (Fin m → Bool) =>
      if ε < |(matchedStatisticQ (fun i => (z.1 i,q.1 i))
        (fun i => (z.2 i,q.2 i)) τ : ℝ)-μ| then (1 : ℝ) else 0) =
      (fun q => if ε < |conditionalMatched z.1 z.2 τ q-μ| then 1 else 0) := by
    funext q
    rw [matched_statistic_cast]
    rfl
  rw [hcast, finite_bad_indicator_mean]

/-- Complete original `signed_matched_conditional_tail` guarantee for `MatchedSignedConditionalTail`; all source hypotheses and output obligations are retained. -/
theorem signed_matched_conditional_tail
    (τ : Equiv.Perm S) {n m k : ℕ} (hk0 : 0 < k)
    (hkn : k ≤ n) (hkm : k ≤ m) (hkS : k ≤ Fintype.card S)
    (a b : S → ℝ) (ha : ∀ x, |a x| ≤ 1) (hb : ∀ x, |b x| ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    signedMatchedConditionalBadMass τ (n:=n) (m:=m) (k:=k) a b ha hb
      (setAverage Finset.univ (fun x => a x*b (τ x))) ε ≤
        4 * Real.exp (-(k : ℝ)*ε^2/8) := by
  rw [signed_matched_conditional_bad_mass_eq]
  exact matched_record_conditional_tail τ hk0 hkn hkm hkS a b ha hb ε hε

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.signed_pair_matched_card_expectation
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.signed_pair_matched_card_mass
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.signed_matched_conditional_bad_mass_eq
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.signed_matched_conditional_tail
