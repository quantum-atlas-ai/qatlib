/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.MatchedPopulationTail
import Qatlib.Concepts.SpinorSampling.Matching.MatchedMeasurementNoise

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Matched Record Conditional Tail

Matched Record Conditional Tail constructions and identities for Spinor Sampling.
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

/-- Complete original `matched_card_event_mass_pos` guarantee for `MatchedRecordConditionalTail`; all source hypotheses and output obligations are retained. -/
theorem matched_card_event_mass_pos [Nonempty S]
    (τ : Equiv.Perm S) {n m k : ℕ} (hk0 : 0 < k)
    (hkn : k ≤ n) (hkm : k ≤ m) (hkS : k ≤ Fintype.card S) :
    0 < matchedCardEventMass τ n m k := by
  obtain ⟨A,hA⟩ := univ_powersetCard_nonempty (S:=S) k hkS
  have hcard := (Finset.mem_powersetCard.mp hA).2
  obtain ⟨J,K,hmatch⟩ := padded_matched_fiber_nonempty τ A hcard hk0 hkn hkm
  unfold matchedCardEventMass
  apply Finset.sum_pos'
  · intro z _
    exact (pairAddressMass_pos z).le
  · refine ⟨(J,K), ?_, pairAddressMass_pos (J,K)⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hmatch,hcard]

/-- Complete original `finite_bad_mass_split_center` guarantee for `MatchedRecordConditionalTail`; all source hypotheses and output obligations are retained. -/
theorem finite_bad_mass_split_center {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (F : X → ℝ) (μ c ε : ℝ) :
    finiteBadMass p F μ ε ≤ finiteBadMass p F c (ε/2) +
      (if ε/2 < |c-μ| then 1 else 0) := by
  classical
  calc
    _ = p.expect (fun x => if ε < |F x-μ| then 1 else 0) :=
      (finite_bad_indicator_mean p F μ ε).symm
    _ ≤ p.expect (fun x => (if ε/2 < |F x-c| then 1 else 0) +
        (if ε/2 < |c-μ| then 1 else 0)) := by
      apply finite_expect_mono
      intro x
      by_cases hp : ε/2 < |c-μ|
      · simp only [ite_eq_left hp]
        split_ifs <;> norm_num
      · by_cases hn : ε/2 < |F x-c|
        · simp only [ite_eq_right hp, ite_eq_left hn]
          split_ifs <;> norm_num
        · have hsmall : ¬ ε < |F x-μ| := by
            have ht : |F x-μ| ≤ |F x-c| + |c-μ| := by
              calc
                _ = |(F x-c)+(c-μ)| := by congr 1; ring
                _ ≤ _ := abs_add_le _ _
            have h1 := le_of_not_gt hp
            have h2 := le_of_not_gt hn
            linarith
          simp only [ite_eq_right hp, ite_eq_right hn, ite_eq_right hsmall, zero_add, le_refl]
    _ = _ := by
      rw [finite_expect_add, finite_bad_indicator_mean, finite_expect_const]

/-- Construction for matched Record Conditional Bad Mass in the matched record conditional tail model. -/
def matchedRecordConditionalBadMass [Nonempty S]
    (τ : Equiv.Perm S) {n m k : ℕ} (a b : S → ℝ)
    (ha : ∀ x, |a x| ≤ 1) (hb : ∀ x, |b x| ≤ 1) (μ ε : ℝ) : ℝ :=
  (∑ z ∈ (Finset.univ : Finset ((Fin n → S) × (Fin m → S))).filter
    (fun z => (matchedSites z.1 z.2 τ).card=k), pairAddressMass z *
      finiteBadMass (productLaw (conditionalSigns a ha z.1) (conditionalSigns b hb z.2))
        (conditionalMatched z.1 z.2 τ) μ ε) / matchedCardEventMass τ n m k

/-- Complete original `matched_record_conditional_tail` guarantee for `MatchedRecordConditionalTail`; all source hypotheses and output obligations are retained. -/
theorem matched_record_conditional_tail [Nonempty S]
    (τ : Equiv.Perm S) {n m k : ℕ} (hk0 : 0 < k)
    (hkn : k ≤ n) (hkm : k ≤ m) (hkS : k ≤ Fintype.card S)
    (a b : S → ℝ) (ha : ∀ x, |a x| ≤ 1) (hb : ∀ x, |b x| ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    matchedRecordConditionalBadMass τ (n:=n) (m:=m) (k:=k) a b ha hb
      (setAverage Finset.univ (fun x => a x*b (τ x))) ε ≤
        4 * Real.exp (-(k : ℝ)*ε^2/8) := by
  classical
  let f : S → ℝ := fun x => a x*b (τ x)
  let μ := setAverage Finset.univ f
  let C : ℝ := 2 * Real.exp (-(k : ℝ)*(ε/2)^2/2)
  let E := (Finset.univ : Finset ((Fin n → S) × (Fin m → S))).filter
    (fun z => (matchedSites z.1 z.2 τ).card=k)
  let pop : ((Fin n → S) × (Fin m → S)) → ℝ := fun z =>
    if ε/2 < |setAverage (matchedSites z.1 z.2 τ) f-μ| then 1 else 0
  have hden := matched_card_event_mass_pos τ hk0 hkn hkm hkS
  have hf (x : S) : |f x| ≤ 1 := by
    dsimp [f]
    rw [abs_mul]
    exact (mul_le_mul (ha x) (hb (τ x)) (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  have hrow (z : (Fin n → S) × (Fin m → S)) (hz : z ∈ E) :
      finiteBadMass (productLaw (conditionalSigns a ha z.1) (conditionalSigns b hb z.2))
        (conditionalMatched z.1 z.2 τ) μ ε ≤ C+pop z := by
    have hcard := (Finset.mem_filter.mp hz).2
    have hi : 0 < (matchedSites z.1 z.2 τ).card := by omega
    have hnoise := conditional_matched_noise_tail z.1 z.2 τ τ.injective hi a b ha hb
      (ε/2) (by linarith)
    have hsplit := finite_bad_mass_split_center
      (productLaw (conditionalSigns a ha z.1) (conditionalSigns b hb z.2))
      (conditionalMatched z.1 z.2 τ) μ (setAverage (matchedSites z.1 z.2 τ) f) ε
    rw [hcard] at hnoise
    exact hsplit.trans (add_le_add hnoise (le_refl (pop z)))
  have hpop : (∑ z ∈ E, pairAddressMass z * pop z) / matchedCardEventMass τ n m k ≤ C := by
    exact matched_address_pair_conditional_population_tail τ hk0 hkn hkm hkS f hf
      (ε/2) (by linarith)
  have hsum : (∑ z ∈ E, pairAddressMass z) = matchedCardEventMass τ n m k := rfl
  unfold matchedRecordConditionalBadMass
  change (∑ z ∈ E, pairAddressMass z * finiteBadMass
    (productLaw (conditionalSigns a ha z.1) (conditionalSigns b hb z.2))
    (conditionalMatched z.1 z.2 τ) μ ε) / matchedCardEventMass τ n m k ≤ _
  calc
    _ ≤ (∑ z ∈ E, pairAddressMass z * (C+pop z)) / matchedCardEventMass τ n m k := by
      apply div_le_div_of_nonneg_right _ hden.le
      exact Finset.sum_le_sum fun z hz =>
        mul_le_mul_of_nonneg_left (hrow z hz) (pairAddressMass_pos z).le
    _ = C + (∑ z ∈ E, pairAddressMass z * pop z) / matchedCardEventMass τ n m k := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum, add_div,
        mul_div_cancel_left₀ C (ne_of_gt hden)]
    _ ≤ C+C := add_le_add (le_refl C) hpop
    _ = _ := by
      dsimp [C]
      have he : -(k : ℝ)*(ε/2)^2/2 = -(k : ℝ)*ε^2/8 := by ring
      rw [he]
      ring

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.matched_card_event_mass_pos
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.finite_bad_mass_split_center
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.matched_record_conditional_tail
