/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.MatchedRecords
import Qatlib.Concepts.SpinorSampling.Matching.MatchedSamplingLaw
import Qatlib.Concepts.SpinorSampling.Matching.SelectedSignProducts

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Matched Measurement Noise

Matched Measurement Noise constructions and identities for Spinor Sampling.
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

/-- Construction for left Match Index in the matched measurement noise model. -/
def leftMatchIndex {n m : ℕ} (J : Fin n → S) (K : Fin m → S) (τ : S → S)
    (x : matchedSites J K τ) : Fin n :=
  chosenFirstIndex J x ((mem_matched_sites J K τ x).mp x.property).1

/-- Construction for right Match Index in the matched measurement noise model. -/
def rightMatchIndex {n m : ℕ} (J : Fin n → S) (K : Fin m → S) (τ : S → S)
    (x : matchedSites J K τ) : Fin m :=
  chosenFirstIndex K (τ x) ((mem_matched_sites J K τ x).mp x.property).2

/-- Complete original `left_match_address` guarantee for `MatchedMeasurementNoise`; all source hypotheses and output obligations are retained. -/
theorem left_match_address {n m : ℕ} (J : Fin n → S) (K : Fin m → S) (τ : S → S)
    (x : matchedSites J K τ) : J (leftMatchIndex J K τ x)=x :=
  (chosen_first_index_spec J x ((mem_matched_sites J K τ x).mp x.property).1).2

/-- Complete original `right_match_address` guarantee for `MatchedMeasurementNoise`; all source hypotheses and output obligations are retained. -/
theorem right_match_address {n m : ℕ} (J : Fin n → S) (K : Fin m → S) (τ : S → S)
    (x : matchedSites J K τ) : K (rightMatchIndex J K τ x)=τ x :=
  (chosen_first_index_spec K (τ x) ((mem_matched_sites J K τ x).mp x.property).2).2

/-- Complete original `left_match_index_injective` guarantee for `MatchedMeasurementNoise`; all source hypotheses and output obligations are retained. -/
theorem left_match_index_injective {n m : ℕ} (J : Fin n → S) (K : Fin m → S) (τ : S → S) :
    Function.Injective (leftMatchIndex J K τ) := by
  intro x y h
  apply Subtype.ext
  calc
    (x : S) = J (leftMatchIndex J K τ x) := (left_match_address J K τ x).symm
    _ = J (leftMatchIndex J K τ y) := congrArg J h
    _ = (y : S) := left_match_address J K τ y

/-- Complete original `right_match_index_injective` guarantee for `MatchedMeasurementNoise`; all source hypotheses and output obligations are retained. -/
theorem right_match_index_injective {n m : ℕ} (J : Fin n → S) (K : Fin m → S) (τ : S → S)
    (hτ : Function.Injective τ) : Function.Injective (rightMatchIndex J K τ) := by
  intro x y h
  apply Subtype.ext
  apply hτ
  calc
    τ x = K (rightMatchIndex J K τ x) := (right_match_address J K τ x).symm
    _ = K (rightMatchIndex J K τ y) := congrArg K h
    _ = τ y := right_match_address J K τ y

/-- Complete original `left_first_sign` guarantee for `MatchedMeasurementNoise`; all source hypotheses and output obligations are retained. -/
theorem left_first_sign {n m : ℕ} (J : Fin n → S) (K : Fin m → S) (τ : S → S)
    (Q : Fin n → Bool) (x : matchedSites J K τ) :
    (firstSignZ (fun i => (J i,Q i)) x : ℝ)=recordSign (Q (leftMatchIndex J K τ x)) := by
  exact first_sign_real_eq (fun i => (J i,Q i)) x _
    (chosen_first_index_spec J x ((mem_matched_sites J K τ x).mp x.property).1).1

/-- Complete original `right_first_sign` guarantee for `MatchedMeasurementNoise`; all source hypotheses and output obligations are retained. -/
theorem right_first_sign {n m : ℕ} (J : Fin n → S) (K : Fin m → S) (τ : S → S)
    (Q : Fin m → Bool) (x : matchedSites J K τ) :
    (firstSignZ (fun i => (K i,Q i)) (τ x) : ℝ)=recordSign (Q (rightMatchIndex J K τ x)) := by
  exact first_sign_real_eq (fun i => (K i,Q i)) (τ x) _
    (chosen_first_index_spec K (τ x) ((mem_matched_sites J K τ x).mp x.property).2).1

/-- Construction for conditional Matched in the matched measurement noise model. -/
def conditionalMatched {n m : ℕ} (J : Fin n → S) (K : Fin m → S) (τ : S → S)
    (z : (Fin n → Bool) × (Fin m → Bool)) : ℝ :=
  matchedStatistic (fun i => (J i,z.1 i)) (fun i => (K i,z.2 i)) τ

/-- Complete original `conditional_matched_rescale` guarantee for `MatchedMeasurementNoise`; all source hypotheses and output obligations are retained. -/
theorem conditional_matched_rescale {n m : ℕ} (J : Fin n → S) (K : Fin m → S)
    (τ : S → S) (hI : 0 < (matchedSites J K τ).card) (a b : S → ℝ)
    (z : (Fin n → Bool) × (Fin m → Bool)) :
    ((matchedSites J K τ).card : ℝ)*(conditionalMatched J K τ z-
      setAverage (matchedSites J K τ) (fun x => a x*b (τ x)))=
      ∑ x : matchedSites J K τ,
        (recordSign (z.1 (leftMatchIndex J K τ x))*recordSign (z.2 (rightMatchIndex J K τ x))-a x*b (τ x)) := by
  let I := matchedSites J K τ
  have hI0 : I.card ≠ 0 := hI.ne'
  have hIr : (I.card : ℝ) ≠ 0 := by exact_mod_cast hI0
  have hs : conditionalMatched J K τ z=
      (∑ x : I, recordSign (z.1 (leftMatchIndex J K τ x))*recordSign (z.2 (rightMatchIndex J K τ x)))/(I.card : ℝ) := by
    dsimp only [conditionalMatched,matchedStatistic]
    rw [ite_eq_right hI0]
    congr 1
    calc
      _ = ∑ x : I, (firstSignZ (fun i => (J i,z.1 i)) x : ℝ)*
          (firstSignZ (fun i => (K i,z.2 i)) (τ x) : ℝ) := (Finset.sum_coe_sort I _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x _
        rw [left_first_sign J K τ z.1 x,right_first_sign J K τ z.2 x]
  have hm : setAverage I (fun x => a x*b (τ x))=(∑ x : I, a x*b (τ x))/(I.card : ℝ) := by
    unfold setAverage
    exact congrArg (fun v : ℝ => v/(I.card : ℝ)) (Finset.sum_coe_sort I (fun x => a x*b (τ x))).symm
  change (I.card : ℝ)*(conditionalMatched J K τ z-setAverage I (fun x => a x*b (τ x)))=_
  rw [hs,hm]
  calc
    _ = (((∑ x : I, recordSign (z.1 (leftMatchIndex J K τ x))*recordSign (z.2 (rightMatchIndex J K τ x)))-
          (∑ x : I, a x*b (τ x)))/(I.card : ℝ))*(I.card : ℝ) := by ring
    _ = _ := by rw [div_mul_cancel₀ _ hIr,Finset.sum_sub_distrib]

/-- Complete original `conditional_matched_mgf` guarantee for `MatchedMeasurementNoise`; all source hypotheses and output obligations are retained. -/
theorem conditional_matched_mgf {n m : ℕ} (J : Fin n → S) (K : Fin m → S)
    (τ : S → S) (hτ : Function.Injective τ) (hI : 0 < (matchedSites J K τ).card)
    (a b : S → ℝ) (ha : ∀ x, |a x| ≤ 1) (hb : ∀ x, |b x| ≤ 1) (t : ℝ) :
    (productLaw (conditionalSigns a ha J) (conditionalSigns b hb K)).expect
      (fun z => Real.exp (t*(((matchedSites J K τ).card : ℝ)*(conditionalMatched J K τ z-
        setAverage (matchedSites J K τ) (fun x => a x*b (τ x)))))) ≤
        Real.exp (((matchedSites J K τ).card : ℝ)*t^2/2) := by
  simp_rw [conditional_matched_rescale J K τ hI a b]
  have ht := selected_sign_product_mgf (fun i => a (J i)) (fun i => b (K i))
    (fun i => ha (J i)) (fun i => hb (K i)) (leftMatchIndex J K τ) (rightMatchIndex J K τ)
    (left_match_index_injective J K τ) (right_match_index_injective J K τ hτ) t
  simpa only [conditionalSigns,left_match_address,right_match_address,Fintype.card_coe] using ht

/-- Complete original `conditional_matched_noise_tail` guarantee for `MatchedMeasurementNoise`; all source hypotheses and output obligations are retained. -/
theorem conditional_matched_noise_tail {n m : ℕ} (J : Fin n → S) (K : Fin m → S)
    (τ : S → S) (hτ : Function.Injective τ) (hI : 0 < (matchedSites J K τ).card)
    (a b : S → ℝ) (ha : ∀ x, |a x| ≤ 1) (hb : ∀ x, |b x| ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    finiteBadMass (productLaw (conditionalSigns a ha J) (conditionalSigns b hb K))
      (conditionalMatched J K τ) (setAverage (matchedSites J K τ) (fun x => a x*b (τ x))) ε ≤
        2*Real.exp (-((matchedSites J K τ).card : ℝ)*ε^2/2) := by
  apply finite_subgaussian_bad_mass _ _ _ (matchedSites J K τ).card ε hI hε
  exact conditional_matched_mgf J K τ hτ hI a b ha hb

/-- Complete original `conditional_matched_q_noise_tail` guarantee for `MatchedMeasurementNoise`; all source hypotheses and output obligations are retained. -/
theorem conditional_matched_q_noise_tail {n m : ℕ} (J : Fin n → S) (K : Fin m → S)
    (τ : S → S) (hτ : Function.Injective τ) (hI : 0 < (matchedSites J K τ).card)
    (a b : S → ℝ) (ha : ∀ x, |a x| ≤ 1) (hb : ∀ x, |b x| ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    finiteBadMass (productLaw (conditionalSigns a ha J) (conditionalSigns b hb K))
      (fun z => (matchedStatisticQ (fun i => (J i,z.1 i)) (fun i => (K i,z.2 i)) τ : ℝ))
      (setAverage (matchedSites J K τ) (fun x => a x*b (τ x))) ε ≤
        2*Real.exp (-((matchedSites J K τ).card : ℝ)*ε^2/2) := by
  have hF : (fun z : (Fin n → Bool) × (Fin m → Bool) =>
      (matchedStatisticQ (fun i => (J i,z.1 i)) (fun i => (K i,z.2 i)) τ : ℝ))=
        conditionalMatched J K τ := by
    funext z
    exact matched_statistic_cast _ _ _
  rw [hF]
  exact conditional_matched_noise_tail J K τ hτ hI a b ha hb ε hε

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.left_match_index_injective
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.right_match_index_injective
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.conditional_matched_rescale
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.conditional_matched_mgf
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.conditional_matched_noise_tail
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.conditional_matched_q_noise_tail
