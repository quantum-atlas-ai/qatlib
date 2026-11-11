/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Model.BornCurrentRecords
import Mathlib.Data.List.FinRange

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Matched Records

Matched Records constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched
open scoped BigOperators

variable {S : Type*} [DecidableEq S]

/-- Construction for first Address Index in the matched records model. -/
def firstAddressIndex {n : ℕ} (J : Fin n → S) (x : S) : Option (Fin n) :=
  (List.finRange n).find? (fun i => decide (J i=x))

/-- Construction for first Sign Z in the matched records model. -/
def firstSignZ {n : ℕ} (ω : Fin n → S × Bool) (x : S) : ℤ :=
  match firstAddressIndex (fun i => (ω i).1) x with
  | none => 0
  | some i => recordSignZ (ω i).2

/-- Construction for occupied Sites in the matched records model. -/
def occupiedSites {n : ℕ} (J : Fin n → S) : Finset S := Finset.univ.image J

/-- Construction for matched Sites in the matched records model. -/
def matchedSites {n m : ℕ} (J : Fin n → S) (K : Fin m → S) (τ : S → S) : Finset S :=
  (occupiedSites J).filter (fun x => τ x ∈ occupiedSites K)

/-- Construction for matched Statistic Q in the matched records model. -/
def matchedStatisticQ {n m : ℕ} (ω : Fin n → S × Bool) (ν : Fin m → S × Bool)
    (τ : S → S) : ℚ :=
  let I := matchedSites (fun i => (ω i).1) (fun i => (ν i).1) τ
  if I.card=0 then 0 else
    (∑ x ∈ I, ((firstSignZ ω x*firstSignZ ν (τ x) : ℤ) : ℚ))/(I.card : ℚ)

noncomputable section

/-- Construction for matched Statistic in the matched records model. -/
def matchedStatistic {n m : ℕ} (ω : Fin n → S × Bool) (ν : Fin m → S × Bool)
    (τ : S → S) : ℝ :=
  let I := matchedSites (fun i => (ω i).1) (fun i => (ν i).1) τ
  if I.card=0 then 0 else
    (∑ x ∈ I, (firstSignZ ω x : ℝ)*(firstSignZ ν (τ x) : ℝ))/(I.card : ℝ)

/-- Complete original `matched_statistic_cast` guarantee for `MatchedRecords`; all source hypotheses and output obligations are retained. -/
theorem matched_statistic_cast {n m : ℕ} (ω : Fin n → S × Bool) (ν : Fin m → S × Bool)
    (τ : S → S) : (matchedStatisticQ ω ν τ : ℝ)=matchedStatistic ω ν τ := by
  dsimp only [matchedStatisticQ, matchedStatistic]
  split_ifs
  · norm_num
  · push_cast
    rfl

/-- Complete original `first_sign_abs` guarantee for `MatchedRecords`; all source hypotheses and output obligations are retained. -/
theorem first_sign_abs {n : ℕ} (ω : Fin n → S × Bool) (x : S) :
    |(firstSignZ ω x : ℝ)| ≤ 1 := by
  cases h : firstAddressIndex (fun i => (ω i).1) x with
  | none => simp [firstSignZ,h]
  | some i => cases hb : (ω i).2 <;> norm_num [firstSignZ,h,recordSignZ,hb]

/-- Complete original `matched_statistic_abs` guarantee for `MatchedRecords`; all source hypotheses and output obligations are retained. -/
theorem matched_statistic_abs {n m : ℕ} (ω : Fin n → S × Bool) (ν : Fin m → S × Bool)
    (τ : S → S) : |matchedStatistic ω ν τ| ≤ 1 := by
  let I := matchedSites (fun i => (ω i).1) (fun i => (ν i).1) τ
  change |if I.card=0 then 0 else
    (∑ x ∈ I, (firstSignZ ω x : ℝ)*(firstSignZ ν (τ x) : ℝ))/(I.card : ℝ)| ≤ _
  by_cases hI : I.card=0
  · simp [hI]
  · rw [ite_eq_right hI, abs_div, abs_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hI : (0 : ℝ) < I.card)]
    apply (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hI : (0 : ℝ) < I.card)).mpr
    calc
      _ ≤ ∑ x ∈ I, |(firstSignZ ω x : ℝ)*(firstSignZ ν (τ x) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x ∈ I, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro x hx
        rw [abs_mul]
        exact (mul_le_mul (first_sign_abs ω x) (first_sign_abs ν (τ x))
          (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (by ring)
      _ = 1*(I.card : ℝ) := by simp

/-- Complete original `occupied_sites_card` guarantee for `MatchedRecords`; all source hypotheses and output obligations are retained. -/
theorem occupied_sites_card {n : ℕ} (J : Fin n → S) : (occupiedSites J).card ≤ n := by
  simpa [occupiedSites] using Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := J)

/-- Complete original `matched_sites_card_left` guarantee for `MatchedRecords`; all source hypotheses and output obligations are retained. -/
theorem matched_sites_card_left {n m : ℕ} (J : Fin n → S) (K : Fin m → S) (τ : S → S) :
    (matchedSites J K τ).card ≤ n :=
  (Finset.card_le_card (Finset.filter_subset _ _)).trans (occupied_sites_card J)

/-- Complete original `first_address_none_iff` guarantee for `MatchedRecords`; all source hypotheses and output obligations are retained. -/
theorem first_address_none_iff {n : ℕ} (J : Fin n → S) (x : S) :
    firstAddressIndex J x=none ↔ x ∉ occupiedSites J := by
  simp [firstAddressIndex,occupiedSites]

/-- Complete original `first_address_some` guarantee for `MatchedRecords`; all source hypotheses and output obligations are retained. -/
theorem first_address_some {n : ℕ} (J : Fin n → S) (x : S) (i : Fin n)
    (h : firstAddressIndex J x=some i) : J i=x := by
  change (List.finRange n).find? (fun j => decide (J j=x))=some i at h
  simpa only [decide_eq_true_eq] using List.find?_some h

/-- Complete original `first_address_exists` guarantee for `MatchedRecords`; all source hypotheses and output obligations are retained. -/
theorem first_address_exists {n : ℕ} (J : Fin n → S) (x : S) (hx : x ∈ occupiedSites J) :
    ∃ i : Fin n, firstAddressIndex J x=some i ∧ J i=x := by
  cases h : firstAddressIndex J x with
  | none => exact False.elim ((first_address_none_iff J x).mp h hx)
  | some i => exact ⟨i,rfl,first_address_some J x i h⟩

/-- Construction for chosen First Index in the matched records model. -/
def chosenFirstIndex {n : ℕ} (J : Fin n → S) (x : S) (hx : x ∈ occupiedSites J) : Fin n :=
  Classical.choose (first_address_exists J x hx)

/-- Complete original `chosen_first_index_spec` guarantee for `MatchedRecords`; all source hypotheses and output obligations are retained. -/
theorem chosen_first_index_spec {n : ℕ} (J : Fin n → S) (x : S) (hx : x ∈ occupiedSites J) :
    firstAddressIndex J x=some (chosenFirstIndex J x hx) ∧ J (chosenFirstIndex J x hx)=x :=
  Classical.choose_spec (first_address_exists J x hx)

/-- Complete original `chosen_first_index_injective` guarantee for `MatchedRecords`; all source hypotheses and output obligations are retained. -/
theorem chosen_first_index_injective {n : ℕ} (J : Fin n → S) :
    Function.Injective (fun x : occupiedSites J => chosenFirstIndex J x x.property) := by
  intro x y h
  apply Subtype.ext
  calc
    (x : S) = J (chosenFirstIndex J x x.property) := (chosen_first_index_spec J x x.property).2.symm
    _ = J (chosenFirstIndex J y y.property) := congrArg J h
    _ = (y : S) := (chosen_first_index_spec J y y.property).2

/-- Complete original `first_sign_real_eq` guarantee for `MatchedRecords`; all source hypotheses and output obligations are retained. -/
theorem first_sign_real_eq {n : ℕ} (ω : Fin n → S × Bool) (x : S) (i : Fin n)
    (h : firstAddressIndex (fun j => (ω j).1) x=some i) :
    (firstSignZ ω x : ℝ)=recordSign (ω i).2 := by
  rw [firstSignZ,h]
  exact record_sign_cast _

/-- Complete original `mem_matched_sites` guarantee for `MatchedRecords`; all source hypotheses and output obligations are retained. -/
theorem mem_matched_sites {n m : ℕ} (J : Fin n → S) (K : Fin m → S) (τ : S → S) (x : S) :
    x ∈ matchedSites J K τ ↔ x ∈ occupiedSites J ∧ τ x ∈ occupiedSites K := Finset.mem_filter

/-- Complete original `matched_sites_card_right` guarantee for `MatchedRecords`; all source hypotheses and output obligations are retained. -/
theorem matched_sites_card_right {n m : ℕ} (J : Fin n → S) (K : Fin m → S) (τ : S → S)
    (hτ : Function.Injective τ) : (matchedSites J K τ).card ≤ m := by
  have hm : Set.MapsTo τ (matchedSites J K τ) (occupiedSites K) := by
    intro x hx
    exact ((mem_matched_sites J K τ x).mp hx).2
  exact (Finset.card_le_card_of_injOn τ hm hτ.injOn).trans (occupied_sites_card K)

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.matched_statistic_cast
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.first_sign_abs
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.matched_statistic_abs
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.matched_sites_card_left
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.chosen_first_index_injective
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.first_sign_real_eq
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.matched_sites_card_right
