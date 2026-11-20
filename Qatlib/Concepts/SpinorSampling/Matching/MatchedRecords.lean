/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.SpinorSampling.Model.BornCurrentRecords
public import Mathlib.Data.List.FinRange

@[expose] public section

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

/-- The rational matched statistic casts to the real average of the first-sign products, with
zero returned in both versions for an empty matched set. -/
theorem matched_statistic_cast {n m : ℕ} (ω : Fin n → S × Bool) (ν : Fin m → S × Bool)
    (τ : S → S) : (matchedStatisticQ ω ν τ : ℝ)=matchedStatistic ω ν τ := by
  dsimp only [matchedStatisticQ, matchedStatistic]
  split_ifs
  · norm_num
  · push_cast
    rfl

/-- The first-sign lookup has absolute value at most one, including its zero value at an absent
site. -/
theorem first_sign_abs {n : ℕ} (ω : Fin n → S × Bool) (x : S) :
    |(firstSignZ ω x : ℝ)| ≤ 1 := by
  cases h : firstAddressIndex (fun i => (ω i).1) x with
  | none => simp [firstSignZ,h]
  | some i => cases hb : (ω i).2 <;> norm_num [firstSignZ,h,recordSignZ,hb]

/-- For any two record arrays and any match map, the real matched statistic lies in [−1, 1]. -/
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

/-- An array of length `n` occupies at most `n` distinct sites. -/
theorem occupied_sites_card {n : ℕ} (J : Fin n → S) : (occupiedSites J).card ≤ n := by
  simpa [occupiedSites] using Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := J)

/-- The matched set contains at most as many sites as there are entries in the left array. -/
theorem matched_sites_card_left {n m : ℕ} (J : Fin n → S) (K : Fin m → S) (τ : S → S) :
    (matchedSites J K τ).card ≤ n :=
  (Finset.card_le_card (Finset.filter_subset _ _)).trans (occupied_sites_card J)

/-- The first-index search returns `none` exactly for sites absent from the array. -/
theorem first_address_none_iff {n : ℕ} (J : Fin n → S) (x : S) :
    firstAddressIndex J x=none ↔ x ∉ occupiedSites J := by
  simp [firstAddressIndex,occupiedSites]

/-- If the first-index search for `x` returns `i`, the array entry at `i` is `x`. -/
theorem first_address_some {n : ℕ} (J : Fin n → S) (x : S) (i : Fin n)
    (h : firstAddressIndex J x=some i) : J i=x := by
  change (List.finRange n).find? (fun j => decide (J j=x))=some i at h
  simpa only [decide_eq_true_eq] using List.find?_some h

/-- For an occupied site, the first-index search returns some index at which the array contains
that site. -/
theorem first_address_exists {n : ℕ} (J : Fin n → S) (x : S) (hx : x ∈ occupiedSites J) :
    ∃ i : Fin n, firstAddressIndex J x=some i ∧ J i=x := by
  cases h : firstAddressIndex J x with
  | none => exact False.elim ((first_address_none_iff J x).mp h hx)
  | some i => exact ⟨i,rfl,first_address_some J x i h⟩

/-- Construction for chosen First Index in the matched records model. -/
def chosenFirstIndex {n : ℕ} (J : Fin n → S) (x : S) (hx : x ∈ occupiedSites J) : Fin n :=
  Classical.choose (first_address_exists J x hx)

/-- For an occupied site, the chosen index is exactly the index returned by the first-address
lookup and its array entry is the given site. -/
theorem chosen_first_index_spec {n : ℕ} (J : Fin n → S) (x : S) (hx : x ∈ occupiedSites J) :
    firstAddressIndex J x=some (chosenFirstIndex J x hx) ∧ J (chosenFirstIndex J x hx)=x :=
  Classical.choose_spec (first_address_exists J x hx)

/-- Choosing the first index of each occupied site gives an injection from occupied sites into
array indices. -/
theorem chosen_first_index_injective {n : ℕ} (J : Fin n → S) :
    Function.Injective (fun x : occupiedSites J => chosenFirstIndex J x x.property) := by
  intro x y h
  apply Subtype.ext
  calc
    (x : S) = J (chosenFirstIndex J x x.property) := (chosen_first_index_spec J x x.property).2.symm
    _ = J (chosenFirstIndex J y y.property) := congrArg J h
    _ = (y : S) := (chosen_first_index_spec J y y.property).2

/-- When the address lookup finds `i` for a site, the real cast of its first sign is the sign
encoded by record `i`. -/
theorem first_sign_real_eq {n : ℕ} (ω : Fin n → S × Bool) (x : S) (i : Fin n)
    (h : firstAddressIndex (fun j => (ω j).1) x=some i) :
    (firstSignZ ω x : ℝ)=recordSign (ω i).2 := by
  rw [firstSignZ,h]
  exact record_sign_cast _

/-- A site is matched exactly when it occurs in the left array and its image under `τ` occurs in
the right array. -/
theorem mem_matched_sites {n m : ℕ} (J : Fin n → S) (K : Fin m → S) (τ : S → S) (x : S) :
    x ∈ matchedSites J K τ ↔ x ∈ occupiedSites J ∧ τ x ∈ occupiedSites K := Finset.mem_filter

/-- An injective match map bounds the number of matched sites by the length of the right array. -/
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
