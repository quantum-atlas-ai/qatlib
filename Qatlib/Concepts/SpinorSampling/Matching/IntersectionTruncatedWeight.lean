/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.OccupiedAddressMoments

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Intersection Truncated Weight

Intersection Truncated Weight constructions and identities for Spinor Sampling.
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

/-- Construction for restricted Insert in the intersection truncated weight model. -/
def restrictedInsert (A B : Finset S) (x : S) : Finset S :=
  if x ∈ A then insert x B else B

/-- Construction for truncated Hit Weight in the intersection truncated weight model. -/
def truncatedHitWeight (T : ℝ) (B : Finset S) : ℝ :=
  if (B.card : ℝ) < T then Real.exp (-(B.card : ℝ)) else 0

omit [Fintype S] [Nonempty S] in
/-- Complete original `restricted_insert_card` guarantee for `IntersectionTruncatedWeight`; all source hypotheses and output obligations are retained. -/
theorem restricted_insert_card (A B : Finset S) (x : S) :
    (restrictedInsert A B x).card = B.card + if x ∈ A \ B then 1 else 0 := by
  by_cases ha : x ∈ A
  · by_cases hb : x ∈ B
    · simp [restrictedInsert, ha, hb, Finset.insert_eq_of_mem hb]
    · simp [restrictedInsert, ha, hb, Finset.card_insert_of_notMem hb]
  · simp [restrictedInsert, ha]

omit [Fintype S] [Nonempty S] in
/-- Complete original `restricted_insert_card_mono` guarantee for `IntersectionTruncatedWeight`; all source hypotheses and output obligations are retained. -/
theorem restricted_insert_card_mono (A B : Finset S) (x : S) :
    B.card ≤ (restrictedInsert A B x).card := by
  rw [restricted_insert_card]
  omega

omit [Fintype S] [Nonempty S] in
/-- Complete original `restricted_insert_subset` guarantee for `IntersectionTruncatedWeight`; all source hypotheses and output obligations are retained. -/
theorem restricted_insert_subset (A B : Finset S) (hB : B ⊆ A) (x : S) :
    restrictedInsert A B x ⊆ A := by
  by_cases hx : x ∈ A
  · simpa only [restrictedInsert, ite_eq_left hx] using Finset.insert_subset hx hB
  · simpa only [restrictedInsert, ite_eq_right hx] using hB

/-- Complete original `uniform_insert_exponential` guarantee for `IntersectionTruncatedWeight`; all source hypotheses and output obligations are retained. -/
theorem uniform_insert_exponential (A B : Finset S) :
    (uniformLaw S).expect (fun x => Real.exp (-((restrictedInsert A B x).card : ℝ))) =
      Real.exp (-(B.card : ℝ)) *
        (1 - ((A \ B).card : ℝ)/(Fintype.card S : ℝ)*(1-Real.exp (-1))) := by
  have hpoint (x : S) : Real.exp (-((restrictedInsert A B x).card : ℝ)) =
      Real.exp (-(B.card : ℝ)) *
        (Real.exp (-1) + (1-Real.exp (-1))*(if x ∈ A \ B then 0 else 1)) := by
    rw [restricted_insert_card]
    by_cases hx : x ∈ A \ B
    · simp only [ite_eq_left hx, Nat.cast_add, Nat.cast_one, mul_zero, add_zero]
      rw [neg_add, Real.exp_add]
    · simp only [ite_eq_right hx, Nat.add_zero, mul_one]
      ring
  simp_rw [hpoint]
  rw [finite_expect_mul, finite_expect_add, finite_expect_const,
    finite_expect_mul, uniform_missing_mass]
  ring

/-- Complete original `exp_neg_one_le_half` guarantee for `IntersectionTruncatedWeight`; all source hypotheses and output obligations are retained. -/
theorem exp_neg_one_le_half : Real.exp (-1 : ℝ) ≤ 1/2 := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hprod : Real.exp (-1 : ℝ)*Real.exp 1=1 := by
    rw [← Real.exp_add]
    norm_num
  have hmul := mul_le_mul_of_nonneg_right htwo (Real.exp_pos (-1 : ℝ)).le
  nlinarith

/-- Complete original `uniform_truncated_weight_step` guarantee for `IntersectionTruncatedWeight`; all source hypotheses and output obligations are retained. -/
theorem uniform_truncated_weight_step (A B : Finset S) (hB : B ⊆ A)
    (T : ℝ) (hT : T ≤ (A.card : ℝ)/2) :
    (uniformLaw S).expect (fun x => truncatedHitWeight T (restrictedInsert A B x)) ≤
      (1-(A.card : ℝ)/(4*(Fintype.card S : ℝ)))*truncatedHitWeight T B := by
  have hM : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  by_cases hr : (B.card : ℝ) < T
  · have hupper (x : S) : truncatedHitWeight T (restrictedInsert A B x) ≤
        Real.exp (-((restrictedInsert A B x).card : ℝ)) := by
      unfold truncatedHitWeight
      split_ifs
      · exact le_rfl
      · exact (Real.exp_pos _).le
    have hc : ((A \ B).card : ℝ) = (A.card : ℝ)-(B.card : ℝ) := by
      rw [Finset.card_sdiff_of_subset hB, Nat.cast_sub (Finset.card_le_card hB)]
    have hq : (A.card : ℝ)/(2*(Fintype.card S : ℝ)) ≤
        ((A \ B).card : ℝ)/(Fintype.card S : ℝ) := by
      rw [hc]
      apply (le_div_iff₀ hM).mpr
      have heq : (A.card : ℝ)/(2*(Fintype.card S : ℝ))*(Fintype.card S : ℝ)=
          (A.card : ℝ)/2 := by field_simp [ne_of_gt hM]
      rw [heq]
      linarith
    have hq0 : 0 ≤ ((A \ B).card : ℝ)/(Fintype.card S : ℝ) := by positivity
    have hfactor : 1-((A \ B).card : ℝ)/(Fintype.card S : ℝ)*(1-Real.exp (-1)) ≤
        1-(A.card : ℝ)/(4*(Fintype.card S : ℝ)) := by
      have heq : (A.card : ℝ)/(2*(Fintype.card S : ℝ))/2 =
          (A.card : ℝ)/(4*(Fintype.card S : ℝ)) := by ring
      have he := exp_neg_one_le_half
      have hmul := mul_le_mul_of_nonneg_left
        (show (1 : ℝ)/2 ≤ 1-Real.exp (-1) by linarith) hq0
      nlinarith
    calc
      _ ≤ (uniformLaw S).expect (fun x => Real.exp (-((restrictedInsert A B x).card : ℝ))) :=
        finite_expect_mono _ _ _ hupper
      _ = _ := uniform_insert_exponential A B
      _ ≤ Real.exp (-(B.card : ℝ)) * (1-(A.card : ℝ)/(4*(Fintype.card S : ℝ))) :=
        mul_le_mul_of_nonneg_left hfactor (Real.exp_pos _).le
      _ = _ := by rw [truncatedHitWeight, ite_eq_left hr]; ring
  · have hz (x : S) : truncatedHitWeight T (restrictedInsert A B x)=0 := by
      have hcard : (B.card : ℝ) ≤ (restrictedInsert A B x).card := by
        exact_mod_cast restricted_insert_card_mono A B x
      have hn : ¬ ((restrictedInsert A B x).card : ℝ) < T := by linarith
      simp only [truncatedHitWeight, ite_eq_right hn]
    simp_rw [hz]
    rw [finite_expect_const, truncatedHitWeight, ite_eq_right hr, mul_zero]

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.restricted_insert_card
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.uniform_insert_exponential
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.uniform_truncated_weight_step
