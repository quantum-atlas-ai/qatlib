/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.IntersectionTruncatedWeight
import Qatlib.Concepts.SpinorSampling.Matching.CohortRecordPairs

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Restricted Occupancy Tail

Restricted Occupancy Tail constructions and identities for Spinor Sampling.
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

/-- Construction for restricted Occupied in the restricted occupancy tail model. -/
def restrictedOccupied {n : ℕ} (A : Finset S) (J : Fin n → S) : Finset S :=
  occupiedSites J ∩ A

omit [Fintype S] [Nonempty S] in
/-- Complete original `restricted_occupied_cons` guarantee for `RestrictedOccupancyTail`; all source hypotheses and output obligations are retained. -/
theorem restricted_occupied_cons {n : ℕ} (A : Finset S) (x : S) (J : Fin n → S) :
    restrictedOccupied A (Fin.cons x J) = restrictedInsert A (restrictedOccupied A J) x := by
  ext y
  by_cases hx : x ∈ A
  · simp only [restrictedOccupied, occupied_sites_cons, restrictedInsert, ite_eq_left hx,
      Finset.mem_inter, Finset.mem_insert]
    aesop
  · simp only [restrictedOccupied, occupied_sites_cons, restrictedInsert, ite_eq_right hx,
      Finset.mem_inter, Finset.mem_insert]
    aesop

/-- Construction for expected Restricted Weight in the restricted occupancy tail model. -/
def expectedRestrictedWeight (A : Finset S) (T : ℝ) (n : ℕ) : ℝ :=
  (cohortLaw (uniformLaw S) n).expect (fun J => truncatedHitWeight T (restrictedOccupied A J))

/-- Complete original `expected_restricted_weight_step` guarantee for `RestrictedOccupancyTail`; all source hypotheses and output obligations are retained. -/
theorem expected_restricted_weight_step (A : Finset S) (T : ℝ)
    (hT : T ≤ (A.card : ℝ)/2) (n : ℕ) :
    expectedRestrictedWeight A T (n+1) ≤
      (1-(A.card : ℝ)/(4*(Fintype.card S : ℝ)))*expectedRestrictedWeight A T n := by
  change (∑ J : Fin (n+1) → S, (uniformLaw S).probOf J *
    truncatedHitWeight T (restrictedOccupied A J)) ≤ _
  rw [product_expect_cons]
  change (uniformLaw S).expect (fun x =>
    (cohortLaw (uniformLaw S) n).expect (fun J =>
      truncatedHitWeight T (restrictedOccupied A (Fin.cons x J)))) ≤ _
  rw [finite_expect_comm]
  simp_rw [restricted_occupied_cons]
  calc
    _ ≤ (cohortLaw (uniformLaw S) n).expect (fun J =>
        (1-(A.card : ℝ)/(4*(Fintype.card S : ℝ)))*
          truncatedHitWeight T (restrictedOccupied A J)) := by
      apply finite_expect_mono
      intro J
      exact uniform_truncated_weight_step A (restrictedOccupied A J)
        Finset.inter_subset_right T hT
    _ = _ := finite_expect_mul _ _ _

/-- Complete original `expected_restricted_weight_geometric` guarantee for `RestrictedOccupancyTail`; all source hypotheses and output obligations are retained. -/
theorem expected_restricted_weight_geometric (A : Finset S) (T : ℝ)
    (hT : T ≤ (A.card : ℝ)/2) (n : ℕ) :
    expectedRestrictedWeight A T n ≤
      (1-(A.card : ℝ)/(4*(Fintype.card S : ℝ)))^n := by
  have hM : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hD : (A.card : ℝ) ≤ Fintype.card S := by exact_mod_cast A.card_le_univ
  have hc : 0 ≤ 1-(A.card : ℝ)/(4*(Fintype.card S : ℝ)) := by
    have hdiv : (A.card : ℝ)/(4*(Fintype.card S : ℝ)) ≤ 1 := by
      apply (div_le_iff₀ (show (0 : ℝ)<4*(Fintype.card S : ℝ) by positivity)).mpr
      nlinarith
    linarith
  induction n with
  | zero =>
    simp only [pow_zero]
    have hz : expectedRestrictedWeight A T 0 = if (0 : ℝ)<T then 1 else 0 := by
      simp [expectedRestrictedWeight, FinDist.expect, cohortLaw, FinDist.probOf,
        restrictedOccupied, occupiedSites, truncatedHitWeight]
    rw [hz]
    split_ifs <;> norm_num
  | succ n ih =>
    calc
      _ ≤ (1-(A.card : ℝ)/(4*(Fintype.card S : ℝ)))*expectedRestrictedWeight A T n :=
        expected_restricted_weight_step A T hT n
      _ ≤ (1-(A.card : ℝ)/(4*(Fintype.card S : ℝ)))*
          (1-(A.card : ℝ)/(4*(Fintype.card S : ℝ)))^n := mul_le_mul_of_nonneg_left ih hc
      _ = _ := by rw [pow_succ]; ring

/-- Construction for restricted Hit Bad Mass in the restricted occupancy tail model. -/
def restrictedHitBadMass (A : Finset S) (T : ℝ) (n : ℕ) : ℝ :=
  (cohortLaw (uniformLaw S) n).expect
    (fun J => if ((restrictedOccupied A J).card : ℝ)<T then 1 else 0)

/-- Complete original `restricted_occupancy_lower_tail` guarantee for `RestrictedOccupancyTail`; all source hypotheses and output obligations are retained. -/
theorem restricted_occupancy_lower_tail (A : Finset S) (m : ℕ)
    (hm : m ≤ Fintype.card S) :
    restrictedHitBadMass A ((m : ℝ)*(A.card : ℝ)/(8*(Fintype.card S : ℝ))) m ≤
      Real.exp (-(m : ℝ)*(A.card : ℝ)/(8*(Fintype.card S : ℝ))) := by
  classical
  let T : ℝ := (m : ℝ)*(A.card : ℝ)/(8*(Fintype.card S : ℝ))
  let c : ℝ := 1-(A.card : ℝ)/(4*(Fintype.card S : ℝ))
  have hM : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hD : (A.card : ℝ) ≤ Fintype.card S := by exact_mod_cast A.card_le_univ
  have hmR : (m : ℝ) ≤ Fintype.card S := by exact_mod_cast hm
  have hD0 : (0 : ℝ) ≤ A.card := by positivity
  have hT : T ≤ (A.card : ℝ)/2 := by
    dsimp [T]
    apply (div_le_iff₀ (show (0 : ℝ)<8*(Fintype.card S : ℝ) by positivity)).mpr
    have hp := mul_le_mul_of_nonneg_right hmR hD0
    have hp0 := mul_nonneg hM.le hD0
    nlinarith
  have hc : 0 ≤ c := by
    have hdiv : (A.card : ℝ)/(4*(Fintype.card S : ℝ)) ≤ 1 := by
      apply (div_le_iff₀ (show (0 : ℝ)<4*(Fintype.card S : ℝ) by positivity)).mpr
      nlinarith
    dsimp [c]
    linarith
  have he : c ≤ Real.exp (-(A.card : ℝ)/(4*(Fintype.card S : ℝ))) := by
    have hx := Real.add_one_le_exp (-(A.card : ℝ)/(4*(Fintype.card S : ℝ)))
    dsimp [c]
    calc
      _ = -(A.card : ℝ)/(4*(Fintype.card S : ℝ))+1 := by ring
      _ ≤ _ := hx
  have hpow : c^m ≤ Real.exp (-(m : ℝ)*(A.card : ℝ)/(4*(Fintype.card S : ℝ))) := by
    calc
      _ ≤ (Real.exp (-(A.card : ℝ)/(4*(Fintype.card S : ℝ))))^m := pow_le_pow_left₀ hc he m
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hpoint (J : Fin m → S) :
      (if ((restrictedOccupied A J).card : ℝ)<T then (1 : ℝ) else 0) ≤
        Real.exp T * truncatedHitWeight T (restrictedOccupied A J) := by
    by_cases hj : ((restrictedOccupied A J).card : ℝ)<T
    · rw [ite_eq_left hj, truncatedHitWeight, ite_eq_left hj, ← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      linarith
    · simp only [ite_eq_right hj, truncatedHitWeight, mul_zero, le_refl]
  change restrictedHitBadMass A T m ≤ _
  calc
    _ ≤ (cohortLaw (uniformLaw S) m).expect
        (fun J => Real.exp T * truncatedHitWeight T (restrictedOccupied A J)) :=
      finite_expect_mono _ _ _ hpoint
    _ = Real.exp T * expectedRestrictedWeight A T m := finite_expect_mul _ _ _
    _ ≤ Real.exp T * c^m := mul_le_mul_of_nonneg_left
      (expected_restricted_weight_geometric A T hT m) (Real.exp_pos _).le
    _ ≤ Real.exp T * Real.exp (-(m : ℝ)*(A.card : ℝ)/(4*(Fintype.card S : ℝ))) :=
      mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [T]; ring

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.restricted_occupied_cons
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.expected_restricted_weight_step
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.expected_restricted_weight_geometric
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.restricted_occupancy_lower_tail
