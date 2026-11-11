/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.MatchedRestrictedBridge
import Qatlib.Concepts.SpinorSampling.Matching.OccupiedSizeTail
import Qatlib.Concepts.SpinorSampling.Matching.CohortRecordPairs

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Matched Intersection Concentration

Matched Intersection Concentration constructions and identities for Spinor Sampling.
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

/-- Construction for matched Small Mass in the matched intersection concentration model. -/
def matchedSmallMass (τ : Equiv.Perm S) (n m : ℕ) (r : ℝ) : ℝ :=
  (productLaw (cohortLaw (uniformLaw S) n) (cohortLaw (uniformLaw S) m)).expect
    (fun z => if ((matchedSites z.1 z.2 τ).card : ℝ)<r then 1 else 0)

/-- Complete original `matched_intersection_lower_tail` guarantee for `MatchedIntersectionConcentration`; all source hypotheses and output obligations are retained. -/
theorem matched_intersection_lower_tail (τ : Equiv.Perm S) (n m : ℕ)
    (hn0 : 0<n) (hn : n ≤ Fintype.card S) (hm : m ≤ Fintype.card S) :
    matchedSmallMass τ n m ((n : ℝ)*(m : ℝ)/(32*(Fintype.card S : ℝ))) ≤
      2*Real.exp (-(n : ℝ)*(m : ℝ)/(32*(Fintype.card S : ℝ))) := by
  classical
  let r : ℝ := (n : ℝ)*(m : ℝ)/(32*(Fintype.card S : ℝ))
  let C : ℝ := Real.exp (-r)
  have hM : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hrow (J : Fin n → S) :
      (cohortLaw (uniformLaw S) m).expect (fun K =>
        if ((matchedSites J K τ).card : ℝ)<r then 1 else 0) ≤
      (if occupiedCount J < (n : ℝ)/4 then 1 else 0)+C := by
    by_cases hbad : occupiedCount J < (n : ℝ)/4
    · have hone : (cohortLaw (uniformLaw S) m).expect (fun K =>
          if ((matchedSites J K τ).card : ℝ)<r then 1 else 0) ≤ 1 := by
        calc
          _ ≤ (cohortLaw (uniformLaw S) m).expect (fun _ => 1) := by
            apply finite_expect_mono
            intro K
            split_ifs <;> norm_num
          _ = _ := finite_expect_const _ _
      rw [ite_eq_left hbad]
      have hC : 0≤C := (Real.exp_pos _).le
      linarith
    · have hgood : (n : ℝ)/4 ≤ ((occupiedSites J).card : ℝ) := le_of_not_gt hbad
      have hradius : r ≤ (m : ℝ)*((occupiedSites J).card : ℝ)/(8*(Fintype.card S : ℝ)) := by
        have hp := mul_le_mul_of_nonneg_left hgood (show (0 : ℝ)≤m by positivity)
        have hd := div_le_div_of_nonneg_right hp
          (show (0 : ℝ)≤8*(Fintype.card S : ℝ) by positivity)
        have he : (m : ℝ)*((n : ℝ)/4)/(8*(Fintype.card S : ℝ))=r := by dsimp [r]; ring
        rwa [he] at hd
      have hdom : (cohortLaw (uniformLaw S) m).expect (fun K =>
          if ((matchedSites J K τ).card : ℝ)<r then 1 else 0) ≤
          (cohortLaw (uniformLaw S) m).expect (fun K =>
          if ((matchedSites J K τ).card : ℝ)<
            (m : ℝ)*((occupiedSites J).card : ℝ)/(8*(Fintype.card S : ℝ)) then 1 else 0) := by
        apply finite_expect_mono
        intro K
        by_cases hk : ((matchedSites J K τ).card : ℝ)<r
        · have hk' := hk.trans_le hradius
          simp only [ite_eq_left hk, ite_eq_left hk', le_refl]
        · simp only [ite_eq_right hk]
          split_ifs <;> norm_num
      have he : Real.exp (-(m : ℝ)*((occupiedSites J).card : ℝ)/(8*(Fintype.card S : ℝ))) ≤ C := by
        apply Real.exp_le_exp.mpr
        convert neg_le_neg hradius using 1
        ring
      rw [ite_eq_right hbad, zero_add]
      exact hdom.trans ((matched_card_conditional_lower_tail τ J hm).trans he)
  have hsmall := occupied_quarter_lower_tail (S:=S) n hn0 hn
  have hfirst : Real.exp (-(n : ℝ)/8) ≤ C := by
    have hmR : (m : ℝ) ≤ Fintype.card S := by exact_mod_cast hm
    have hnR : (0 : ℝ)≤n := by positivity
    have hp := mul_le_mul_of_nonneg_left hmR hnR
    have hp0 := mul_nonneg hnR hM.le
    have hr : r ≤ (n : ℝ)/8 := by
      dsimp [r]
      apply (div_le_iff₀ (show (0 : ℝ)<32*(Fintype.card S : ℝ) by positivity)).mpr
      nlinarith
    exact Real.exp_le_exp.mpr (by linarith)
  unfold matchedSmallMass
  rw [product_law_expect]
  calc
    _ ≤ (cohortLaw (uniformLaw S) n).expect
        (fun J => (if occupiedCount J<(n : ℝ)/4 then 1 else 0)+C) :=
      finite_expect_mono _ _ _ hrow
    _ = occupiedQuarterBadMass (S:=S) n+C := by
      rw [finite_expect_add, finite_expect_const]
      rfl
    _ ≤ Real.exp (-(n : ℝ)/8)+C := add_le_add hsmall (le_refl C)
    _ ≤ C+C := add_le_add hfirst (le_refl C)
    _ = 2*Real.exp (-(n : ℝ)*(m : ℝ)/(32*(Fintype.card S : ℝ))) := by
      dsimp [C]
      have he : -r = -(n : ℝ)*(m : ℝ)/(32*(Fintype.card S : ℝ)) := by dsimp [r]; ring
      rw [he]
      ring

/-- Complete original `signed_matched_intersection_lower_tail` guarantee for `MatchedIntersectionConcentration`; all source hypotheses and output obligations are retained. -/
theorem signed_matched_intersection_lower_tail (τ : Equiv.Perm S) (n m : ℕ)
    (hn0 : 0<n) (hn : n ≤ Fintype.card S) (hm : m ≤ Fintype.card S)
    (a b : S → ℝ) (ha : ∀ x, |a x|≤1) (hb : ∀ x, |b x|≤1) :
    (productLaw (cohortLaw (signedRecordLaw a ha) n)
      (cohortLaw (signedRecordLaw b hb) m)).expect (fun z =>
        if ((matchedSites (fun i => (z.1 i).1) (fun i => (z.2 i).1) τ).card : ℝ)<
          (n : ℝ)*(m : ℝ)/(32*(Fintype.card S : ℝ)) then 1 else 0) ≤
      2*Real.exp (-(n : ℝ)*(m : ℝ)/(32*(Fintype.card S : ℝ))) := by
  rw [signed_pair_site_projection a b ha hb
    (fun z : (Fin n → S) × (Fin m → S) =>
      if ((matchedSites z.1 z.2 τ).card : ℝ)<
        (n : ℝ)*(m : ℝ)/(32*(Fintype.card S : ℝ)) then 1 else 0)]
  exact matched_intersection_lower_tail τ n m hn0 hn hm

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.matched_intersection_lower_tail
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.signed_matched_intersection_lower_tail
