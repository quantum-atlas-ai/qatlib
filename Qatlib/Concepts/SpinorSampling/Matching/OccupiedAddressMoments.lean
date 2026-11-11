/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.MatchedRecords
import Qatlib.Concepts.SpinorSampling.Matching.MatchedSamplingLaw

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Occupied Address Moments

Occupied Address Moments constructions and identities for Spinor Sampling.
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

/-- Construction for occupied Count in the occupied address moments model. -/
def occupiedCount {n : ℕ} (J : Fin n → S) : ℝ := (occupiedSites J).card

/-- Construction for expected Occupied in the occupied address moments model. -/
def expectedOccupied (n : ℕ) : ℝ := (cohortLaw (uniformLaw S) n).expect occupiedCount

omit [Fintype S] [Nonempty S] in
/-- Complete original `occupied_sites_cons` guarantee for `OccupiedAddressMoments`; all source hypotheses and output obligations are retained. -/
theorem occupied_sites_cons {n : ℕ} (x : S) (J : Fin n → S) :
    occupiedSites (Fin.cons x J)=insert x (occupiedSites J) := by
  ext y
  simp [occupiedSites, Fin.exists_fin_succ, eq_comm]

omit [Fintype S] [Nonempty S] in
/-- Complete original `occupied_count_cons` guarantee for `OccupiedAddressMoments`; all source hypotheses and output obligations are retained. -/
theorem occupied_count_cons {n : ℕ} (x : S) (J : Fin n → S) :
    occupiedCount (Fin.cons x J)=occupiedCount J+if x ∈ occupiedSites J then 0 else 1 := by
  rw [occupiedCount,occupied_sites_cons]
  by_cases hx : x ∈ occupiedSites J
  · rw [ite_eq_left hx,Finset.insert_eq_of_mem hx]
    simp [occupiedCount]
  · rw [ite_eq_right hx,Finset.card_insert_of_notMem hx]
    simp [occupiedCount]

/-- Complete original `uniform_missing_mass` guarantee for `OccupiedAddressMoments`; all source hypotheses and output obligations are retained. -/
theorem uniform_missing_mass (R : Finset S) :
    (uniformLaw S).expect (fun x => if x ∈ R then 0 else 1)=
      1-(R.card : ℝ)/(Fintype.card S : ℝ) := by
  have hmember : (uniformLaw S).expect (fun x => if x ∈ R then 1 else 0)=
      (R.card : ℝ)/(Fintype.card S : ℝ) := by
    unfold FinDist.expect uniformLaw
    simp_rw [mul_ite, mul_one, mul_zero]
    rw [sum_mem_indicator]
    simp only [Finset.sum_const,nsmul_eq_mul]
    ring
  calc
    _ = (uniformLaw S).expect (fun x => 1-(if x ∈ R then 1 else 0)) := by
      congr 1
      funext x
      split_ifs <;> norm_num
    _ = _ := by rw [finite_expect_sub,finite_expect_const,hmember]

/-- Complete original `expected_occupied_recurrence` guarantee for `OccupiedAddressMoments`; all source hypotheses and output obligations are retained. -/
theorem expected_occupied_recurrence (n : ℕ) :
    expectedOccupied (S := S) (n+1)=expectedOccupied (S := S) n+1-
      expectedOccupied (S := S) n/(Fintype.card S : ℝ) := by
  change (∑ J : Fin (n+1) → S, (uniformLaw S).probOf J*occupiedCount J)=_
  rw [product_expect_cons]
  have hcomm : (∑ x : S, (uniformLaw S).prob x*(∑ J : Fin n → S,
      (uniformLaw S).probOf J*occupiedCount (Fin.cons x J)))=
      (cohortLaw (uniformLaw S) n).expect (fun J =>
        (uniformLaw S).expect (fun x => occupiedCount (Fin.cons x J))) := by
    unfold FinDist.expect cohortLaw
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro J _
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hcomm]
  simp_rw [occupied_count_cons,finite_expect_add,finite_expect_const,uniform_missing_mass]
  have hdiv : (cohortLaw (uniformLaw S) n).expect (fun J =>
      occupiedCount J/(Fintype.card S : ℝ))=
      expectedOccupied (S := S) n/(Fintype.card S : ℝ) := by
    unfold expectedOccupied FinDist.expect
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div]
  have hmiss : (cohortLaw (uniformLaw S) n).expect (fun x =>
      1-(occupiedSites x).card/(Fintype.card S : ℝ))=
      1-expectedOccupied (S := S) n/(Fintype.card S : ℝ) := by
    rw [finite_expect_sub, finite_expect_const]
    simpa [occupiedCount] using hdiv
  rw [hmiss]
  change expectedOccupied (S := S) n +
    (1-expectedOccupied (S := S) n/(Fintype.card S : ℝ)) = _
  ring

/-- Complete original `expected_occupied_upper` guarantee for `OccupiedAddressMoments`; all source hypotheses and output obligations are retained. -/
theorem expected_occupied_upper (n : ℕ) : expectedOccupied (S := S) n ≤ n := by
  calc
    _ ≤ (cohortLaw (uniformLaw S) n).expect (fun _ => (n : ℝ)) := by
      apply finite_expect_mono
      intro J
      dsimp [occupiedCount]
      exact_mod_cast occupied_sites_card J
    _ = _ := finite_expect_const _ _

/-- Complete original `expected_occupied_lower` guarantee for `OccupiedAddressMoments`; all source hypotheses and output obligations are retained. -/
theorem expected_occupied_lower (n : ℕ) :
    (n : ℝ)-(n : ℝ)*((n : ℝ)-1)/(2*(Fintype.card S : ℝ)) ≤
      expectedOccupied (S := S) n := by
  have hM : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  induction n with
  | zero => simp [expectedOccupied,FinDist.expect,cohortLaw,FinDist.probOf,occupiedCount,occupiedSites]
  | succ n ih =>
    rw [expected_occupied_recurrence]
    have hupper := div_le_div_of_nonneg_right (expected_occupied_upper (S := S) n) hM.le
    have hstep : ((n+1 : ℕ) : ℝ)-((n+1 : ℕ) : ℝ)*(((n+1 : ℕ) : ℝ)-1)/(2*(Fintype.card S : ℝ))=
        ((n : ℝ)-(n : ℝ)*((n : ℝ)-1)/(2*(Fintype.card S : ℝ)))+1-
          (n : ℝ)/(Fintype.card S : ℝ) := by
      push_cast
      ring
    rw [hstep]
    linarith

/-- Complete original `expected_occupied_half` guarantee for `OccupiedAddressMoments`; all source hypotheses and output obligations are retained. -/
theorem expected_occupied_half (n : ℕ) (hn : n ≤ Fintype.card S) :
    (n : ℝ)/2 ≤ expectedOccupied (S := S) n := by
  have hM : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hnR : (n : ℝ) ≤ Fintype.card S := by exact_mod_cast hn
  have hquad : (n : ℝ)*((n : ℝ)-1) ≤ (n : ℝ)*(Fintype.card S : ℝ) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hdiv := (div_le_iff₀ (show (0 : ℝ)<2*(Fintype.card S : ℝ) by positivity)).mpr
    (show (n : ℝ)*((n : ℝ)-1) ≤ ((n : ℝ)/2)*(2*(Fintype.card S : ℝ)) by nlinarith)
  linarith [expected_occupied_lower (S := S) n]

omit [Fintype S] [Nonempty S] in
/-- Complete original `occupied_count_coordinate` guarantee for `OccupiedAddressMoments`; all source hypotheses and output obligations are retained. -/
theorem occupied_count_coordinate {n : ℕ} (J K : Fin n → S) (i : Fin n)
    (h : ∀ j, j ≠ i → J j=K j) : |occupiedCount J-occupiedCount K| ≤ 1 := by
  have hsubset (A B : Fin n → S) (hAB : ∀ j, j ≠ i → A j=B j) :
      occupiedSites A ⊆ insert (A i) (occupiedSites B) := by
    intro x hx
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hx
    by_cases hj : j=i
    · subst j
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j,Finset.mem_univ j,(hAB j hj).symm⟩)
  have hJK := (Finset.card_le_card (hsubset J K h)).trans (Finset.card_insert_le _ _)
  have hKJ := (Finset.card_le_card (hsubset K J (fun j hj => (h j hj).symm))).trans
    (Finset.card_insert_le _ _)
  have h1 : (occupiedSites J).card ≤ (occupiedSites K).card+1 := hJK
  have h2 : (occupiedSites K).card ≤ (occupiedSites J).card+1 := hKJ
  have h1R : occupiedCount J ≤ occupiedCount K+1 := by
    dsimp [occupiedCount]
    exact_mod_cast h1
  have h2R : occupiedCount K ≤ occupiedCount J+1 := by
    dsimp [occupiedCount]
    exact_mod_cast h2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.occupied_count_cons
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.uniform_missing_mass
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.expected_occupied_recurrence
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.expected_occupied_upper
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.expected_occupied_lower
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.expected_occupied_half
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.occupied_count_coordinate
