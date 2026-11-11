/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.MatchedIntersectionConcentration
import Qatlib.Concepts.SpinorSampling.Matching.MatchedSignedConditionalTail

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Matched Unconditional Tail

Matched Unconditional Tail constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched
noncomputable section
open scoped BigOperators
open Qatlib

/-- Complete original `expect_finset_nat_sum` guarantee for `MatchedUnconditionalTail`; all source hypotheses and output obligations are retained. -/
private theorem expect_finset_nat_sum {X : Type} [Fintype X]
    (p : FinDist X) (s : Finset ℕ) (g : ℕ → X → ℝ) :
    p.expect (fun x => ∑ k ∈ s, g k x) = ∑ k ∈ s, p.expect (g k) := by
  unfold FinDist.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

variable {S : Type} [Fintype S] [Nonempty S] [DecidableEq S]

/-- Complete original `signed_matched_unconditional_tail` guarantee for `MatchedUnconditionalTail`; all source hypotheses and output obligations are retained. -/
theorem signed_matched_unconditional_tail (τ : Equiv.Perm S) (n m : ℕ)
    (hn0 : 0<n) (hm0 : 0<m) (hn : n ≤ Fintype.card S) (hm : m ≤ Fintype.card S)
    (a b : S → ℝ) (ha : ∀ x, |a x|≤1) (hb : ∀ x, |b x|≤1)
    (ε : ℝ) (hε0 : 0<ε) (hε1 : ε≤1) :
    finiteBadMass (productLaw (cohortLaw (signedRecordLaw a ha) n)
      (cohortLaw (signedRecordLaw b hb) m))
      (fun z => (matchedStatisticQ z.1 z.2 τ : ℝ))
      (setAverage Finset.univ (fun x => a x*b (τ x))) ε ≤
      6*Real.exp (-(n : ℝ)*(m : ℝ)*ε^2/(256*(Fintype.card S : ℝ))) := by
  classical
  let p := productLaw (cohortLaw (signedRecordLaw a ha) n) (cohortLaw (signedRecordLaw b hb) m)
  let R : ((Fin n → S × Bool) × (Fin m → S × Bool)) → ℕ := fun z =>
    (matchedSites (fun i => (z.1 i).1) (fun i => (z.2 i).1) τ).card
  let F : ((Fin n → S × Bool) × (Fin m → S × Bool)) → ℝ :=
    fun z => (matchedStatisticQ z.1 z.2 τ : ℝ)
  let μ := setAverage Finset.univ (fun x => a x*b (τ x))
  let r : ℝ := (n : ℝ)*(m : ℝ)/(32*(Fintype.card S : ℝ))
  let c : ℝ := 4*Real.exp (-r*ε^2/8)
  let L := min n (min m (Fintype.card S))
  let t : Finset ℕ := (Finset.range (L+1)).filter (fun k => r ≤ (k : ℝ))
  let N : ℕ → ℝ := fun k => p.expect (fun z =>
    if R z=k then (if ε < |F z-μ| then 1 else 0) else 0)
  let D : ℕ → ℝ := fun k => p.expect (fun z => if R z=k then 1 else 0)
  have hM : (0 : ℝ)<Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hr : 0<r := by dsimp [r]; positivity
  have hc : 0≤c := by dsimp [c]; positivity
  have hRmax (z : (Fin n → S × Bool) × (Fin m → S × Bool)) : R z ≤ L := by
    apply le_min
    · exact matched_sites_card_left _ _ _
    · apply le_min
      · have hs : restrictedOccupied ((occupiedSites (fun i => (z.1 i).1)).image τ)
            (fun i => (z.2 i).1) ⊆ occupiedSites (fun i => (z.2 i).1) := Finset.inter_subset_left
        have hh := Finset.card_le_card hs
        rw [restricted_occupied_shifted_card] at hh
        exact hh.trans (occupied_sites_card (fun i => (z.2 i).1))
      · exact (matchedSites (fun i => (z.1 i).1) (fun i => (z.2 i).1) τ).card_le_univ
  have hstratum (k : ℕ) (hk : k ∈ t) : N k ≤ c*D k := by
    obtain ⟨hkRange,hkr⟩ := Finset.mem_filter.mp hk
    have hkL : k≤L := by have hh := Finset.mem_range.mp hkRange; omega
    have hkn : k≤n := by dsimp [L] at hkL; omega
    have hkm : k≤m := by dsimp [L] at hkL; omega
    have hkS : k≤Fintype.card S := by dsimp [L] at hkL; omega
    have hk0 : 0<k := by exact_mod_cast hr.trans_le hkr
    have hD : D k=matchedCardEventMass τ n m k := signed_pair_matched_card_mass τ a b ha hb
    have hDpos : 0<D k := by rw [hD]; exact matched_card_event_mass_pos τ hk0 hkn hkm hkS
    have hcond := signed_matched_conditional_tail τ hk0 hkn hkm hkS a b ha hb ε hε0
    unfold signedMatchedConditionalBadMass at hcond
    change N k / D k ≤ 4*Real.exp (-(k : ℝ)*ε^2/8) at hcond
    have hbound : 4*Real.exp (-(k : ℝ)*ε^2/8) ≤ c := by
      have hp := mul_le_mul_of_nonneg_right hkr (sq_nonneg ε)
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ)≤4)
      exact Real.exp_le_exp.mpr (by linarith)
    exact ((div_le_iff₀ hDpos).mp hcond).trans
      (mul_le_mul_of_nonneg_right hbound hDpos.le)
  have hDsum : (∑ k ∈ t, D k)≤1 := by
    calc
      _ = p.expect (fun z => ∑ k ∈ t, if R z=k then 1 else 0) :=
        (expect_finset_nat_sum p t _).symm
      _ ≤ p.expect (fun _ => 1) := by
        apply finite_expect_mono
        intro z
        by_cases hz : R z ∈ t <;> simp [eq_comm,hz]
      _ = _ := finite_expect_const _ _
  have hNsum : (∑ k ∈ t, N k)≤c := by
    calc
      _ ≤ ∑ k ∈ t, c*D k := Finset.sum_le_sum hstratum
      _ = c*(∑ k ∈ t, D k) := (Finset.mul_sum _ _ _).symm
      _ ≤ c*1 := mul_le_mul_of_nonneg_left hDsum hc
      _ = _ := mul_one c
  have hpoint (z : (Fin n → S × Bool) × (Fin m → S × Bool)) :
      (if ε < |F z-μ| then (1 : ℝ) else 0) ≤
      (if (R z : ℝ)<r then 1 else 0) +
        ∑ k ∈ t, if R z=k then (if ε < |F z-μ| then 1 else 0) else 0 := by
    by_cases hs : (R z : ℝ)<r
    · have hnonneg : (0 : ℝ)≤∑ k ∈ t,
          if R z=k then (if ε < |F z-μ| then 1 else 0) else 0 := by
        apply Finset.sum_nonneg
        intro k _
        split_ifs <;> norm_num
      rw [ite_eq_left hs]
      have hbase : (if ε < |F z-μ| then (1 : ℝ) else 0) ≤ 1 := by
        split_ifs <;> norm_num
      have hle : (1 : ℝ) ≤ 1 + ∑ k ∈ t,
          if R z=k then (if ε < |F z-μ| then 1 else 0) else 0 := by
        linarith only [hnonneg]
      exact hbase.trans hle
    · rw [ite_eq_right hs, zero_add]
      by_cases hbad : ε < |F z-μ|
      · have hmem : R z ∈ t := by
          apply Finset.mem_filter.mpr
          constructor
          · apply Finset.mem_range.mpr
            have hh := hRmax z
            omega
          · exact le_of_not_gt hs
        have hsingle := Finset.single_le_sum
          (fun k (_hk : k ∈ t) => show (0 : ℝ)≤
            (if R z=k then (if ε < |F z-μ| then 1 else 0) else 0) from by
              split_ifs <;> norm_num) hmem
        simpa only [ite_eq_left rfl, ite_eq_left hbad,ite_true] using hsingle
      · simp only [ite_eq_right hbad, ite_self, Finset.sum_const_zero, le_refl]
  have hsmall : p.expect (fun z => if (R z : ℝ)<r then 1 else 0) ≤ 2*Real.exp (-r) := by
    have hh := signed_matched_intersection_lower_tail τ n m hn0 hn hm a b ha hb
    have he : -(n : ℝ)*(m : ℝ)/(32*(Fintype.card S : ℝ)) = -r := by dsimp [r]; ring
    simpa only [he] using hh
  have hexp : Real.exp (-r) ≤ Real.exp (-r*ε^2/8) := by
    have hsq : ε^2≤1 := by nlinarith
    have hp := mul_le_mul_of_nonneg_left hsq hr.le
    exact Real.exp_le_exp.mpr (by nlinarith)
  change finiteBadMass p F μ ε ≤ _
  rw [← finite_bad_indicator_mean]
  calc
    _ ≤ p.expect (fun z => (if (R z : ℝ)<r then 1 else 0) +
        ∑ k ∈ t, if R z=k then (if ε < |F z-μ| then 1 else 0) else 0) :=
      finite_expect_mono _ _ _ hpoint
    _ = p.expect (fun z => if (R z : ℝ)<r then 1 else 0) + ∑ k ∈ t, N k := by
      rw [finite_expect_add, expect_finset_nat_sum]
    _ ≤ 2*Real.exp (-r)+c := add_le_add hsmall hNsum
    _ ≤ 6*Real.exp (-r*ε^2/8) := by dsimp [c]; linarith
    _ = _ := by
      congr 1
      congr 1
      dsimp [r]
      ring

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.signed_matched_unconditional_tail
