/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Retained.RetainedBellStrata

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Retained Bell Pooling

Retained Bell Pooling constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
noncomputable section
open scoped BigOperators Classical
open Qatlib Matched

variable {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] {n m K : ℕ}

/-- Construction for observed Rvec in the retained bell pooling model. -/
def observedRvec (τ : S → S) (ω : Fin K → CohortObservation n m τ) : Fin K → ℕ :=
  fun j => (matchedSites (ω j).1 (ω j).2.1 τ).card

/-- Construction for pooled Hits in the retained bell pooling model. -/
def pooledHits (τ : S → S) (ω : Fin K → CohortObservation n m τ) : ℕ :=
  ∑ j : Fin K,hitCount (ω j).2.2

/-- Construction for pooled Matches in the retained bell pooling model. -/
def pooledMatches (τ : S → S) (ω : Fin K → CohortObservation n m τ) : ℕ :=
  ∑ j : Fin K,observedRvec τ ω j

/-- Pool hits and matches, never average the block means. -/
def pooledMeanQ (τ : S → S) (ω : Fin K → CohortObservation n m τ) : ℚ :=
  (pooledHits τ ω : ℚ)/(pooledMatches τ ω : ℚ)

/-- Construction for fresh Observation Blocks in the retained bell pooling model. -/
def freshObservationBlocks (a b c k : S → ℝ) (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1)
    (τ : Equiv.Perm S) (K : ℕ) : FinDist (Fin K → CohortObservation n m τ) :=
  cohortLaw (cohortObservationLaw a b c k hz τ τ.injective) K

/-- Construction for pooled Stratum PGF in the retained bell pooling model. -/
def pooledStratumPGF (a b c k : S → ℝ) (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1)
    (τ : Equiv.Perm S) (ρ : Fin K → ℕ) (u : ℝ) : ℝ :=
  (freshObservationBlocks (n:=n) (m:=m) a b c k hz τ K).expect
    (fun ω => if observedRvec τ ω=ρ then u^(pooledHits τ ω) else 0)

/-- Complete original `pooled_stratum_product` guarantee for `RetainedBellPooling`; all source hypotheses and output obligations are retained. -/
theorem pooled_stratum_product (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S) (ρ : Fin K → ℕ) (u : ℝ) :
    pooledStratumPGF (n:=n) (m:=m) a b c k hz τ ρ u=
      ∏ j : Fin K,observationStratumPGF (n:=n) (m:=m) a b c k hz τ (ρ j) u := by
  have hf (ω : Fin K → CohortObservation n m τ) :
      (if observedRvec τ ω=ρ then u^(pooledHits τ ω) else 0)=
        ∏ j : Fin K,if (matchedSites (ω j).1 (ω j).2.1 τ).card=ρ j then
          u^(hitCount (ω j).2.2) else 0 := by
    by_cases h : observedRvec τ ω=ρ
    · rw [ite_eq_left h,pooledHits,← Finset.prod_pow_eq_pow_sum]
      apply Finset.prod_congr rfl
      intro j _
      exact (ite_eq_left (congrFun h j)).symm
    · rw [ite_eq_right h]
      obtain ⟨j,hj⟩ : ∃ j,observedRvec τ ω j≠ρ j := by
        by_contra hh
        apply h
        funext j
        exact not_not.mp (not_exists.mp hh j)
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      exact ite_eq_right hj
  unfold pooledStratumPGF
  simp_rw [hf]
  change (∑ ω : Fin K → CohortObservation n m τ,
      (cohortObservationLaw a b c k hz τ τ.injective).probOf ω*
        ∏ j : Fin K,if (matchedSites (ω j).1 (ω j).2.1 τ).card=ρ j then
          u^(hitCount (ω j).2.2) else 0)=_
  exact (cohortObservationLaw a b c k hz τ τ.injective).expect_prod
    (fun j ω => if (matchedSites ω.1 ω.2.1 τ).card=ρ j then u^(hitCount ω.2.2) else 0)

/-- Complete original `observation_stratum_at_one` guarantee for `RetainedBellPooling`; all source hypotheses and output obligations are retained. -/
theorem observation_stratum_at_one (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S) (r : ℕ) :
    observationStratumPGF (n:=n) (m:=m) a b c k hz τ r 1=matchedCardEventMass τ n m r := by
  rw [observation_stratum_address_pgf]
  simp [matchedCardEventMass]

/-- Complete original `pooled_stratum_at_one` guarantee for `RetainedBellPooling`; all source hypotheses and output obligations are retained. -/
theorem pooled_stratum_at_one (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S) (ρ : Fin K → ℕ) :
    pooledStratumPGF (n:=n) (m:=m) a b c k hz τ ρ 1=
      ∏ j : Fin K,matchedCardEventMass τ n m (ρ j) := by
  rw [pooled_stratum_product]
  simp_rw [observation_stratum_at_one]

/-- Complete original `pooled_stratum_pgf` guarantee for `RetainedBellPooling`; all source hypotheses and output obligations are retained. -/
theorem pooled_stratum_pgf (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S) (ρ : Fin K → ℕ) (u : ℝ) :
    pooledStratumPGF (n:=n) (m:=m) a b c k hz τ ρ u=
      ∏ j : Fin K,((matchedCardEventMass τ n m (ρ j) / (Fintype.card S).choose (ρ j))*
        ∑ A ∈ (Finset.univ : Finset S).powersetCard (ρ j),
          ∏ x ∈ A,(1+bellProbability (complexSpinor a b c k x)
            (complexSpinor a b c k (τ x))*(u-1))) := by
  rw [pooled_stratum_product]
  simp_rw [observation_stratum_pgf]

omit [Fintype S] [Nonempty S] in
/-- Complete original `pooled_zero_matches` guarantee for `RetainedBellPooling`; all source hypotheses and output obligations are retained. -/
theorem pooled_zero_matches (τ : S → S) (ω : Fin K → CohortObservation n m τ)
    (h : pooledMatches τ ω=0) : pooledMeanQ τ ω=0 := by
  simp [pooledMeanQ,h]

omit [Fintype S] [Nonempty S] in
/-- Complete original `pooled_hits_from_output` guarantee for `RetainedBellPooling`; all source hypotheses and output obligations are retained. -/
theorem pooled_hits_from_output (τ : S → S) (ω : Fin K → CohortObservation n m τ)
    (h : pooledMatches τ ω≠0) :
    pooledMeanQ τ ω*(pooledMatches τ ω : ℚ)=∑ j : Fin K,observedHitsQ τ (ω j) := by
  rw [pooledMeanQ,div_mul_cancel₀ _ (by exact_mod_cast h)]
  simp only [pooledHits,Nat.cast_sum,observed_hits_cast]


omit [Fintype S] [Nonempty S] in
/-- Complete original `pooled_hits_le_matches` guarantee for `RetainedBellPooling`; all source hypotheses and output obligations are retained. -/
theorem pooled_hits_le_matches (τ : S → S) (ω : Fin K → CohortObservation n m τ) :
    pooledHits τ ω≤pooledMatches τ ω := by
  unfold pooledHits pooledMatches observedRvec hitCount
  apply Finset.sum_le_sum
  intro j _
  calc
    _ ≤ ∑ _x : matchedSites (ω j).1 (ω j).2.1 τ,(1 : ℕ) := by
      apply Finset.sum_le_sum
      intro x _
      split_ifs <;> omega
    _ = _ := by simp

omit [Fintype S] [Nonempty S] in
/-- Complete original `pooled_output_rescale` guarantee for `RetainedBellPooling`; all source hypotheses and output obligations are retained. -/
theorem pooled_output_rescale (τ : S → S) (ω : Fin K → CohortObservation n m τ) :
    (pooledMatches τ ω : ℝ)*(pooledMeanQ τ ω : ℝ)=(pooledHits τ ω : ℝ) := by
  by_cases h : pooledMatches τ ω=0
  · have hz : pooledHits τ ω=0 := by have hh := pooled_hits_le_matches τ ω; omega
    simp [h,hz]
  · have hQ : (pooledMatches τ ω : ℚ)≠0 := by exact_mod_cast h
    have hq : (pooledMatches τ ω : ℚ)*pooledMeanQ τ ω=(pooledHits τ ω : ℚ) := by
      unfold pooledMeanQ
      exact mul_div_cancel₀ _ hQ
    exact_mod_cast hq

/-- Construction for pooled Centered Stratum MGF in the retained bell pooling model. -/
def pooledCenteredStratumMGF (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S)
    (ρ : Fin K → ℕ) (pbar t : ℝ) : ℝ :=
  (freshObservationBlocks (n:=n) (m:=m) a b c k hz τ K).expect (fun ω =>
    if observedRvec τ ω=ρ then Real.exp
      (t*(pooledMatches τ ω : ℝ)*((pooledMeanQ τ ω : ℝ)-pbar)) else 0)

/-- Complete original `pooled_centered_stratum_mgf` guarantee for `RetainedBellPooling`; all source hypotheses and output obligations are retained. -/
theorem pooled_centered_stratum_mgf (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S)
    (ρ : Fin K → ℕ) (pbar t : ℝ) :
    pooledCenteredStratumMGF (n:=n) (m:=m) a b c k hz τ ρ pbar t=
      Real.exp (-t*(∑ j : Fin K,(ρ j : ℝ))*pbar)*
        pooledStratumPGF (n:=n) (m:=m) a b c k hz τ ρ (Real.exp t) := by
  unfold pooledCenteredStratumMGF pooledStratumPGF FinDist.expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : observedRvec τ ω=ρ
  · simp only [ite_eq_left h]
    have hR : (pooledMatches τ ω : ℝ)=∑ j : Fin K,(ρ j : ℝ) := by
      simp only [pooledMatches,Nat.cast_sum]
      rw [h]
    have hp : (Real.exp t)^(pooledHits τ ω)=
        Real.exp (t*(pooledMatches τ ω : ℝ)*(pooledMeanQ τ ω : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      rw [mul_assoc,pooled_output_rescale]
      ring
    have he : Real.exp (t*(pooledMatches τ ω : ℝ)*((pooledMeanQ τ ω : ℝ)-pbar))=
        Real.exp (-t*(∑ j : Fin K,(ρ j : ℝ))*pbar)*(Real.exp t)^(pooledHits τ ω) := by
      rw [hp,← Real.exp_add,← hR]
      congr 1
      ring
    rw [he]
    ring
  · simp [h]

end
end Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.pooled_stratum_product
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.observation_stratum_at_one
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.pooled_stratum_at_one
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.pooled_stratum_pgf
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.pooled_zero_matches
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.pooled_hits_from_output

#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.pooled_hits_le_matches
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.pooled_output_rescale
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.pooled_centered_stratum_mgf
