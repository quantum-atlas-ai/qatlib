/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Retained.RetainedBellJoint
import Qatlib.Concepts.StoppingCore.InterruptBridge.QuerySpaceExtensions
import Qatlib.Concepts.SpinorSampling.Matching.MatchedSiteSymmetry

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Retained Bell Observations

Retained Bell Observations constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
noncomputable section
open scoped BigOperators Classical
open Qatlib Matched

variable {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] {n m : ℕ}

/-- Construction for matched Enumeration in the retained bell observations model. -/
def matchedEnumeration (J : Fin n → S) (K : Fin m → S) (τ : S → S) :
    List (matchedSites J K τ) := Finset.univ.toList

/-- Construction for native Matched Law in the retained bell observations model. -/
def nativeMatchedLaw (a b c k : S → ℝ) (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1)
    (J : Fin n → S) (K : Fin m → S) (τ : S → S) (hτ : Function.Injective τ) :
    FinDist (matchedSites J K τ → Bool) :=
  nativePairHitLaw (matchedPhysicalFin J K τ) (matched_physical_fin_injective J K τ hτ)
    (matchedEnumeration J K τ) (Finset.nodup_toList _) (fun _ => by simp [matchedEnumeration])
    (flatCohortSpin a b c k J K)
    (fun w => complex_spinor_mass a b c k hz (flatCohortAddress J K w))

/-- Only labels and the Bell hits actually measured at selected labels occur. -/
def CohortObservation (n m : ℕ) (τ : S → S) :=
  (J : Fin n → S) × (K : Fin m → S) × (matchedSites J K τ → Bool)

/-- Typeclass instance for cohort Observation Fintype in the retained bell observations model. -/
noncomputable instance cohortObservationFintype (τ : S → S) : Fintype (CohortObservation n m τ) :=
  inferInstanceAs (Fintype ((J : Fin n → S) × (K : Fin m → S) × (matchedSites J K τ → Bool)))

/-- Construction for cohort Observation Law in the retained bell observations model. -/
def cohortObservationLaw (a b c k : S → ℝ) (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1)
    (τ : S → S) (hτ : Function.Injective τ) : FinDist (CohortObservation n m τ) where
  prob ω := (cohortLaw (uniformLaw S) n).prob ω.1*
    (cohortLaw (uniformLaw S) m).prob ω.2.1*
      (nativeMatchedLaw a b c k hz ω.1 ω.2.1 τ hτ).prob ω.2.2
  nonneg ω := mul_nonneg (mul_nonneg ((cohortLaw (uniformLaw S) n).nonneg ω.1)
    ((cohortLaw (uniformLaw S) m).nonneg ω.2.1))
    ((nativeMatchedLaw a b c k hz ω.1 ω.2.1 τ hτ).nonneg ω.2.2)
  sum_one := by
    change (∑ ω : (J : Fin n → S) × (K : Fin m → S) × (matchedSites J K τ → Bool),_)=1
    rw [Fintype.sum_sigma]
    simp_rw [Fintype.sum_sigma]
    simp_rw [← Finset.mul_sum]
    simp_rw [(nativeMatchedLaw a b c k hz _ _ τ hτ).sum_one,mul_one]
    simp_rw [← Finset.mul_sum,(cohortLaw (uniformLaw S) m).sum_one,mul_one]
    exact (cohortLaw (uniformLaw S) n).sum_one

/-- Complete original `cohort_observation_mass` guarantee for `RetainedBellObservations`; all source hypotheses and output obligations are retained. -/
theorem cohort_observation_mass (a b c k : S → ℝ) (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1)
    (τ : S → S) (hτ : Function.Injective τ) (ω : CohortObservation n m τ) :
    (cohortObservationLaw a b c k hz τ hτ).prob ω=
      (1/(Fintype.card S : ℝ))^(n+m)*
        ∏ x : matchedSites ω.1 ω.2.1 τ,(bellEventLaw (complexSpinor a b c k x)
          (complexSpinor a b c k (τ x)) (complex_spinor_mass a b c k hz x)
            (complex_spinor_mass a b c k hz (τ x))).prob (ω.2.2 x) := by
  change (cohortLaw (uniformLaw S) n).prob ω.1*(cohortLaw (uniformLaw S) m).prob ω.2.1*
    nativePairHitMass _ _ _ ω.2.2=_
  rw [uniform_cohort_address_prob,uniform_cohort_address_prob,
    native_matched_hit_product a b c k hz ω.1 ω.2.1 τ hτ
      (matchedEnumeration ω.1 ω.2.1 τ) (Finset.nodup_toList _) (fun _ => by simp [matchedEnumeration]),pow_add]

/-- No missing selected site gets a free Bernoulli outcome; R=0 returns zero. -/
def observedHitsQ (τ : S → S) (ω : CohortObservation n m τ) : ℚ :=
  ∑ x : matchedSites ω.1 ω.2.1 τ,if ω.2.2 x then 1 else 0

/-- Construction for observed Mean Q in the retained bell observations model. -/
def observedMeanQ (τ : S → S) (ω : CohortObservation n m τ) : ℚ :=
  observedHitsQ τ ω/(matchedSites ω.1 ω.2.1 τ).card

omit [Fintype S] [Nonempty S] in
/-- Complete original `observed_empty` guarantee for `RetainedBellObservations`; all source hypotheses and output obligations are retained. -/
theorem observed_empty (τ : S → S) (ω : CohortObservation n m τ)
    (h : (matchedSites ω.1 ω.2.1 τ).card=0) : observedMeanQ τ ω=0 := by
  simp [observedMeanQ,h]

omit [Fintype S] [Nonempty S] in
/-- Complete original `observation_bell_counts` guarantee for `RetainedBellObservations`; all source hypotheses and output obligations are retained. -/
theorem observation_bell_counts (τ : S → S) (ω : CohortObservation n m τ) :
    QueryCount (pairProgram (matchedPhysicalFin ω.1 ω.2.1 τ)
      (matchedEnumeration ω.1 ω.2.1 τ))=0 ∧
    GateCount (pairProgram (matchedPhysicalFin ω.1 ω.2.1 τ)
      (matchedEnumeration ω.1 ω.2.1 τ))=2*(matchedSites ω.1 ω.2.1 τ).card := by
  simpa only [matchedEnumeration,Finset.length_toList,Finset.card_univ,Fintype.card_coe] using
    pair_program_counts (matchedPhysicalFin ω.1 ω.2.1 τ) (matchedEnumeration ω.1 ω.2.1 τ)

-- The left side is the unnormalized original fresh-copy address branch,
-- evolved by the same native gates and then actually read out.
/-- Complete original `raw_capture_native_mass` guarantee for `RetainedBellObservations`; all source hypotheses and output obligations are retained. -/
theorem raw_capture_native_mass (a b c k : S → ℝ) (J : Fin n → S) (K : Fin m → S)
    (τ : S → S) (l : List (matchedSites J K τ)) (z : matchedSites J K τ → Bool) :
    (∑ σ : Reg (n+m),if pairHits (matchedPhysicalFin J K τ) σ=z then
      BornProb (Run (1 : Matrix (Reg (n+m)) (Reg (n+m)) ℂ)
        (pairProgram (matchedPhysicalFin J K τ) l)
          (capturedCohortAmplitude a b c k (flatCohortAddress J K))) σ else 0)=
      (1/(Fintype.card S : ℝ))^(n+m)*
        nativePairHitMass (matchedPhysicalFin J K τ) l (flatCohortSpin a b c k J K) z := by
  let C : ℂ := (Real.sqrt (Fintype.card S : ℝ) : ℂ)^(n+m)
  have hM : (Fintype.card S : ℝ)>0 := by exact_mod_cast Fintype.card_pos
  have hc : C≠0 := by
    apply pow_ne_zero
    exact_mod_cast (Real.sqrt_pos.mpr hM).ne'
  have hv : capturedCohortAmplitude a b c k (flatCohortAddress J K)=
      C⁻¹ • spinTensor (flatCohortSpin a b c k J K) := by
    funext σ
    change capturedCohortAmplitude a b c k (flatCohortAddress J K) σ=
      C⁻¹*spinTensor (flatCohortSpin a b c k J K) σ
    rw [← flat_cohort_from_address_projection a b c k J K σ]
    change _=C⁻¹*(C*_)
    rw [← mul_assoc,inv_mul_cancel₀ hc,one_mul]
  have hnorm : Complex.normSq (C⁻¹)=(1/(Fintype.card S : ℝ))^(n+m) := by
    simp only [C,map_inv₀,map_pow,Complex.normSq_ofReal,
      Real.mul_self_sqrt (Nat.cast_nonneg (Fintype.card S)),one_div,inv_pow]
  rw [hv,Qatlib.Concepts.StoppingCore.InterruptBridge.run_smul]
  unfold nativePairHitMass BornProb
  simp only [Pi.smul_apply,smul_eq_mul,Complex.sq_norm,map_mul,hnorm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs <;> simp


/-- Complete original `cohort_observation_is_raw_born` guarantee for `RetainedBellObservations`; all source hypotheses and output obligations are retained. -/
theorem cohort_observation_is_raw_born (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : S → S) (hτ : Function.Injective τ)
    (ω : CohortObservation n m τ) :
    (cohortObservationLaw a b c k hz τ hτ).prob ω=
      ∑ σ : Reg (n+m),if pairHits (matchedPhysicalFin ω.1 ω.2.1 τ) σ=ω.2.2 then
        BornProb (Run (1 : Matrix (Reg (n+m)) (Reg (n+m)) ℂ)
          (pairProgram (matchedPhysicalFin ω.1 ω.2.1 τ) (matchedEnumeration ω.1 ω.2.1 τ))
            (capturedCohortAmplitude a b c k (flatCohortAddress ω.1 ω.2.1))) σ else 0 := by
  change (cohortLaw (uniformLaw S) n).prob ω.1*(cohortLaw (uniformLaw S) m).prob ω.2.1*
    nativePairHitMass _ _ _ ω.2.2=_
  rw [uniform_cohort_address_prob,uniform_cohort_address_prob,← pow_add]
  exact (raw_capture_native_mass a b c k ω.1 ω.2.1 τ
    (matchedEnumeration ω.1 ω.2.1 τ) ω.2.2).symm

end
end Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.cohortObservationLaw
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.cohort_observation_mass
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.observed_empty
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.observation_bell_counts
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.raw_capture_native_mass

#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.cohort_observation_is_raw_born
