/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Retained.RetainedBellObservations
import Qatlib.Concepts.SpinorSampling.Matching.MatchedConditionalLaw

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Retained Bell PGF

Retained Bell PGF constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
noncomputable section
open scoped BigOperators Classical
open Qatlib Matched

/-- Construction for hit Count in the retained bell pgf model. -/
def hitCount {I : Type*} [Fintype I] (z : I → Bool) : ℕ :=
  ∑ i : I,if z i then 1 else 0

/-- Complete original `bool_law_pgf` guarantee for `RetainedBellPGF`; all source hypotheses and output obligations are retained. -/
theorem bool_law_pgf (p : FinDist Bool) (u : ℝ) :
    p.expect (fun b => if b then u else 1)=1+p.prob true*(u-1) := by
  have h := p.sum_one
  simp only [Fintype.sum_bool] at h
  simp only [FinDist.expect,Fintype.sum_bool,ite_true]
  change p.prob true*u+p.prob false*1=_
  nlinarith

/-- Complete original `family_hit_pgf` guarantee for `RetainedBellPGF`; all source hypotheses and output obligations are retained. -/
theorem family_hit_pgf {I : Type} [Fintype I] [DecidableEq I]
    (p : I → FinDist Bool) (u : ℝ) :
    (finiteFamilyLaw p).expect (fun z => u^(hitCount z))=
      ∏ i : I,(1+(p i).prob true*(u-1)) := by
  have hp (z : I → Bool) : u^(hitCount z)=∏ i : I,if z i then u else 1 := by
    rw [hitCount,← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_congr rfl
    intro i _
    cases z i <;> simp
  simp_rw [hp]
  rw [finite_family_expect_product p (fun (_ : I) (b : Bool) => if b then u else 1)]
  simp_rw [bool_law_pgf]

variable {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] {n m : ℕ}

omit [Fintype S] [Nonempty S] in
/-- Complete original `observed_hits_cast` guarantee for `RetainedBellPGF`; all source hypotheses and output obligations are retained. -/
theorem observed_hits_cast (τ : S → S) (ω : CohortObservation n m τ) :
    (hitCount ω.2.2 : ℚ)=observedHitsQ τ ω := by
  simp only [hitCount,observedHitsQ,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

omit [Fintype S] [Nonempty S] in
/-- Complete original `native_matched_pgf` guarantee for `RetainedBellPGF`; all source hypotheses and output obligations are retained. -/
theorem native_matched_pgf (a b c k : S → ℝ) (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1)
    (J : Fin n → S) (K : Fin m → S) (τ : S → S) (hτ : Function.Injective τ) (u : ℝ) :
    (nativeMatchedLaw a b c k hz J K τ hτ).expect (fun z => u^(hitCount z))=
      ∏ x ∈ matchedSites J K τ,(1+bellProbability (complexSpinor a b c k x)
        (complexSpinor a b c k (τ x))*(u-1)) := by
  let p := fun x : matchedSites J K τ => bellEventLaw (complexSpinor a b c k x)
    (complexSpinor a b c k (τ x)) (complex_spinor_mass a b c k hz x)
      (complex_spinor_mass a b c k hz (τ x))
  have hp : (nativeMatchedLaw a b c k hz J K τ hτ).prob=(finiteFamilyLaw p).prob := by
    funext z
    exact native_matched_hit_product a b c k hz J K τ hτ (matchedEnumeration J K τ)
      (Finset.nodup_toList _) (fun _ => by simp [matchedEnumeration]) z
  change (∑ z,(nativeMatchedLaw a b c k hz J K τ hτ).prob z*u^(hitCount z))=_
  rw [hp]
  change (finiteFamilyLaw p).expect (fun z => u^(hitCount z))=_
  rw [family_hit_pgf]
  simp only [p,bell_event_law_hit]
  exact Finset.prod_coe_sort (matchedSites J K τ) (fun x =>
    1+bellProbability (complexSpinor a b c k x) (complexSpinor a b c k (τ x))*(u-1))

/-- Keep the event mass: zero-probability strata never require conditioning. -/
def observationStratumPGF (a b c k : S → ℝ) (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1)
    (τ : Equiv.Perm S) (r : ℕ) (u : ℝ) : ℝ :=
  (cohortObservationLaw (n:=n) (m:=m) a b c k hz τ τ.injective).expect
    (fun ω => if (matchedSites ω.1 ω.2.1 τ).card=r then u^(hitCount ω.2.2) else 0)

/-- Complete original `observation_stratum_address_pgf` guarantee for `RetainedBellPGF`; all source hypotheses and output obligations are retained. -/
theorem observation_stratum_address_pgf (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S) (r : ℕ) (u : ℝ) :
    observationStratumPGF (n:=n) (m:=m) a b c k hz τ r u=
      ∑ z ∈ (Finset.univ : Finset ((Fin n → S) × (Fin m → S))).filter
        (fun z => (matchedSites z.1 z.2 τ).card=r),pairAddressMass z*
          ∏ x ∈ matchedSites z.1 z.2 τ,(1+bellProbability (complexSpinor a b c k x)
            (complexSpinor a b c k (τ x))*(u-1)) := by
  unfold observationStratumPGF FinDist.expect
  change (∑ ω : (J : Fin n → S) × (K : Fin m → S) × (matchedSites J K τ → Bool),
    (cohortLaw (uniformLaw S) n).prob ω.1*(cohortLaw (uniformLaw S) m).prob ω.2.1*
      (nativeMatchedLaw a b c k hz ω.1 ω.2.1 τ τ.injective).prob ω.2.2*
        (if (matchedSites ω.1 ω.2.1 τ).card=r then u^(hitCount ω.2.2) else 0))=_
  rw [Fintype.sum_sigma]
  simp_rw [Fintype.sum_sigma]
  rw [Finset.sum_filter,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro J _
  apply Finset.sum_congr rfl
  intro K _
  by_cases h : (matchedSites J K τ).card=r
  · simp only [ite_eq_left h]
    calc
      _ = pairAddressMass (J,K)*
          (nativeMatchedLaw a b c k hz J K τ τ.injective).expect (fun z => u^(hitCount z)) := by
        unfold pairAddressMass FinDist.expect
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        ring
      _ = _ := by rw [native_matched_pgf]
  · simp [h]

end
end Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.family_hit_pgf
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.observed_hits_cast
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.native_matched_pgf
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.observation_stratum_address_pgf
