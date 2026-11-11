/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.HighConfidenceExecution
import Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBornBridge

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Native High Confidence

Native High Confidence constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.FiniteExecution Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched
noncomputable section
open scoped BigOperators
open Qatlib
open Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge

variable {S : Type} [Fintype S] [Nonempty S] [DecidableEq S]

/-- Keep every dependent carrier while replacing only the single-record law. -/
def correlationRecordLaw (mode : CorrelationMode) (n K : ℕ) (q : FinDist (S × Bool)) :
    FinDist (CorrelationData S mode n K) :=
  match mode with
  | .zero =>
      { prob := fun _ => 1
        nonneg := fun _ => zero_le_one
        sum_one := by simp [CorrelationData] }
  | .matched => productLaw (cohortLaw q n) (cohortLaw q n)
  | .matchedMedian => cohortLaw (productLaw (cohortLaw q n) (cohortLaw q n)) K
  | .ustatisticMedian => cohortLaw (cohortLaw q n) K

/-- Construction for high Record Distribution in the native high confidence model. -/
def highRecordDistribution {d : ℕ} (p : HighConfidencePlanQ)
    (qV : Fin d → FinDist (S × Bool)) (qS : Fin 3 → FinDist (S × Bool)) :
    FinDist (HighConfidenceData S d p) :=
  independentPairLaw
    (finiteFamilyLaw (fun j => independentPairLaw
      (correlationRecordLaw p.current.mode p.current.records p.current.blocks (qV j))
      (independentPairLaw (cohortLaw (qV j) p.crossRecords)
        (targetNormLaw p.norm.mode p.norm.records p.norm.blocks))))
    (finiteFamilyLaw (fun i : Fin 3 × Fin d => correlationRecordLaw p.spinSchedule.mode
      p.spinSchedule.records p.spinSchedule.blocks (qS i.1)))

/-- Complete original `correlation_record_law_signed` guarantee for `NativeHighConfidence`; all source hypotheses and output obligations are retained. -/
theorem correlation_record_law_signed (mode : CorrelationMode) (n K : ℕ)
    (m : S → ℝ) (hm : ∀ x, |m x|≤1) :
    correlationRecordLaw mode n K (signedRecordLaw m hm)=correlationLaw mode n K m hm := by
  cases mode <;> rfl

/-- Complete original `high_record_distribution_signed` guarantee for `NativeHighConfidence`; all source hypotheses and output obligations are retained. -/
theorem high_record_distribution_signed {d : ℕ} (p : HighConfidencePlanQ)
    (mv : Fin d → S → ℝ) (hmv : ∀ j x, |mv j x|≤1)
    (ms : Fin 3 → S → ℝ) (hms : ∀ i x, |ms i x|≤1) :
    highRecordDistribution p (fun j => signedRecordLaw (mv j) (hmv j))
      (fun i => signedRecordLaw (ms i) (hms i))=highConfidenceLaw p mv hmv ms hms := by
  simp only [highRecordDistribution,correlation_record_law_signed,highConfidenceLaw,velocityRawLaw]

/-- Construction for native High Confidence Law in the native high confidence model. -/
def nativeHighConfidenceLaw (d r : ℕ) (p : HighConfidencePlanQ)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1) :
    FinDist (HighConfidenceData (Fin d → Fin (2^r)) d p) :=
  highRecordDistribution p (fun j => nativeCurrentLaw d r j a b c k hz)
    (fun i => nativeSpinLaw d r i a b c k hz)

/-- Complete original `native_high_confidence_law_eq` guarantee for `NativeHighConfidence`; all source hypotheses and output obligations are retained. -/
theorem native_high_confidence_law_eq (d r : ℕ) (p : HighConfidencePlanQ)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1) :
    nativeHighConfidenceLaw d r p a b c k hz=
      highConfidenceLaw p (spinorCurrentMean a b c k (periodicUnitShift d (2^r)))
        (spinor_current_mean_bound a b c k hz (periodicUnitShift d (2^r)))
        (pauliField a b c k) (fun i x => unit_spin_component_bound
          (pauliField a b c k) (pauli_field_unit a b c k hz) i x) := by
  simp only [nativeHighConfidenceLaw,native_current_law_eq_signed,native_spin_law_eq_signed,
    high_record_distribution_signed]

/-- Complete original `grid_cardinality` guarantee for `NativeHighConfidence`; all source hypotheses and output obligations are retained. -/
theorem grid_cardinality (d r : ℕ) : Fintype.card (Fin d → Fin (2^r))=2^(d*r) := by
  simp only [Fintype.card_fun,Fintype.card_fin,← Nat.pow_mul,Nat.mul_comm]

/-- Complete original `native_high_confidence_accuracy` guarantee for `NativeHighConfidence`; all source hypotheses and output obligations are retained. -/
theorem native_high_confidence_accuracy {d r : ℕ} (hd : 0<d)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1)
    (u : Fin d → (Fin d → Fin (2^r)) → ℚ) (α β U γ η δ : ℚ)
    (hα : 0<α) (hβ : 0≤β) (hU : 0≤U) (hγ : 0≤γ)
    (hu : ∀ j x, |u j x|≤U) (hη : 0<η) (hδ : 0<δ) (hδ1 : δ<1) :
    let p := gridHighConfidencePlanQ d r α β U γ η δ
    finiteBadMass (nativeHighConfidenceLaw d r p a b c k hz)
      (fun z => (highConfidenceOutputQ p u (fun j => periodicDoubleShift d (2^r) j) α β U γ z : ℝ))
      (implementedResidualLoss (spinorCurrentMean a b c k (periodicUnitShift d (2^r)))
        (fun j x => (u j x : ℝ)) (pauliField a b c k) (periodicDoubleShift d (2^r))
        (α : ℝ) (β : ℝ) (γ : ℝ)) ((η : ℝ)/2)≤(δ : ℝ) := by
  have hroot : Real.sqrt (Fintype.card (Fin d → Fin (2^r)) : ℝ)≤
      (((2^((d*r+1)/2) : ℕ) : ℚ) : ℝ) := by
    rw [grid_cardinality]
    simpa only [Rat.cast_natCast] using dyadic_root_bounds d r
  have ht := high_confidence_accuracy hd
    (spinorCurrentMean a b c k (periodicUnitShift d (2^r)))
    (spinor_current_mean_bound a b c k hz (periodicUnitShift d (2^r)))
    (pauliField a b c k) (pauli_field_unit a b c k hz) u (periodicDoubleShift d (2^r))
    ((2^((d*r+1)/2) : ℕ) : ℚ) α β U γ η δ hroot hα hβ hU hγ hu hη hδ hδ1
  rw [grid_cardinality] at ht
  simpa only [native_high_confidence_law_eq,gridHighConfidencePlanQ] using ht

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.correlation_record_law_signed
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.high_record_distribution_signed
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.native_high_confidence_law_eq
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.grid_cardinality
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.native_high_confidence_accuracy
