/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Retained.LowSpinExecution
import Qatlib.Concepts.SpinorSampling.Matching.NativeHighConfidence

set_option backward.isDefEq.respectTransparency false

/-!
# Native Low Spin

Native Low Spin constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.FiniteExecution Qatlib.Foundations.ProbabilityCore.Concentration Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
noncomputable section
open scoped BigOperators Classical
open Matched NativeBridge

variable {S : Type} [Fintype S] [Nonempty S] [DecidableEq S]

-- Fresh native current records and retained Bell observations, with no
/-- signed-Pauli stage. The norm groups consume only classical random sites. -/
def lowSpinRecordDistribution {d : ℕ} (p : LowSpinPlanQ)
    (qV : Fin d → FinDist (S × Bool)) (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (e : Fin d → Equiv.Perm S) :
    FinDist (LowSpinData S d e p) :=
  independentPairLaw
    (finiteFamilyLaw (fun j => independentPairLaw
      (correlationRecordLaw p.velocity.current.mode p.velocity.current.records
        p.velocity.current.blocks (qV j))
      (independentPairLaw (cohortLaw (qV j) p.velocity.crossRecords)
        (targetNormLaw p.velocity.norm.mode p.velocity.norm.records p.velocity.norm.blocks))))
    (lowSpinBellLaw a b c k hz e p.spin)

/-- Complete original `low_spin_record_distribution_signed` guarantee for `NativeLowSpin`; all source hypotheses and output obligations are retained. -/
theorem low_spin_record_distribution_signed {d : ℕ} (p : LowSpinPlanQ)
    (mv : Fin d → S → ℝ) (hmv : ∀ j x, |mv j x|≤1) (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (e : Fin d → Equiv.Perm S) :
    lowSpinRecordDistribution p (fun j => signedRecordLaw (mv j) (hmv j)) a b c k hz e=
      lowSpinLaw p mv hmv a b c k hz e := by
  simp only [lowSpinRecordDistribution,correlation_record_law_signed,lowSpinLaw,velocityRawLaw]

/-- Construction for native Low Spin Law in the native low spin model. -/
def nativeLowSpinLaw (d r : ℕ) (p : LowSpinPlanQ)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) :
    FinDist (LowSpinData (Fin d → Fin (2^r)) d (periodicDoubleShift d (2^r)) p) :=
  lowSpinRecordDistribution p (fun j => nativeCurrentLaw d r j a b c k hz)
    a b c k hz (periodicDoubleShift d (2^r))

/-- Complete original `native_low_spin_law_eq` guarantee for `NativeLowSpin`; all source hypotheses and output obligations are retained. -/
theorem native_low_spin_law_eq (d r : ℕ) (p : LowSpinPlanQ)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) :
    nativeLowSpinLaw d r p a b c k hz=
      lowSpinLaw p (spinorCurrentMean a b c k (periodicUnitShift d (2^r)))
        (spinor_current_mean_bound a b c k hz (periodicUnitShift d (2^r)))
        a b c k hz (periodicDoubleShift d (2^r)) := by
  simp only [nativeLowSpinLaw,native_current_law_eq_signed,low_spin_record_distribution_signed]

/-- Complete original `native_low_spin_accuracy` guarantee for `NativeLowSpin`; all source hypotheses and output obligations are retained. -/
theorem native_low_spin_accuracy {d r : ℕ} (hd : 0<d)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1)
    (u : Fin d → (Fin d → Fin (2^r)) → ℚ) (α β U γ η δ p₀ : ℚ)
    (hα : 0<α) (hβ : 0≤β) (hU : 0≤U) (hγ : 0≤γ)
    (hu : ∀ j x, |u j x|≤U) (hη : 0<η) (hδ : 0<δ) (hδ1 : δ<1)
    (hp : 0≤p₀) (hp1 : p₀≤1/2)
    (hmean : γ≠0 → ∀ j,bellMean a b c k (periodicDoubleShift d (2^r) j)≤(p₀ : ℝ)) :
    let p := lowSpinPlanQ (2^r) d (2^(d*r)) ((2^((d*r+1)/2) : ℕ) : ℚ) α β U γ η δ p₀
    finiteBadMass (nativeLowSpinLaw d r p a b c k hz)
      (fun z => (lowSpinOutputQ p u (periodicDoubleShift d (2^r)) α β U γ z : ℝ))
      (implementedResidualLoss (spinorCurrentMean a b c k (periodicUnitShift d (2^r)))
        (fun j x => (u j x : ℝ)) (pauliField a b c k) (periodicDoubleShift d (2^r))
        (α : ℝ) (β : ℝ) (γ : ℝ)) ((η : ℝ)/2)≤(δ : ℝ) := by
  have hroot : Real.sqrt (Fintype.card (Fin d → Fin (2^r)) : ℝ)≤
      (((2^((d*r+1)/2) : ℕ) : ℚ) : ℝ) := by
    rw [grid_cardinality]
    simpa only [Rat.cast_natCast] using dyadic_root_bounds d r
  have ht := low_spin_accuracy hd (2^r)
    (spinorCurrentMean a b c k (periodicUnitShift d (2^r)))
    (spinor_current_mean_bound a b c k hz (periodicUnitShift d (2^r)))
    a b c k hz u (periodicDoubleShift d (2^r)) ((2^((d*r+1)/2) : ℕ) : ℚ)
    α β U γ η δ p₀ hroot hα hβ hU hγ hu hη hδ hδ1 hp hp1 hmean
    (fun hside j => periodic_double_shift_small_side d (2^r) j hside)
  rw [grid_cardinality] at ht
  simpa only [native_low_spin_law_eq] using ht

end
end Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.low_spin_record_distribution_signed
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.native_low_spin_law_eq
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.native_low_spin_accuracy
