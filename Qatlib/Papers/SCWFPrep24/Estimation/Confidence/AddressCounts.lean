/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.CopyMultiplicities
import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.SharedInput
import Qatlib.Concepts.SpinorSampling.Retained.RetainedSpinCohorts

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Address Counts

Every shared phase realization preserves the pointwise physical mass before any averaging.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ComplexOrder
namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.AddressCounts
open Qatlib.Concepts.SpinorSampling.Model
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
open Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence
open Qatlib.Concepts.SpinorSampling.NativeRecords.SharedCopyPhases

/-- Every shared phase realization preserves the pointwise physical mass before any averaging. -/
theorem sharedPhaseField_mass {A : Type*} (ψ : A → Bool → ℂ)
    (hψ : ∀ a,qubitMass (ψ a)=1) (Q : ℕ) (ω : A → Fin (Q+1)) (a : A) :
    qubitMass (sharedPhaseField ψ Q ω a)=1 := by
  change qubitMass (fun s => rootPhase Q (ω a)*ψ a s)=1
  rw [qubitMass_scale,Complex.normSq_eq_norm_sq,rootPhase_norm,one_pow,hψ a,one_mul]

/-- The original full quantum input has exactly the actual uniform iid address mass, using the existing retained-cohort identity. -/
theorem original_copy_address_mass {A : Type*} [Fintype A] [Nonempty A]
    (ψ : A → Bool → ℂ) (hψ : ∀ a,qubitMass (ψ a)=1)
    (Q : ℕ) (ω : A → Fin (Q+1)) (x : Fin Q → A) :
    (∑ s : Fin Q → Bool,Complex.normSq (originalSuppliedCopies ψ Q ω
      (fun j => (x j,s j))))=1/(Fintype.card A : ℝ)^Q := by
  have hp (a : A) : (real0 (sharedPhaseField ψ Q ω) a)^2+
      (imag0 (sharedPhaseField ψ Q ω) a)^2+(real1 (sharedPhaseField ψ Q ω) a)^2+
        (imag1 (sharedPhaseField ψ Q ω) a)^2=1 := by
    simpa only [qubitMass,real0,imag0,real1,imag1,Complex.normSq_apply,pow_two,
      add_comm,add_left_comm,add_assoc] using sharedPhaseField_mass ψ hψ Q ω a
  have h := cohort_address_mass (real0 (sharedPhaseField ψ Q ω)) (imag0 (sharedPhaseField ψ Q ω))
    (real1 (sharedPhaseField ψ Q ω)) (imag1 (sharedPhaseField ψ Q ω)) hp x
  simpa only [capturedCohortAmplitude,originalSuppliedCopies,one_div_pow] using h

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.AddressCounts

namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.AddressCounts
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence
open Qatlib.Concepts.SpinorSampling.Matching.CopyMultiplicities

/-- The actual physical address marginal is the same product law used for the multinomial count calculation. -/
theorem original_copy_address_probability {A : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    (ψ : A → Bool → ℂ) (hψ : ∀ a,qubitMass (ψ a)=1)
    (Q : ℕ) (ω : A → Fin (Q+1)) (x : Fin Q → A) :
    (∑ s : Fin Q → Bool,Complex.normSq (originalSuppliedCopies ψ Q ω
      (fun j => (x j,s j))))=(uniformCopyLaw A Q).prob x := by
  rw [original_copy_address_mass ψ hψ Q ω x,uniformCopyLaw_prob]

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.AddressCounts
