/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.NativeRecords.SharedCopyPhases
import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.Checkerboard

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Shared phases on the original complete supplied input

Every tensor factor calls the existing suppliedSpinState with its original
1/sqrt(M) amplitude and the same hidden local phase field. The assumptions
here are exactly pointwise unit spinors. These are input-state and phase-block
identities; the full original loss promise and confidence lower bound follow
only after the remaining count lifting and loss separation are proved.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ComplexOrder
namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence
open Qatlib.Concepts.SpinorSampling.Model
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
open Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
open Qatlib.Concepts.SpinorSampling.NativeRecords.SharedCopyPhases

/-- One hidden local phase field is chosen for the original physical spinor and reused across every copy. -/
def sharedPhaseField {A : Type*} (ψ : A → Bool → ℂ) (Q : ℕ)
    (ω : A → Fin (Q+1)) (a : A) (s : Bool) : ℂ := rootPhase Q (ω a)*ψ a s

/-- The original suppliedSpinState keeps its exact normalization under the common local phase factor. -/
theorem original_supplied_phase_factor {A : Type*} [Fintype A]
    (ψ : A → Bool → ℂ) (Q : ℕ) (ω : A → Fin (Q+1)) (a : A) (s : Bool) :
    suppliedSpinState (real0 (sharedPhaseField ψ Q ω)) (imag0 (sharedPhaseField ψ Q ω))
      (real1 (sharedPhaseField ψ Q ω)) (imag1 (sharedPhaseField ψ Q ω)) s a=
        rootPhase Q (ω a)*suppliedSpinState (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ) s a := by
  simp only [suppliedSpinState,complexSpinor_parts,sharedPhaseField]
  ring

/-- The original Q-copy input retains one fixed physical spinor and phase field in all complete address registers. -/
def originalSuppliedCopies {A : Type*} [Fintype A] (ψ : A → Bool → ℂ) (Q : ℕ)
    (ω : A → Fin (Q+1)) (x : Fin Q → A × Bool) : ℂ :=
  ∏ j,suppliedSpinState (real0 (sharedPhaseField ψ Q ω)) (imag0 (sharedPhaseField ψ Q ω))
    (real1 (sharedPhaseField ψ Q ω)) (imag1 (sharedPhaseField ψ Q ω)) (x j).2 (x j).1

/-- The complete original supplied-copy amplitude is literally the common-phase tensor vector. -/
theorem originalSuppliedCopies_eq {A : Type*} [Fintype A]
    (ψ : A → Bool → ℂ) (Q : ℕ) (ω : A → Fin (Q+1)) :
    originalSuppliedCopies ψ Q ω=sharedPhasedCopyAmplitude
      (fun a s => suppliedSpinState (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ) s a) Q ω := by
  funext x
  simp only [originalSuppliedCopies,original_supplied_phase_factor,sharedPhasedCopyAmplitude]

/-- Pointwise unit spinors internally give normalized original Q-copy physical inputs for every shared phase realization. -/
theorem originalSuppliedCopies_normalized {A : Type*} [Fintype A] [Nonempty A]
    (ψ : A → Bool → ℂ) (hψ : ∀ a,qubitMass (ψ a)=1)
    (Q : ℕ) (ω : A → Fin (Q+1)) : Normalized (originalSuppliedCopies ψ Q ω) := by
  have hp (a : A) : (real0 ψ a)^2+(imag0 ψ a)^2+(real1 ψ a)^2+(imag1 ψ a)^2=1 := by
    simpa only [qubitMass,real0,imag0,real1,imag1,Complex.normSq_apply,pow_two,
      add_comm,add_left_comm,add_assoc] using hψ a
  have hn := supplied_spin_state_normalized (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ) hp
  rw [originalSuppliedCopies_eq]
  exact sharedPhasedCopyAmplitude_normalized _ hn Q ω

/-- The actual complete original Q-copy density has precisely the shared-phase multiplicity blocks, with all spin and address amplitudes preserved. -/
theorem original_shared_phase_density_entry {A : Type*} [Fintype A] [DecidableEq A]
    (ψ : A → Bool → ℂ) (Q : ℕ) (x y : Fin Q → A × Bool) :
    phaseMean Q (fun ω => originalSuppliedCopies ψ Q ω x*star (originalSuppliedCopies ψ Q ω y))=
      (if (∀ a,multiplicity (fun j => (x j).1) a=multiplicity (fun j => (y j).1) a)
        then 1 else 0)*
      (∏ j,suppliedSpinState (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ) (x j).2 (x j).1)*
      star (∏ j,suppliedSpinState (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ) (y j).2 (y j).1) := by
  simp only [originalSuppliedCopies_eq]
  exact shared_phase_density_entry
    (fun a s => suppliedSpinState (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ) s a) Q x y

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence
