/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.SharedInput
import Qatlib.Concepts.SpinorSampling.NativeRecords.CoherentCountLift

set_option backward.isDefEq.respectTransparency false

/-!
# Coherent Input

The original supplied state and the exact coherent count lift have identical complete density entries, including the original grid normalization.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix
namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.CoherentInput
open Qatlib.Concepts.SpinorSampling.Model
open Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence
open Qatlib.Concepts.SpinorSampling.NativeRecords.SharedCopyPhases
open Qatlib.Concepts.SpinorSampling.NativeRecords.CoherentCountLift

/-- The original supplied state and the exact coherent count lift have identical complete density entries, including the original grid normalization. -/
theorem original_input_count_lift_entry {A : Type*} [Fintype A] [DecidableEq A] (Q : ℕ)
    (ψ : A → Bool → ℂ) (z w : Fin Q → A × Bool) :
    phaseMean Q (fun ω => originalSuppliedCopies ψ Q ω z*star (originalSuppliedCopies ψ Q ω w))=
      ∑ y : Fin Q → A,(1/(Fintype.card A : ℂ)^Q)*
        (fullOrbitMatrix y*ᵥ(fun t => copyAmplitude ψ Q (fun j => (y j,t j)))) z*
        star ((fullOrbitMatrix y*ᵥ(fun t => copyAmplitude ψ Q (fun j => (y j,t j)))) w) := by
  let κ : ℂ := Real.sqrt (Fintype.card A : ℝ)
  have hκs : star κ=κ := by simp [κ]
  have hκsq : κ^2=(Fintype.card A : ℂ) := by
    dsimp only [κ]
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Fintype.card A))
  have hpow : κ^Q*star (κ^Q)=(Fintype.card A : ℂ)^Q := by
    rw [star_pow,hκs,←mul_pow,←pow_two,hκsq]
  have hv (x : Fin Q → A × Bool) :
      (∏ j,suppliedSpinState (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ) (x j).2 (x j).1)=
        copyAmplitude ψ Q x/κ^Q := by
    simp only [suppliedSpinState,complexSpinor_parts,copyAmplitude,Finset.prod_div_distrib,Fin.prod_const]
    rfl
  have h := original_shared_phase_density_entry ψ Q z w
  rw [hv z,hv w] at h
  have hn :
      (if (∀ a,multiplicity (fun j => (z j).1) a=multiplicity (fun j => (w j).1) a) then (1 : ℂ) else 0)*
        (copyAmplitude ψ Q z/κ^Q)*star (copyAmplitude ψ Q w/κ^Q)=
      (1/(Fintype.card A : ℂ)^Q)*
        (if (∀ a,multiplicity (fun j => (z j).1) a=multiplicity (fun j => (w j).1) a) then 1 else 0)*
          copyAmplitude ψ Q z*star (copyAmplitude ψ Q w) := by
    rw [star_div₀,mul_assoc,div_mul_div_comm,hpow]
    ring
  rw [hn] at h
  exact h.trans (fullOrbitMatrix_average_entry ψ (1/(Fintype.card A : ℂ)^Q) z w).symm

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.CoherentInput
