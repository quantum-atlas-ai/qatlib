/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.PhysicalRisk
import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.LegalNull
import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.PhasedAlternative

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Original Promise

The fixed Bool-to-Fin spin relabelling preserves the literal physical spin amplitudes.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ComplexOrder HermitianMat
namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
open Qatlib.Concepts.SpinorSampling.Model
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

/-- The fixed Bool-to-Fin spin relabelling preserves the literal physical spin amplitudes. -/
def spinorFin {A : Type*} (ψ : A → Bool → ℂ) (x : A) (i : Fin 2) : ℂ :=
  ψ x (boolEquivFin2.symm i)

/-- The fixed spin relabelling preserves the source's pointwise mass exactly. -/
theorem spinorFin_mass {A : Type*} (ψ : A → Bool → ℂ) (x : A) :
    (∑ i : Fin 2, Complex.normSq (spinorFin ψ x i)) = qubitMass (ψ x) := by
  have h := Equiv.sum_comp boolEquivFin2
    (fun i : Fin 2 => Complex.normSq (ψ x (boolEquivFin2.symm i)))
  simpa only [spinorFin, Equiv.symm_apply_apply, Fintype.sum_bool, qubitMass, add_comm] using h.symm

/-- The actual complete-address supplied vector of a physical Bool-spin field, with its original 1/sqrt(M) factor. -/
def literalFieldState {A : Type*} [Fintype A] (ψ : A → Bool → ℂ)
    (z : A × Fin 2) : ℂ := ψ z.1 (boolEquivFin2.symm z.2)/(Real.sqrt (Fintype.card A : ℝ) : ℂ)

/-- This vector is exactly the original suppliedSpinState in fixed spin coordinates, without a new physical encoding. -/
theorem literalFieldState_original {A : Type*} [Fintype A] (ψ : A → Bool → ℂ)
    (z : A × Fin 2) :
    literalFieldState ψ z = suppliedSpinState (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ)
      (boolEquivFin2.symm z.2) z.1 := by
  rw [suppliedSpinState, complexSpinor_parts]
  rfl

/-- The actual finite canonical measurement law on two identical complete supplied copies of a fixed physical input. -/
def literalFieldOutcome {A O : Type*} [Fintype A] [Fintype O]
    (P : POVM O ((A × Fin 2) × (A × Fin 2))) (ψ : A → Bool → ℂ) (o : O) : ℝ :=
  effectWeight (P.mats o) (pairedState (literalFieldState ψ))

/-- Sampling one hidden phase assignment and supplying the resulting physical field twice agrees exactly with the actual prior-law implementation. -/
theorem literalFieldOutcome_phases {A O : Type*} [Fintype A] [Fintype O]
    (P : POVM O ((A × Fin 2) × (A × Fin 2))) (ψ : A → Bool → ℂ)
    (ω : A → Fin 4) :
    physicalOutcome P (spinorFin ψ) ω =
      literalFieldOutcome P (fun x s => fourthPhase (ω x)*ψ x s) := rfl

/-- Every physical null prior input produces exactly its literal canonical complete-address outcome law. -/
theorem literalFieldOutcome_null {A O : Type*} [Fintype A] [Fintype O]
    (P : POVM O ((A × Fin 2) × (A × Fin 2))) (parity : A → Bool)
    (z : (Fin 3 × Bool) × (A → Fin 4)) :
    nullPhysicalOutcome P parity z = literalFieldOutcome P
      (checkerboardSpinor parity (fun x => fourthPhase (z.2 x))
        (pauliCheckerBasis z.1.1 z.1.2)) := by
  have hs : literalFieldState (checkerboardSpinor parity (fun x => fourthPhase (z.2 x))
      (pauliCheckerBasis z.1.1 z.1.2)) =
      phasedFieldState (nullField parity z.1.1 z.1.2) z.2 := by
    funext p
    simp only [literalFieldState, checkerboardSpinor, pauliCheckerBasis, phasedFieldState,
      nullField, Equiv.apply_symm_apply]
  unfold nullPhysicalOutcome physicalOutcome literalFieldOutcome
  rw [hs]

/-- The original periodic physical promise uses pointwise unit spinors, zero global source Bloch means and the actual public double-shift Bell means. -/
def OriginalPeriodicPromise (d N : ℕ) [NeZero N] (p0 : ℝ)
    (ψ : (Fin d → Fin N) → Bool → ℂ) : Prop :=
  (∀ x, qubitMass (ψ x) = 1) ∧
    (∀ i, siteMean (fun x => qubitBloch (ψ x) i) = 0) ∧
      ∀ k : Fin d, bellMean (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ)
        (periodicDoubleShift d N k) ≤ p0

/-- The full original periodic loss at kappa=1 and zero target current, with the actual physical mesh size. -/
def originalPeriodicLoss (d N : ℕ) [NeZero N] (lam : ℝ)
    (ψ : (Fin d → Fin N) → Bool → ℂ) : ℝ :=
  spinorDiscreteLoss (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ)
    (fun _ _ => 0) (periodicUnitShift d N) (2*Real.pi/N) 1 lam

/-- Every individual physical null input obeys all original periodic promises, including the public Bell means, before any averaging over hidden inputs. -/
theorem actual_null_original_periodic_promise (d N : ℕ) [NeZero N] (hN : 2 ∣ N)
    (j : Fin d) (p0 : ℝ) (hp0 : 0 ≤ p0) (axis : Fin 3) (sign : Bool)
    (ω : (Fin d → Fin N) → Fin 4) :
    OriginalPeriodicPromise d N p0 (checkerboardSpinor (gridParity d N hN)
      (fun x => fourthPhase (ω x)) (pauliCheckerBasis axis sign)) := by
  constructor
  · intro x
    exact checkerboard_normalized _ _ _ (fun x => fourthPhase_normSq (ω x))
      (pauliCheckerBasis_mass axis sign) x
  constructor
  · intro i
    unfold siteMean
    rw [actual_null_periodic_global_bloch_zero d N hN j axis sign ω i, zero_div]
  · intro k
    have hb : bellMean
        (real0 (checkerboardSpinor (gridParity d N hN) (fun x => fourthPhase (ω x))
          (pauliCheckerBasis axis sign)))
        (imag0 (checkerboardSpinor (gridParity d N hN) (fun x => fourthPhase (ω x))
          (pauliCheckerBasis axis sign)))
        (real1 (checkerboardSpinor (gridParity d N hN) (fun x => fourthPhase (ω x))
          (pauliCheckerBasis axis sign)))
        (imag1 (checkerboardSpinor (gridParity d N hN) (fun x => fourthPhase (ω x))
          (pauliCheckerBasis axis sign))) (periodicDoubleShift d N k) = 0 := by
      unfold bellMean
      simp_rw [complexSpinor_parts, actual_null_periodic_double_bell_zero d N hN axis sign ω k]
      exact site_mean_const 0
    rw [hb]
    exact hp0

/-- Every individual actual slow-rotation alternative obeys the original public promise whenever the exact sin²(h)/2 threshold is allowed. -/
theorem actual_alternative_original_periodic_promise (d N : ℕ) [NeZero N] [Fact (1 < N)]
    (j : Fin d) (p0 : ℝ) (hp0 : (Real.sin (2*Real.pi/N))^2/2 ≤ p0)
    (α : ℂ) (hα : Complex.normSq α = 1) (ω : (Fin d → Fin N) → Fin 4) :
    OriginalPeriodicPromise d N p0 (phasedRotatingField d N j α ω) := by
  constructor
  · intro x
    change qubitMass (fun s => fourthPhase (ω x)*rotatingField d N j α x s) = 1
    rw [qubitMass_scale, fourthPhase_normSq, rotatingField_mass d N j α hα, one_mul]
  constructor
  · intro i
    unfold siteMean
    rw [phasedRotatingField_global_bloch_zero d N j α hα ω i, zero_div]
  · intro k
    rw [phasedRotatingField_bellMean d N j k α hα ω]
    split_ifs
    · exact hp0
    · exact le_trans (div_nonneg (sq_nonneg _) (by norm_num)) hp0

end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
