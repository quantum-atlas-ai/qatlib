/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.OriginalPromise

set_option backward.isDefEq.respectTransparency false

/-!
# Original Risk

The selected concrete null physical input of the actual six-frame shared-phase finite prior.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ComplexOrder HermitianMat
namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
open Qatlib.Foundations.FiniteStats.BornEstimator
open Qatlib.Concepts.SpinorSampling.Model
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

local instance (d N : ℕ) : DecidableEq (Fin d → Fin N) := Classical.decEq _

/-- The selected concrete null physical input of the actual six-frame shared-phase finite prior. -/
def periodicNullInput (d N : ℕ) [NeZero N] (hN : 2 ∣ N)
    (z : (Fin 3 × Bool) × ((Fin d → Fin N) → Fin 4)) :
    (Fin d → Fin N) → Bool → ℂ :=
  checkerboardSpinor (gridParity d N hN) (fun x => fourthPhase (z.2 x))
    (pauliCheckerBasis z.1.1 z.1.2)

/-- Every actual null prior input satisfies the complete original periodic promise and has zero FULL original loss. -/
theorem periodicNullInput_legal_zero (d N : ℕ) [NeZero N] (hN : 2 ∣ N)
    (j : Fin d) (lam p0 : ℝ) (hp0 : 0 ≤ p0)
    (z : (Fin 3 × Bool) × ((Fin d → Fin N) → Fin 4)) :
    OriginalPeriodicPromise d N p0 (periodicNullInput d N hN z) ∧
      originalPeriodicLoss d N lam (periodicNullInput d N hN z) = 0 := by
  exact ⟨actual_null_original_periodic_promise d N hN j p0 hp0 z.1.1 z.1.2 z.2,
    actual_null_periodic_full_original_loss_zero d N hN z.1.1 z.1.2 z.2 lam⟩

/-- A finite-output estimator uniformly biased by at most beta on ALL inputs of the original periodic promise has an attained zero-full-loss variance floor against every finite PSD-separable two-copy canonical POVM. The entire prior domination and physical gap are proved, rather than supplied as assumptions. -/
theorem original_periodic_bounded_bias_null_variance {O K : Type*} [Fintype O] [Fintype K]
    (d N : ℕ) [NeZero N] [Fact (1 < N)] (hN : 2 ∣ N) (j : Fin d)
    (P : POVM O (((Fin d → Fin N) × Fin 2) × ((Fin d → Fin N) × Fin 2)))
    (E F : O → K → HermitianMat ((Fin d → Fin N) × Fin 2) ℂ)
    (hE : ∀ o k, 0 ≤ E o k) (hF : ∀ o k, 0 ≤ F o k)
    (hsep : ∀ o, P.mats o = ∑ k, E o k ⊗ₖ F o k)
    (lam p0 beta : ℝ) (hp0 : (Real.sin (2*Real.pi/N))^2/2 ≤ p0)
    (hbeta : 0 ≤ beta)
    (hsmall : beta < lam^2*(Real.sin (2*Real.pi/N))^2/(2*Real.pi/N)^2)
    (y : O → ℝ)
    (hbias : ∀ ψ : (Fin d → Fin N) → Bool → ℂ, OriginalPeriodicPromise d N p0 ψ →
      |mean (literalFieldOutcome P ψ) y-originalPeriodicLoss d N lam ψ| ≤ beta) :
    ∃ z : (Fin 3 × Bool) × ((Fin d → Fin N) → Fin 4),
      OriginalPeriodicPromise d N p0 (periodicNullInput d N hN z) ∧
      originalPeriodicLoss d N lam (periodicNullInput d N hN z) = 0 ∧
      (lam^2*(Real.sin (2*Real.pi/N))^2/(2*Real.pi/N)^2-beta)^2/24-beta^2 ≤
        variance (literalFieldOutcome P (periodicNullInput d N hN z)) y := by
  have hOne : Complex.normSq (1 : ℂ) = 1 := by norm_num
  have hp : 0 ≤ p0 := le_trans (div_nonneg (sq_nonneg _) (by norm_num)) hp0
  have hv (x : Fin d → Fin N) : ∑ i, Complex.normSq
      (spinorFin (rotatingField d N j 1) x i) = 1 := by
    rw [spinorFin_mass, rotatingField_mass d N j 1 hOne]
  have hn (z : (Fin 3 × Bool) × ((Fin d → Fin N) → Fin 4)) :
      |mean (nullPhysicalOutcome P (gridParity d N hN) z) y| ≤ beta := by
    have hh := hbias (periodicNullInput d N hN z)
      (periodicNullInput_legal_zero d N hN j lam p0 hp z).1
    rw [(periodicNullInput_legal_zero d N hN j lam p0 hp z).2, sub_zero] at hh
    rw [literalFieldOutcome_null]
    exact hh
  have ha (ω : (Fin d → Fin N) → Fin 4) :
      |mean (physicalOutcome P (spinorFin (rotatingField d N j 1)) ω) y-
        originalPeriodicLoss d N lam (phasedRotatingField d N j 1 ω)| ≤ beta := by
    rw [literalFieldOutcome_phases]
    exact hbias _ (actual_alternative_original_periodic_promise d N j p0 hp0 1 hOne ω)
  obtain ⟨z,hz⟩ := physical_bounded_bias_null_variance P E F hE hF hsep
    (gridParity d N hN) (spinorFin (rotatingField d N j 1)) hv y
    (fun ω => originalPeriodicLoss d N lam (phasedRotatingField d N j 1 ω))
    (lam^2*(Real.sin (2*Real.pi/N))^2/(2*Real.pi/N)^2) beta hbeta hsmall hn ha
    (fun ω => phasedRotatingField_full_original_loss_gap d N j 1 hOne ω lam)
  refine ⟨z,(periodicNullInput_legal_zero d N hN j lam p0 hp z).1,
    (periodicNullInput_legal_zero d N hN j lam p0 hp z).2,?_⟩
  rw [literalFieldOutcome_null] at hz
  exact hz

/-- The same original uniform-bias contract gives an attained null mean-square-error floor at zero FULL original loss, with the actual same-input two-copy canonical measurement law. -/
theorem original_periodic_bounded_bias_null_mse {O K : Type*} [Fintype O] [Fintype K]
    (d N : ℕ) [NeZero N] [Fact (1 < N)] (hN : 2 ∣ N) (j : Fin d)
    (P : POVM O (((Fin d → Fin N) × Fin 2) × ((Fin d → Fin N) × Fin 2)))
    (E F : O → K → HermitianMat ((Fin d → Fin N) × Fin 2) ℂ)
    (hE : ∀ o k, 0 ≤ E o k) (hF : ∀ o k, 0 ≤ F o k)
    (hsep : ∀ o, P.mats o = ∑ k, E o k ⊗ₖ F o k)
    (lam p0 beta : ℝ) (hp0 : (Real.sin (2*Real.pi/N))^2/2 ≤ p0)
    (hsmall : beta < lam^2*(Real.sin (2*Real.pi/N))^2/(2*Real.pi/N)^2)
    (y : O → ℝ)
    (hbias : ∀ ψ : (Fin d → Fin N) → Bool → ℂ, OriginalPeriodicPromise d N p0 ψ →
      |mean (literalFieldOutcome P ψ) y-originalPeriodicLoss d N lam ψ| ≤ beta) :
    ∃ z : (Fin 3 × Bool) × ((Fin d → Fin N) → Fin 4),
      OriginalPeriodicPromise d N p0 (periodicNullInput d N hN z) ∧
      originalPeriodicLoss d N lam (periodicNullInput d N hN z) = 0 ∧
      (lam^2*(Real.sin (2*Real.pi/N))^2/(2*Real.pi/N)^2-beta)^2/24 ≤
        second (literalFieldOutcome P (periodicNullInput d N hN z)) y := by
  have hOne : Complex.normSq (1 : ℂ) = 1 := by norm_num
  have hp : 0 ≤ p0 := le_trans (div_nonneg (sq_nonneg _) (by norm_num)) hp0
  have hv (x : Fin d → Fin N) : ∑ i, Complex.normSq
      (spinorFin (rotatingField d N j 1) x i) = 1 := by
    rw [spinorFin_mass, rotatingField_mass d N j 1 hOne]
  have ha (ω : (Fin d → Fin N) → Fin 4) :
      |mean (physicalOutcome P (spinorFin (rotatingField d N j 1)) ω) y-
        originalPeriodicLoss d N lam (phasedRotatingField d N j 1 ω)| ≤ beta := by
    rw [literalFieldOutcome_phases]
    exact hbias _ (actual_alternative_original_periodic_promise d N j p0 hp0 1 hOne ω)
  obtain ⟨z,hz⟩ := physical_bounded_bias_null_second P E F hE hF hsep
    (gridParity d N hN) (spinorFin (rotatingField d N j 1)) hv y
    (fun ω => originalPeriodicLoss d N lam (phasedRotatingField d N j 1 ω))
    (lam^2*(Real.sin (2*Real.pi/N))^2/(2*Real.pi/N)^2) beta hsmall ha
    (fun ω => phasedRotatingField_full_original_loss_gap d N j 1 hOne ω lam)
  refine ⟨z,(periodicNullInput_legal_zero d N hN j lam p0 hp z).1,
    (periodicNullInput_legal_zero d N hN j lam p0 hp z).2,?_⟩
  rw [literalFieldOutcome_null] at hz
  exact hz

end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
