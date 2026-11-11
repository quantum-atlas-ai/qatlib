/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.PaidPhysicalReceipt
import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.DyadicRisk

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Paid physical finite-output comparator and original null-risk separation

The generated public rational coefficient, complete physical observation law,
fixed physical memory boundary and same-record resources are consumed together.
The lower comparison retains arbitrary full-address PSD-separable effects.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ComplexOrder HermitianMat
namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
open Qatlib
open Qatlib.Concepts.SpinorSampling.Model
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
open Qatlib.Foundations.FiniteStats.BornEstimator
open Qatlib.Concepts.SpinorSampling.Retained.PrefixSupply
open Qatlib.Concepts.SpinorSampling.FiniteExecution.MeasuredReset
local instance (d N : ℕ) : DecidableEq (Fin d → Fin N) := Classical.decEq _

/-- The actual computed finite plan and its same physical record law give the whole original loss, exact null variance and complete two-copy physical receipts. -/
theorem physical_pair_estimator_exists (d r : ℕ) (lam beta : ℚ)
    (hd : d=2 ∨ d=3) (hr : 2≤r) (hlam : 0<lam) (hbeta : 0<beta) :
    ∃ c,paidPairPlanQ d r lam beta=some c ∧
      (∀ (ψ : PairGrid d r → Bool → ℂ) (hψ : ∀ x,qubitMass (ψ x)=1),
        |(physicalPairLaw d r ψ hψ).expect (fun z => (physicalPairOutputQ d r lam c z : ℝ))-
          spinorDiscreteLoss (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ)
            (fun _ _ => 0) (periodicUnitShift d (2^r)) (2*Real.pi/((2^r : ℕ) : ℝ)) 1 (lam : ℝ)|≤(beta : ℝ)) ∧
      (∀ (ψ : PairGrid d r → Bool → ℂ) (hψ : ∀ x,qubitMass (ψ x)=1),
        spinorDiscreteLoss (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ)
          (fun _ _ => 0) (periodicUnitShift d (2^r)) (2*Real.pi/((2^r : ℕ) : ℝ)) 1 (lam : ℝ)=0 →
        (physicalPairLaw d r ψ hψ).expect (fun z => (physicalPairOutputQ d r lam c z : ℝ))=0 ∧
        (physicalPairLaw d r ψ hψ).variance (fun z => (physicalPairOutputQ d r lam c z : ℝ))=
          8*(d : ℝ)*(paidGridSize d r : ℝ)*(c.value : ℝ)^2 ∧
        (physicalPairLaw d r ψ hψ).variance (fun z => (physicalPairOutputQ d r lam c z : ℝ))≤
          32*(d : ℝ)*(paidGridSize d r : ℝ)/(2*Real.pi/((2^r : ℕ) : ℝ))^4) ∧
      (∀ (ψ : PairGrid d r → Bool → ℂ) (hψ : ∀ x,qubitMass (ψ x)=1)
        (z : (Bool × Fin 4) × PhysicalPairObservation d r),
        (physicalPairLaw d r ψ hψ).prob z≠0 →
          ∃ t,physicalPairSelectedTrace d r z=some t ∧ pairTraceBudget d r t) ∧
      (∀ (ψ : PairGrid d r → Bool → ℂ) (hψ : ∀ x,qubitMass (ψ x)=1),
        (physicalPairLaw d r ψ hψ).expect (physicalCaptureFee d r)=3*(d : ℝ)/4 ∧
        (physicalPairLaw d r ψ hψ).expect (physicalTestFee d r)=
          (d : ℝ)/(4*(paidGridSize d r : ℝ))) ∧
      (∀ (ψ : PairGrid d r → Bool → ℂ) (x : PairGrid d r),
        AtMostOnePhysicalSpin (canonicalFirstStorageBoundary d r ψ x)) ∧
      (∀ (n : ℕ) (φ : QState (Reg n)) (out : Reg n),
        AtMostOnePhysicalSpin
          (Run (1 : Matrix (Reg n) (Reg n) ℂ) (measuredClearProgram (allPhysicalWires n) out)
            (ApplyGate (measuredMaskMatrix (allPhysicalWires n) out) φ))) ∧
      c.bits≤2*max 16 (inverseSquareBitsQ (2^r) (paidPairEnvelopeQ d r lam) beta) := by
  obtain ⟨c,hc⟩ := paidPairPlanQ_total d r lam beta hd hr hlam hbeta
  refine ⟨c,hc,?_,?_,?_,?_,?_,?_,?_⟩
  · intro ψ hψ
    exact physicalPairOutputQ_bias d r lam beta c hc ψ hψ
  · intro ψ hψ hz
    exact physicalPairOutputQ_null_variance d r lam beta c hc ψ hψ hz
  · intro ψ hψ z hz
    exact physicalPairLaw_selected_trace_budget d r hr ψ hψ z hz
  · intro ψ hψ
    exact ⟨physicalPairLaw_expected_capture_gates d r hd ψ hψ,
      physicalPairLaw_expected_Bell_gates d r hd ψ hψ⟩
  · exact canonicalFirstStorageBoundary_one_spin d r
  · exact fullReadoutMask_zero_memory
  · exact inverseSquareGeneratedQ_bits _ _ _ _ (paidPairPlanQ_spec d r lam beta c hc).2

/-- In the original explicit public numerical separation regime, every uniformly bounded-bias finite-output PSD-separable two-copy estimator has strictly larger variance than the actual finite-output retained-spin protocol at a legal zero-full-loss input. -/
theorem physical_pair_strict_null_risk_separation {O K : Type*} [Fintype O] [Fintype K]
    (d r : ℕ) (hd : d=2 ∨ d=3) (hr : 2≤r)
    (P : POVM O (((Fin d → Fin (2^r)) × Fin 2) × ((Fin d → Fin (2^r)) × Fin 2)))
    (E F : O → K → HermitianMat ((Fin d → Fin (2^r)) × Fin 2) ℂ)
    (hE : ∀ o k,0≤E o k) (hF : ∀ o k,0≤F o k)
    (hsep : ∀ o,P.mats o=∑ k,E o k ⊗ₖ F o k)
    (lam beta : ℚ) (hlam : 0<lam) (hbeta : 0<beta) (p0 : ℝ)
    (hp0 : (Real.sin (2*Real.pi/(2^r : ℕ)))^2/2≤p0)
    (hseparate : 32*(d : ℝ)*(paidGridSize d r : ℝ)/(2*Real.pi/(2^r : ℕ))^4 <
      ((lam : ℝ)^2*(Real.sin (2*Real.pi/(2^r : ℕ)))^2/(2*Real.pi/(2^r : ℕ))^2-(beta : ℝ))^2/24-
        (beta : ℝ)^2)
    (y : O → ℝ)
    (hbias : ∀ ψ : PairGrid d r → Bool → ℂ,
      OriginalPeriodicPromise d (2^r) p0 ψ →
      |mean (literalFieldOutcome P ψ) y-originalPeriodicLoss d (2^r) (lam : ℝ) ψ|≤(beta : ℝ)) :
    ∃ c,paidPairPlanQ d r lam beta=some c ∧
      ∃ ψ : PairGrid d r → Bool → ℂ, ∃ hp : OriginalPeriodicPromise d (2^r) p0 ψ,
        originalPeriodicLoss d (2^r) (lam : ℝ) ψ=0 ∧
        (physicalPairLaw d r ψ hp.1).variance
          (fun z => (physicalPairOutputQ d r lam c z : ℝ)) < variance (literalFieldOutcome P ψ) y := by
  have hS := original_periodic_gap_pos (2^r) (original_dyadic_mesh_parameters r hr).1
    (lam : ℝ) (by exact_mod_cast hlam)
  have hb : (0 : ℝ)<(beta : ℝ) := by exact_mod_cast hbeta
  have hsmall : (beta : ℝ)<(lam : ℝ)^2*(Real.sin (2*Real.pi/(2^r : ℕ)))^2/
      (2*Real.pi/(2^r : ℕ))^2 := by
    by_contra h
    have hl := le_of_not_gt h
    have hu : (0 : ℝ)≤32*(d : ℝ)*(paidGridSize d r : ℝ)/(2*Real.pi/(2^r : ℕ))^4 := by positivity
    have hm := mul_nonneg (le_of_lt hS) (sub_nonneg.mpr hl)
    nlinarith [sq_nonneg ((lam : ℝ)^2*(Real.sin (2*Real.pi/(2^r : ℕ)))^2/
      (2*Real.pi/(2^r : ℕ))^2),sq_nonneg (beta : ℝ)]
  obtain ⟨c,hc⟩ := paidPairPlanQ_total d r lam beta hd hr hlam hbeta
  obtain ⟨ψ,hp,hzero,hfloor⟩ := original_dyadic_bounded_bias_null_variance d r hd hr
    P E F hE hF hsep (lam : ℝ) p0 (beta : ℝ) hp0 (le_of_lt hb) hsmall y hbias
  have hv := (physicalPairOutputQ_null_variance d r lam beta c hc ψ hp.1 hzero).2.2
  exact ⟨c,hc,ψ,hp,hzero,lt_of_le_of_lt hv (lt_of_lt_of_le hseparate hfloor)⟩

end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
