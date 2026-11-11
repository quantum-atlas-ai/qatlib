/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.NativeHighConfidence
import Qatlib.Concepts.SpinorSampling.FiniteExecution.ParameterEncoding

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# High Confidence Original

High Confidence Original constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.FiniteExecution Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched
noncomputable section
open scoped BigOperators
open Qatlib
open Qatlib.Concepts.SpinorSampling.FiniteExecution.ParameterEncoding

/-- Complete original `generated_high_confidence_original_accuracy` guarantee for `HighConfidenceOriginal`; all source hypotheses and output obligations are retained. -/
theorem generated_high_confidence_original_accuracy {d r : ℕ}
    (κ lam U η δ eb : ℚ) (coef : CoefficientCandidateQ)
    (hc : coefficientsGeneratedQ d (2^r) κ lam U η=some coef)
    (hd : 0<d) (hκ : 0<κ) (hU : 0≤U) (hη : 0<η) (hδ : 0<δ) (hδ1 : δ<1)
    (heb0 : 0≤eb) (heb : eb≤coef.maxTargetError)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1)
    (u : Fin d → (Fin d → Fin (2^r)) → ℝ)
    (û : Fin d → (Fin d → Fin (2^r)) → ℚ)
    (hu : ∀ j x, |u j x|≤(U : ℝ)) (htarget : ∀ j x, |(û j x : ℝ)-u j x|≤(eb : ℝ)) :
    let p := gridHighConfidencePlanQ d r coef.alpha coef.beta (U+eb) coef.gamma η δ
    finiteBadMass (nativeHighConfidenceLaw d r p a b c k hz)
      (fun z => (highConfidenceOutputQ p û (fun j => periodicDoubleShift d (2^r) j)
        coef.alpha coef.beta (U+eb) coef.gamma z : ℝ))
      (spinorDiscreteLoss a b c k u (periodicUnitShift d (2^r))
        (2*Real.pi/((2^r : ℕ) : ℝ)) (κ : ℝ) (lam : ℝ)) (η : ℝ)≤(δ : ℝ) := by
  let e := periodicUnitShift d (2^r)
  let e2 := periodicDoubleShift d (2^r)
  let mv := spinorCurrentMean a b c k e
  let ms := pauliField a b c k
  let p := gridHighConfidencePlanQ d r coef.alpha coef.beta (U+eb) coef.gamma η δ
  let law := nativeHighConfidenceLaw d r p a b c k hz
  let F := fun z : HighConfidenceData (Fin d → Fin (2^r)) d p =>
    (highConfidenceOutputQ p û (fun j => e2 j) coef.alpha coef.beta (U+eb) coef.gamma z : ℝ)
  let L1 := implementedResidualLoss mv (fun j x => (û j x : ℝ)) ms e2
    (coef.alpha : ℝ) (coef.beta : ℝ) (coef.gamma : ℝ)
  let h : ℝ := 2*Real.pi/((2^r : ℕ) : ℝ)
  let C : ℝ := ((2^r : ℕ) : ℝ)/6+(1/(κ : ℝ))*(U : ℝ)
  have hv := coefficients_generated_valid d (2^r) κ lam U η coef hc
  have hl := coefficients_generated_legal d (2^r) κ lam U η coef hd (by positivity) hκ hU hη hc
  have hu' (j : Fin d) (x : Fin d → Fin (2^r)) : |û j x|≤U+eb := by
    have hh := rounded_target_abs_bound _ _ _ _ (hu j x) (htarget j x)
    exact_mod_cast hh
  have hstat : finiteBadMass law F L1 ((η : ℝ)/2)≤(δ : ℝ) :=
    native_high_confidence_accuracy hd a b c k hz û coef.alpha coef.beta (U+eb) coef.gamma η δ
      hl.1 hl.2.1.le (add_nonneg hU heb0) hl.2.2.1 hu' hη hδ hδ1
  have hh : 0<h := by dsimp [h]; positivity
  have hκR : (0 : ℝ)<κ := Rat.cast_pos.mpr hκ
  have hηR : (0 : ℝ)<η := Rat.cast_pos.mpr hη
  have hUR : (0 : ℝ)≤U := Rat.cast_nonneg.mpr hU
  have hebR : (0 : ℝ)≤eb := Rat.cast_nonneg.mpr heb0
  have hC0 : 0≤C := by dsimp [C]; positivity
  have hC : 1/h+(1/(κ : ℝ))*(U : ℝ)≤C := by
    dsimp [C,h]
    linarith [inverse_mesh_rational_upper (2^r)]
  have hEB : (eb : ℝ)≤(κ : ℝ)*precisionStep d C (η : ℝ) := by
    rw [← hv.2.2.2.1]
    exact Rat.cast_le.mpr heb
  have hb := sufficient_bias_budget d C (κ : ℝ) (η : ℝ)
    (coef.alphaError : ℝ) (eb : ℝ) (coef.gammaError : ℝ) hd hC0 hκR hηR
    ((abs_nonneg _).trans hv.1) hebR hv.2.2.2.2.1 hEB hv.2.2.2.2.2
  have hbias : |L1-spinorDiscreteLoss a b c k u e h (κ : ℝ) (lam : ℝ)|≤(η : ℝ)/16 := by
    rw [spinor_discrete_loss_eq a b c k hz u e h (κ : ℝ) (lam : ℝ) hh.ne' hκR.ne']
    have hid : (fun j => (e j).trans (e j))=e2 := by
      funext j
      exact periodic_unit_shift_square d (2^r) j
    rw [hid]
    have ht := implemented_loss_bias_bound mv u (fun j x => (û j x : ℝ))
      (1/h) (coef.alpha : ℝ) (1/(κ : ℝ)) ((lam : ℝ)^2/(2*h^2)) (coef.gamma : ℝ)
      (U : ℝ) C (coef.alphaError : ℝ) (eb : ℝ) (coef.gammaError : ℝ)
      (spinor_current_mean_bound a b c k hz e) hu htarget ms (pauli_field_unit a b c k hz) e2
      (by positivity) (by positivity) hv.1 hv.2.1 hC
    change |implementedResidualLoss mv (fun j x => (û j x : ℝ)) ms e2
      (coef.alpha : ℝ) (coef.beta : ℝ) (coef.gamma : ℝ)-_|≤_
    rw [hv.2.2.1]
    exact ht.trans hb
  change finiteBadMass law F (spinorDiscreteLoss a b c k u e h (κ : ℝ) (lam : ℝ)) (η : ℝ)≤(δ : ℝ)
  exact (finite_bad_mass_change_center law F _ L1 ((η : ℝ)/2) (η : ℝ)
    (by linarith [hbias])).trans hstat

/-- Complete original `enclosed_high_confidence_original_accuracy` guarantee for `HighConfidenceOriginal`; all source hypotheses and output obligations are retained. -/
theorem enclosed_high_confidence_original_accuracy {d r : ℕ} (box : PhysicalBoxQ) (U η0 δ0 eb : ℚ)
    (κ lam η δ : ℝ) (coef : CoefficientCandidateQ)
    (hc : coefficientsGeneratedQ d (2^r) (kappaApproxQ box) (lambdaApproxQ box) U (η0/2)=some coef)
    (hd : 0<d) (hklo : 0<box.kappa.lo) (hU : 0≤U) (hη0 : 0<η0) (hδ0 : 0<δ0) (hδ01 : δ0<1)
    (heb0 : 0≤eb) (heb : eb≤coef.maxTargetError)
    (hκlo : (box.kappa.lo : ℝ)≤κ) (hκhi : κ≤(box.kappa.hi : ℝ))
    (hlam0 : 0≤lam) (hlamlo : (box.lambda.lo : ℝ)≤lam) (hlamhi : lam≤(box.lambda.hi : ℝ))
    (hbudget : parameterBiasQ d r U box≤η0/2) (hη : (η0 : ℝ)≤η) (hδ : (δ0 : ℝ)≤δ)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1)
    (u : Fin d → (Fin d → Fin (2^r)) → ℝ) (û : Fin d → (Fin d → Fin (2^r)) → ℚ)
    (hu : ∀ j x, |u j x|≤(U : ℝ)) (htarget : ∀ j x, |(û j x : ℝ)-u j x|≤(eb : ℝ)) :
    let p := gridHighConfidencePlanQ d r coef.alpha coef.beta (U+eb) coef.gamma (η0/2) δ0
    finiteBadMass (nativeHighConfidenceLaw d r p a b c k hz)
      (fun z => (highConfidenceOutputQ p û (fun j => periodicDoubleShift d (2^r) j)
        coef.alpha coef.beta (U+eb) coef.gamma z : ℝ))
      (spinorDiscreteLoss a b c k u (periodicUnitShift d (2^r))
        (2*Real.pi/((2^r : ℕ) : ℝ)) κ lam) η≤δ := by
  have ht := generated_high_confidence_original_accuracy (kappaApproxQ box) (lambdaApproxQ box)
    U (η0/2) δ0 eb coef hc hd hklo hU (by positivity) hδ0 hδ01 heb0 heb a b c k hz u û hu htarget
  exact physical_box_accuracy_transfer box U η0 δ0 a b c k hz u (periodicUnitShift d (2^r))
    κ lam η δ _ _ hklo hU hκlo hκhi hlam0 hlamlo hlamhi hu hbudget hη hδ ht

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.generated_high_confidence_original_accuracy
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.enclosed_high_confidence_original_accuracy
