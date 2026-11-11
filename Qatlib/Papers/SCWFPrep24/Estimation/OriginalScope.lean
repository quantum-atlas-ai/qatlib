/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Retained.LowSpinOriginal

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.SCWFPrep24.Estimation

/-! OQ #141@44d4c95b9bcc0125a536ca5ccb06758090c5ace6 supplies this explicitly attributed extension/consumer of the Su et al. loss and encoding. It does not certify their entire training algorithm or a later analytical lower bound. -/
section
open Qatlib.Concepts.SpinorSampling.FiniteExecution Qatlib.Foundations.ProbabilityCore.Concentration Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords Qatlib.Concepts.SpinorSampling.Retained
open Qatlib.Concepts.SpinorSampling.Retained
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild
open scoped BigOperators
open Qatlib
open Qatlib.Concepts.SpinorSampling.FiniteExecution.ParameterEncoding
open Qatlib.Concepts.SpinorSampling.Matching.Matched

/-- Complete fixed-source statement `SCWFPreliminary.RetainedSpin.generated_low_spin_original_accuracy`; every original binder, hypothesis, and output is retained. -/
theorem retained_spin_full_loss_accuracy {d r : ℕ}
    (κ lam U η δ eb p₀ : ℚ) (coef : CoefficientCandidateQ)
    (hc : coefficientsGeneratedQ d (2^r) κ lam U η=some coef)
    (hd : 0<d) (hκ : 0<κ) (hU : 0≤U) (hη : 0<η) (hδ : 0<δ) (hδ1 : δ<1)
    (heb0 : 0≤eb) (heb : eb≤coef.maxTargetError)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1)
    (u : Fin d → (Fin d → Fin (2^r)) → ℝ)
    (û : Fin d → (Fin d → Fin (2^r)) → ℚ)
    (hu : ∀ j x, |u j x|≤(U : ℝ)) (htarget : ∀ j x, |(û j x : ℝ)-u j x|≤(eb : ℝ))
    (hp : 0≤p₀) (hp1 : p₀≤1/2)
    (hmean : coef.gamma≠0 → ∀ j,bellMean a b c k (periodicDoubleShift d (2^r) j)≤(p₀ : ℝ)) :
    let p := lowSpinPlanQ (2^r) d (2^(d*r)) ((2^((d*r+1)/2) : ℕ) : ℚ)
      coef.alpha coef.beta (U+eb) coef.gamma η δ p₀
    finiteBadMass (nativeLowSpinLaw d r p a b c k hz)
      (fun z => (lowSpinOutputQ p û (fun j => periodicDoubleShift d (2^r) j)
        coef.alpha coef.beta (U+eb) coef.gamma z : ℝ))
      (spinorDiscreteLoss a b c k u (periodicUnitShift d (2^r))
        (2*Real.pi/((2^r : ℕ) : ℝ)) (κ : ℝ) (lam : ℝ)) (η : ℝ)≤(δ : ℝ) := by
  exact Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.generated_low_spin_original_accuracy κ lam U η δ eb p₀ coef hc hd hκ hU hη hδ hδ1 heb0 heb a b c k hz u û hu htarget hp hp1 hmean
end

end Qatlib.Papers.SCWFPrep24.Estimation
