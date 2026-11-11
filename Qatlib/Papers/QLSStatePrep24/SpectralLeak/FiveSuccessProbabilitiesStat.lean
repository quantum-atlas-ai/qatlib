/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLSStatePrep24.SpectralLeak.BandModels

/-!
# Specification of five spectral success weights

The proposition `Clause31FiveSuccessProbabilities` states the quantitative comparison of the
single-band, inverse-band, near-band, full-band, and perturbed state weights. Its hypotheses
specify spectral band membership, legal normalized rows, total row error below one, and a norm
perturbation bound. See [LowSu2026] for the paper context.

## Main statements

* `Clause31FiveSuccessProbabilities`: The proposition comparing five success weights under valid
  spectral bands, normalized coefficients, legal rows, and a bounded state perturbation,
  including factor-nine inverse-band bounds, leakage estimates, and a `4 * εbm` probability
  error.

## References

* [Low and Su, 2026][LowSu2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Papers.QLSStatePrep24.SpectralLeak
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QLSStatePrep24.SpectralLeak
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Matrix
open Qatlib.Concepts.QlsReadoutSpec.Amplification Qatlib.Papers.QLSStatePrep24.SpectralLeak
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

/-- The proposition comparing five success weights under valid spectral bands, normalized
coefficients, legal rows, and a bounded state perturbation, including factor-nine
inverse-band bounds, leakage estimates, and a `4 * εbm` probability error. -/
def Clause31FiveSuccessProbabilities : Prop :=
  ∀ (I : Type) [Fintype I] (m : ℕ) (k : I → ℕ) (σ : I → ℝ) (γ : I → ℂ)
    (ξ : ℕ → I → QState (Fin 2)) (δ : ℕ → ℝ)
    (χ : QState (Fin m × I)) (εbm : ℝ),
    (∀ u, bandIndexValid m (σ u) (k u)) → Normalized γ →
    bandRowsLegal m k ξ δ → 0 ≤ εbm →
    normVec χ ≤ 1 → normVec (χ-weightedBandState m γ (stopCoefficient ξ)) ≤ 2*εbm →
    let e := ∑ j : Fin m, δ (j.val+1)
    e < 1 →
    let p1 := singleBandProbability m k γ
    let p := inverseBandProbability m σ γ
    let pn := (normVec (nearBandState m k γ (stopCoefficient ξ)))^2
    let pf := (normVec (weightedBandState m γ (stopCoefficient ξ)))^2
    let pbm := (normVec χ)^2
    p1/9 ≤ p ∧ p ≤ p1 ∧ p1/9*(1-e^2) ≤ pn ∧ pn ≤ p1 ∧
    pn ≤ pf ∧ pf ≤ pn*(1+9^3*e^2/(1-e)^2) ∧ abs (pf-pbm) ≤ 4*εbm

end Qatlib.Papers.QLSStatePrep24.SpectralLeak
