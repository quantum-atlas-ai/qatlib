/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLSStatePrep24.SpectralLeak.BandModels

/-!
# Specification of spectral leakage bounds

The proposition `Clause30WeightedSpectralLeakage` packages stopping-mass normalization and two
leakage estimates for legal band rows. Both estimates are quadratic in the sum of row errors,
with constants expressed through `singleBandProbability`. See [LowSu2026] for the paper context.

## Main statements

* `Clause30WeightedSpectralLeakage`: The proposition that legal rows have unit stopping mass and
  that weighted and unweighted leakage are bounded by `9 * p1 * e²` and `p1 * e² / 9`,
  respectively.

## References

* [Low and Su, 2026][LowSu2026]
-/

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

/-- The proposition that legal rows have unit stopping mass and that weighted and unweighted
leakage are bounded by `9 * p1 * e²` and `p1 * e² / 9`, respectively. -/
def Clause30WeightedSpectralLeakage : Prop :=
  ∀ (I : Type) [Fintype I] (m : ℕ) (k : I → ℕ) (γ : I → ℂ)
    (ξ : ℕ → I → QState (Fin 2)) (δ : ℕ → ℝ), bandRowsLegal m k ξ δ →
    let ζ := stopCoefficient ξ
    let e := ∑ j : Fin m, δ (j.val+1)
    (∀ u, (∑ j : Fin m, ‖ζ (j.val+1) u‖^2)=1) ∧
    bandLeakage m k γ ζ true ≤ 9*singleBandProbability m k γ*e^2 ∧
    bandLeakage m k γ ζ false ≤ singleBandProbability m k γ/9*e^2

end Qatlib.Papers.QLSStatePrep24.SpectralLeak
