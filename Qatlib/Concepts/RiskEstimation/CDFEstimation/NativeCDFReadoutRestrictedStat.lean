/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.Postselection
import Qatlib.Concepts.NativeNumerics.LayeredMean.NativeSignedMeanConsumers
import Qatlib.Concepts.RiskEstimation.CVaREstimation.CVaRAlgorithmFiniteRestrictedQuan
import Qatlib.Concepts.NativeNumerics.EmpiricalRisk.RiskActualAccessLedgerFiniteQuan
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.NativeAeReadout

/-!
# Specification of native CDF readout

This module defines `NativeCDFReadoutRestricted`, the tail guarantee for the median of `2 * r +
1` finite-precision amplitude-estimation samples of a CDF.

The quantum risk-analysis setting is described in [WoernerEgger2019].

## Main statements

* `NativeCDFReadoutRestricted`: The proposition that native CDF median decoding exceeds error `π
  / M + π² / M² + 2⁻ᵇⁱᵗˢ` with probability at most `(8 / 9) ^ r` for unitary preparation and `M
  ≥ 2`.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.NativeNumerics.EmpiricalRisk
open Qatlib.Concepts.SqEstimation.HierarchicalSQ
open Qatlib.Concepts.RiskEstimation.CVaREstimation
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.RiskEstimation.CDFEstimation
open Matrix Polynomial Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

/-- The proposition that native CDF median decoding exceeds error `π / M + π² / M² + 2⁻ᵇⁱᵗˢ`
with probability at most `(8 / 9) ^ r` for unitary preparation and `M ≥ 2`. -/
def NativeCDFReadoutRestricted : Prop :=
    ∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j : I)
      (loss : I → ℚ) (t : ℚ) (bits M r : ℕ)
      (hA : A ∈ Matrix.unitaryGroup I ℂ) (hM : 2 ≤ M),
      let sample := fun p : FinDist (Fin M) =>
        (closurePMF ({
          prob := p.probOf
          nonneg := fun ω => Finset.prod_nonneg (fun z _ => p.nonneg (ω z))
          sum_one := p.sum_probOf (2*r+1) } : FinDist (Fin (2*r+1) → Fin M))).map
          (fun ω => (((List.ofFn (fun z => nativeAEDecode M bits (ω z))).mergeSort
            (fun a b => a ≤ b)).getD r 0))
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sample (riskCDFLaw A j loss t M hA hM))
        (fun z => Real.pi/M+Real.pi^2/(M : ℝ)^2+(1/2 : ℝ)^bits <
          |(z : ℝ)-riskCDF A j loss t|) ≤ ENNReal.ofReal ((8/9 : ℝ)^r)

end Qatlib.Concepts.RiskEstimation.CDFEstimation
