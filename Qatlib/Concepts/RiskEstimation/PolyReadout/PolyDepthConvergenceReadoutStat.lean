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
import Qatlib.Concepts.RiskEstimation.PolyReadout.PolyRotationDefs

/-!
# Specification of polynomial payoff readout

This module defines `PolyDepthConvergenceReadout`, the concentration property for rescaled
native median readout of the polynomially rotated payoff law.

The quantum risk-analysis setting is described in [WoernerEgger2019].

## Main statements

* `PolyDepthConvergenceReadout`: The proposition that the rescaled median readout estimates the
  Born-weighted mean of a payoff in `[0, 1]` within `riskPolyReadoutWindow`, except with
  probability at most `(8 / 9) ^ r`, when `0 < c ≤ 1`.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.NativeNumerics.EmpiricalRisk
open Qatlib.Concepts.SqEstimation.HierarchicalSQ
open Qatlib.Concepts.RiskEstimation.CVaREstimation

open Qatlib.Foundations.PureStateMath
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
namespace Qatlib.Concepts.RiskEstimation.PolyReadout
open Matrix Polynomial Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

/-- The proposition that the rescaled median readout estimates the Born-weighted mean of a
payoff in `[0, 1]` within `riskPolyReadoutWindow`, except with probability at most `(8 / 9)
^ r`, when `0 < c ≤ 1`. -/
def PolyDepthConvergenceReadout : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j : I) (f : I → ℝ)
    (u : ℕ) (c : ℝ) (M r bits : ℕ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (hM : 2 ≤ M),
    (∀ i, f i ∈ Set.Icc (0 : ℝ) 1) → 0 < c → c ≤ 1 →
    let sample := fun p : FinDist (Fin M) =>
      (closurePMF ({
        prob := p.probOf
        nonneg := fun ω => Finset.prod_nonneg (fun z _ => p.nonneg (ω z))
        sum_one := p.sum_probOf (2*r+1) } : FinDist (Fin (2*r+1) → Fin M))).map
          (fun ω => (((List.ofFn (fun z => nativeAEDecode M bits (ω z))).mergeSort
            (fun a b => a ≤ b)).getD r 0))
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event ((sample (riskPolyMeanLaw M A j f u c hA hM)).map
        (fun z => ((z : ℝ) - 1/2)/c + 1/2))
      (fun w => riskPolyReadoutWindow u c M bits <
        |w - ∑ i, BornProb (A*ᵥ Ket j) i * f i|)
      ≤ ENNReal.ofReal ((8/9 : ℝ)^r)

end Qatlib.Concepts.RiskEstimation.PolyReadout
