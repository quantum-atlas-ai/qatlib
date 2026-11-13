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
# Finite rational value-at-risk specification

`NativeVaRFiniteRestricted` specifies approximate quantile bracketing for a median of rationally
decoded amplitude estimates. Its assumptions budget both amplitude-estimation error and decoding
error; its conclusions bound the failure probability and the number of bisection calls. The
estimator follows the risk-analysis construction of [WoernerEgger2019].

## Main statements

* `NativeVaRFiniteRestricted`: the finite precision bracket and support call-count contract.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

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
namespace Qatlib.Concepts.RiskEstimation.VaRQuantile
open Matrix Polynomial Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

/-- The specification of approximate quantile bracketing using median rational CDF readout with
amplitude-estimation and decoding errors within the tolerance. It bounds the bracket failure
probability and every supported call counter by the prescribed depth-dependent quantities. -/
def NativeVaRFiniteRestricted : Prop :=
    ∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j : I)
      (loss : I → ℚ) (xs : List ℚ) (q ε : ℚ) (bits M r : ℕ)
      (hA : A ∈ Matrix.unitaryGroup I ℂ) (hM : 2 ≤ M),
      xs ≠ [] → xs.SortedLE → (∀ i, loss i ∈ xs) → 0 < q → q < 1 → 0 < ε →
      Real.pi/M+Real.pi^2/(M : ℝ)^2+(1/2 : ℝ)^bits ≤ (ε : ℝ) →
      let sample := fun p : FinDist (Fin M) =>
        (closurePMF ({
          prob := p.probOf
          nonneg := fun ω => Finset.prod_nonneg (fun z _ => p.nonneg (ω z))
          sum_one := p.sum_probOf (2*r+1) } : FinDist (Fin (2*r+1) → Fin M))).map
          (fun ω => (((List.ofFn (fun z => nativeAEDecode M bits (ω z))).mergeSort
            (fun a b => a ≤ b)).getD r 0))
      let bisect := fun (sampler : ℚ → PMF ℚ) (xs : List ℚ) (q : ℚ)
          (fuel lo hi : ℕ) =>
        Nat.rec (motive := fun _ => ℕ → ℕ → PMF (ℕ×ℕ))
          (fun lo _ => PMF.pure (lo,0))
          (fun _ rec lo hi => if hi ≤ lo then PMF.pure (lo,0) else
            let mid := (lo+hi)/2
            (sampler (xs.getD mid 0)).bind (fun z =>
              (if q ≤ z then rec lo mid else rec (mid+1) hi).map
                (fun out => (out.1,out.2+1)))) fuel lo hi
      let law := bisect (fun t => sample (riskCDFLaw A j loss t M hA hM)) xs q
        (Nat.clog 2 xs.length+1) 0 (xs.length-1)
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event law (fun z => z.1 ≥ xs.length ∨
        riskCDF A j loss (xs.getD z.1 0) < (q : ℝ)-ε ∨
        (z.1 ≠ 0 ∧ (q : ℝ)+ε < riskCDF A j loss (xs.getD (z.1-1) 0))) ≤
          ENNReal.ofReal ((Nat.clog 2 xs.length+1)*(8/9 : ℝ)^r) ∧
        ∀ z ∈ law.support, z.2 ≤ Nat.clog 2 xs.length+1

end Qatlib.Concepts.RiskEstimation.VaRQuantile
