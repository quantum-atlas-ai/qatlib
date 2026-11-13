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
# Rational quantile routing specification

`NativeRiskRoutingSubgoal` states that a fuel-limited bisection using rational samples agrees
with real-valued `riskBisect` after coercion. It also requires every supported output to record
at most the supplied fuel in calls. This transport specification supports finite precision
implementations of the search in [WoernerEgger2019].

## Main statements

* `NativeRiskRoutingSubgoal`: equality of routing laws and the support call-count guarantee.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.NativeNumerics.EmpiricalRisk
open Qatlib.Concepts.RiskEstimation.CVaREstimation
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018
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

/-- The specification that rational-sample bisection equals `riskBisect` after coercion to the
reals and that all supported call counters are bounded by the fuel. -/
def NativeRiskRoutingSubgoal : Prop :=
    let bisect := fun (sampler : ℚ → PMF ℚ) (xs : List ℚ) (q : ℚ)
          (fuel lo hi : ℕ) =>
        Nat.rec (motive := fun _ => ℕ → ℕ → PMF (ℕ×ℕ))
          (fun lo _ => PMF.pure (lo,0))
          (fun _ rec lo hi => if hi ≤ lo then PMF.pure (lo,0) else
            let mid := (lo+hi)/2
            (sampler (xs.getD mid 0)).bind (fun z =>
              (if q ≤ z then rec lo mid else rec (mid+1) hi).map
                (fun out => (out.1,out.2+1)))) fuel lo hi
      ∀ (sampler : ℚ → PMF ℚ) (xs : List ℚ) (q : ℚ) (fuel lo hi : ℕ),
        bisect sampler xs q fuel lo hi =
          riskBisect (fun t => (sampler t).map (fun z => (z : ℝ))) xs (q : ℝ) fuel lo hi ∧
        (∀ z ∈ (bisect sampler xs q fuel lo hi).support, z.2 ≤ fuel)

end Qatlib.Concepts.RiskEstimation.VaRQuantile
