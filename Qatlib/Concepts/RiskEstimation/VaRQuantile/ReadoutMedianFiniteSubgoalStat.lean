/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.VaRQuantile.RiskDefs

/-!
# Median CDF readout specification

`ReadoutMedianFiniteSubgoal` specifies the tail probability of the median estimator for
`riskCDF`. For a unitary preparation and an amplitude-estimation size at least two, the
probability of exceeding the window `π/M + π²/M²` is bounded by `(8/9)^r`. This is a
median-amplified version of amplitude estimation [BrassardEtAl2002].

## Main statements

* `ReadoutMedianFiniteSubgoal`: the finite CDF median error contract.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018

open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
namespace Qatlib.Concepts.RiskEstimation.VaRQuantile
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

/-- The specification that the median CDF readout exceeds the window `π/M + π²/M²` around
`riskCDF` with probability at most `(8/9)^r`. -/
def ReadoutMedianFiniteSubgoal : Prop :=
∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j : I) (loss : I  → ℚ)
  (t : ℚ) (M r : ℕ) (hA : A∈Matrix.unitaryGroup I ℂ) (hM : 2 ≤ M),
  Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (riskMedianPMF (riskCDFLaw A j loss t M hA hM) r)
    (fun z => Real.pi/M+Real.pi^2/(M:ℝ)^2 < |z-riskCDF A j loss t|)
     ≤ ENNReal.ofReal ((8/9:ℝ)^r)
end Qatlib.Concepts.RiskEstimation.VaRQuantile
