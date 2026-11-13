/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.VaRQuantile.RiskDefs

/-!
# Specification of finite CDF preparation

This module states `CDFActualFiniteSubgoal`, the finite-dimensional CDF preparation identity and
threshold monotonicity property for unitary data preparation.

The quantum risk-analysis setting is described in [WoernerEgger2019].

## Main statements

* `CDFActualFiniteSubgoal`: The proposition that unitary CDF payoff preparation has flag
  probability `riskCDF` and that the resulting CDF is monotone in its threshold.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
namespace Qatlib.Concepts.RiskEstimation.CDFEstimation
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

/-- The proposition that unitary CDF payoff preparation has flag probability `riskCDF` and that
the resulting CDF is monotone in its threshold. -/
def CDFActualFiniteSubgoal : Prop :=
∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j : I) (loss : I  → ℚ) (t : ℚ),
  A∈Matrix.unitaryGroup I ℂ  →
  MeasureProb (payoffPreparation A (riskCDFPayoff loss t)*ᵥ Ket (j,false))
    (Finset.univ.filter (fun p : I ×Bool => p.2=true))=riskCDF A j loss t ∧
  (∀ u : ℚ,t ≤ u  → riskCDF A j loss t ≤ riskCDF A j loss u)
end Qatlib.Concepts.RiskEstimation.CDFEstimation
