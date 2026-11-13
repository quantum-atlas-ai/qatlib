/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.VaRQuantile.RiskDefs

/-!
# Separated finite quantile specification

`StableQuantileFiniteRestricted` specifies the probability of returning an incorrect quantile
index. The CDF must exceed the target plus the error margin at the chosen index and remain below
the target minus that margin at every earlier index. The specification expresses a stable case
of the bisection procedure in [WoernerEgger2019].

## Main statements

* `StableQuantileFiniteRestricted`: the separated-index recovery probability contract.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
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

/-- The specification that `riskVaR` recovers a prescribed, margin-separated quantile index
except with probability at most the bisection depth times `(8/9)^r`. -/
def StableQuantileFiniteRestricted : Prop :=
∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j : I)
  (loss : I  → ℚ) (xs : List ℚ) (q eps : ℝ) (M r v : ℕ) (hA : A∈Matrix.unitaryGroup I ℂ) (hM : 2 ≤ M),
  xs ≠ []  → xs.SortedLE  → (∀ i,loss i∈xs)  → 0 < q  → q < 1  → 0 < eps  → v < xs.length  →
  Real.pi/M+Real.pi^2/(M:ℝ)^2 ≤ eps  →
  q+eps < riskCDF A j loss (xs.getD v 0)  →
  (∀ u : ℕ,u < v  → riskCDF A j loss (xs.getD u 0) < q-eps)  →
  Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (riskVaR A j loss xs q M r hA hM) (fun z => z.1 ≠ v)
     ≤ ENNReal.ofReal ((Nat.clog 2 xs.length+1)*(8/9:ℝ)^r)
end Qatlib.Concepts.RiskEstimation.VaRQuantile
