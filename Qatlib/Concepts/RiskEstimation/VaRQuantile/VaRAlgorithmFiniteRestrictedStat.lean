/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.VaRQuantile.RiskDefs

/-!
# Finite value-at-risk accuracy specification

`VaRAlgorithmFiniteRestricted` specifies the approximate quantile bracket produced by `riskVaR`
on a nonempty sorted list containing all loss values. If the amplitude-estimation window fits
within the chosen tolerance, the probability of an invalid index or a failed bracket inequality
is bounded by the search depth times the median failure bound. This is the finite search
specification associated with [WoernerEgger2019].

## Main statements

* `VaRAlgorithmFiniteRestricted`: the finite approximate-bracket failure probability contract.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option warningAsError false
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

/-- The specification that, on a sorted list containing all losses and with sufficient readout
accuracy, the approximate quantile-bracket failure probability of `riskVaR` is at most
`(Nat.clog 2 xs.length + 1) * (8/9)^r`. -/
def VaRAlgorithmFiniteRestricted : Prop :=
∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j : I)
  (loss : I  → ℚ) (xs : List ℚ) (q eps : ℝ) (M r : ℕ) (hA : A∈Matrix.unitaryGroup I ℂ) (hM : 2 ≤ M),
  xs ≠ []  → xs.SortedLE  → (∀ i,loss i∈xs)  → 0 < q  → q < 1  → 0 < eps  →
  Real.pi/M+Real.pi^2/(M:ℝ)^2 ≤ eps  →
  Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (riskVaR A j loss xs q M r hA hM)
    (fun z => z.1 ≥ xs.length ∨riskCDF A j loss (xs.getD z.1 0) < q-eps ∨
      (z.1 ≠ 0 ∧q+eps < riskCDF A j loss (xs.getD (z.1-1) 0)))
     ≤ ENNReal.ofReal ((Nat.clog 2 xs.length+1)*(8/9:ℝ)^r)
end Qatlib.Concepts.RiskEstimation.VaRQuantile
