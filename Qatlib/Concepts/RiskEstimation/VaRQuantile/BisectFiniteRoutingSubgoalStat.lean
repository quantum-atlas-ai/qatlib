/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.VaRQuantile.RiskDefs

/-!
# Finite quantile routing specification

`BisectFiniteRoutingSubgoal` specifies the behavior of `riskBisect` on a nonempty sorted list of
rational thresholds. Uniformly accurate samples of a monotone function give an approximate
quantile bracket with failure probability at most the search depth times the per-call bound, and
the call counter never exceeds that depth. The specification models the bisection step in
[WoernerEgger2019].

## Main statements

* `BisectFiniteRoutingSubgoal`: the approximate quantile bracket and depth-bound contract.

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

/-- The specification that bisection on a sorted finite threshold list fails to bracket the
target with probability at most `d * delta`, where `d` is the prescribed depth. It also
requires the probability of using more than `d` calls to be zero. -/
def BisectFiniteRoutingSubgoal : Prop :=
∀ (sample : ℚ  → PMF ℝ) (xs : List ℚ) (q eps delta : ℝ) (F : ℚ  → ℝ),
  xs ≠ []  → xs.SortedLE  → 0 < q  → q < 1  → 0 ≤ eps  → 0 ≤ delta  → Monotone F  → F (xs.getLastD 0)=1  →
  (∀ t,Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sample t) (fun z => eps < |z-F t|) ≤ ENNReal.ofReal delta)  →
  let d := Nat.clog 2 xs.length+1;
  let p := riskBisect sample xs q d 0 (xs.length-1);
  Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun z => z.1 ≥ xs.length ∨F (xs.getD z.1 0) < q-eps ∨
    (z.1 ≠ 0 ∧q+eps < F (xs.getD (z.1-1) 0))) ≤ ENNReal.ofReal (d*delta) ∧
  Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun z => d < z.2)=0
end Qatlib.Concepts.RiskEstimation.VaRQuantile
