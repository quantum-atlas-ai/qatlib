/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.VaRQuantile.RiskDefs

/-!
# Exact quantile bisection specification

`ExactQuantileNoMargin` specifies deterministic bisection with exact evaluations of `riskCDF`.
For a sorted finite list containing all loss values, the resulting index is the first one whose
cumulative probability reaches the target, and its threshold is minimal among qualifying
entries. This is the exact-evaluation counterpart of the risk search in [WoernerEgger2019].

## Main statements

* `ExactQuantileNoMargin`: in-range output, strict inequalities at earlier indices, and minimal
  qualifying threshold.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.RiskEstimation.VaRQuantile
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

/-- The specification that exact CDF bisection returns the first index reaching the target
probability on a sorted list containing every loss. Its selected threshold is minimal among
entries whose cumulative probability reaches the target. -/
def ExactQuantileNoMargin : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j : I)
    (loss : I → ℚ) (xs : List ℚ) (q : ℝ) (_hA : A ∈ Matrix.unitaryGroup I ℂ),
    xs ≠ [] → xs.SortedLE → (∀ i, loss i ∈ xs) → 0 < q → q < 1 →
    let F := fun v : ℕ => riskCDF A j loss (xs.getD v 0)
    let exactBisect : ℕ → ℕ → ℕ → ℕ := fun fuel lo hi =>
      Nat.rec (motive := fun _ => ℕ → ℕ → ℕ)
        (fun lo _ => lo)
        (fun _ rec lo hi => if hi ≤ lo then lo else
          let mid := (lo+hi)/2
          if q ≤ F mid then rec lo mid else rec (mid+1) hi)
        fuel lo hi
    let v := exactBisect (Nat.clog 2 xs.length + 1) 0 (xs.length - 1)
    v < xs.length ∧
    (∀ u : ℕ, u < v → F u < q) ∧
    (q ≤ F v) ∧
    (∀ u : ℕ, u < xs.length → q ≤ F u → xs.getD v 0 ≤ xs.getD u 0)

end Qatlib.Concepts.RiskEstimation.VaRQuantile
