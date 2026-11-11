/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NativeNumerics.EmpiricalRisk.EmpiricalRiskConsumers
import Qatlib.Concepts.RiskEstimation.PopulationGap.NativeRiskDefs

/-!
# Statement of the native empirical CVaR bound

The predicate `EmpiricalNativeCVaRTargetError` states a guarantee for native empirical CVaR on a
sorted loss grid. Given a separated target quantile, bounded losses, approximation bounds for a
target probability and tail mean, and a positive denominator margin, it bounds the event of an
incorrect index or excessive error in the target ratio.

The source paper is [WoernerEgger2019].

## Main statements

* `EmpiricalNativeCVaRTargetError`: The native CVaR guarantee relative to μ/p under the
  specified loss, quantile separation, precision, approximation, and positive-denominator
  conditions. It bounds the probability of a wrong target index or ratio error above the stated
  tolerance by (Nat.clog 2 xs.length + 3)(8/9)^r.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.FairRandomBits.EmpiricalWeight
open Qatlib.Concepts.NativeNumerics.EmpiricalRisk
open Qatlib.Concepts.RiskEstimation.PopulationGap
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018

open Qatlib.Concepts.LinearLearning.ConcisePipeline

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QRiskWoerner18.EmpiricalRisk
open Matrix
open scoped Classical BigOperators ENNReal

/-- The native CVaR guarantee relative to μ/p under the specified loss, quantile separation,
precision, approximation, and positive-denominator conditions. It bounds the probability of
a wrong target index or ratio error above the stated tolerance by (Nat.clog 2 xs.length +
3)(8/9)^r. -/
def EmpiricalNativeCVaRTargetError : Prop :=
  ∀ (n N ebits rotationBits bits M r : ℕ) (ω : Fin N → Option (Fin n))
    (loss : Option (Fin n) → ℚ) (t : ℚ) (p μ η : ℝ) (xs : List ℚ) (q ε : ℚ) (v : ℕ),
    0 < N → (hloss : ∀ a, 0 ≤ loss a ∧ loss a ≤ 1) → (hM : 2 ≤ M) →
    xs ≠ [] → xs.SortedLE → (∀ a, loss a ∈ xs) →
    0 < q → q < 1 → 0 < ε → v < xs.length →
    xs.getD v 0 = t →
    Real.pi/M+Real.pi^2/(M : ℝ)^2+64/(2 : ℝ)^rotationBits+(1/2 : ℝ)^bits ≤ (ε : ℝ) →
    (q : ℝ)+ε < riskCDF (empiricalPrepare ω ebits) none loss t →
    (∀ u : ℕ, u < v → riskCDF (empiricalPrepare ω ebits) none loss (xs.getD u 0) < (q : ℝ)-ε) →
    2*(ε : ℝ) < riskCDF (empiricalPrepare ω ebits) none loss t →
    0 ≤ η → |(empiricalCDF ω loss t : ℝ)-p| ≤ η →
    |(((∑ a, empiricalWeight ω a*riskTailPayoff loss t a)/(N : ℚ) : ℚ) : ℝ)-μ| ≤ η →
    0 < p → 2*(η+64*(n : ℝ)/2^ebits) < p →
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
      (riskNativeCVaR (empiricalPrepare ω ebits) none loss xs q ε rotationBits bits M r
        (empiricalPrepare_unitary ω ebits) hloss hM)
      (fun z => z.1 ≠ v ∨
        4*(ε : ℝ)/riskCDF (empiricalPrepare ω ebits) none loss t+
          4*(η+64*(n : ℝ)/2^ebits)/p < |(z.2.1 : ℝ)-μ/p|) ≤
      ENNReal.ofReal ((Nat.clog 2 xs.length+3)*(8/9 : ℝ)^r)

end Qatlib.Papers.QRiskWoerner18.EmpiricalRisk
