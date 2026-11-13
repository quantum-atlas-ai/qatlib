/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NativeNumerics.EmpiricalRisk.EmpiricalRiskConsumers
import Qatlib.Concepts.RiskEstimation.PopulationGap.NativeRiskDefs

/-!
# Statement of the joint empirical value-at-risk bound

The predicate `EmpiricalNativeVaRJoint` specifies population CDF brackets for native
value-at-risk output after independent sampling. The quantile tolerance includes estimation,
sampling, and preparation errors, while the probability bound accounts for the finite loss grid
and the number of binary-search readouts.

The source paper is [WoernerEgger2019].

## Main statements

* `EmpiricalNativeVaRJoint`: The joint sampling and native value-at-risk guarantee on a nonempty
  sorted grid containing every loss value. Under its precision and positivity conditions, the
  probability of an invalid index or violated CDF brackets is at most xs.length/(4Nν²) +
  (Nat.clog 2 xs.length + 1)(8/9)^r.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean

open Qatlib.Concepts.FairRandomBits.EmpiricalWeight
open Qatlib.Concepts.NativeNumerics.EmpiricalRisk
open Qatlib.Concepts.SqEstimation.HierarchicalSQ
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.RiskEstimation.PopulationGap

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.LinearLearning.ConcisePipeline

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QRiskWoerner18.EmpiricalRisk
open Matrix
open scoped Classical BigOperators ENNReal

/-- The joint sampling and native value-at-risk guarantee on a nonempty sorted grid containing
every loss value. Under its precision and positivity conditions, the probability of an
invalid index or violated CDF brackets is at most xs.length/(4Nν²) + (Nat.clog 2 xs.length +
1)(8/9)^r. -/
def EmpiricalNativeVaRJoint : Prop :=
  ∀ (n N ebits bits M r : ℕ) (p : FinDist (Option (Fin n))) (loss : Option (Fin n) → ℚ)
    (xs : List ℚ) (q ε : ℚ) (ν : ℝ),
    0 < N → xs ≠ [] → xs.SortedLE → (∀ a, loss a ∈ xs) →
    0 < q → q < 1 → 0 < ε → 0 < ν → (hM : 2 ≤ M) →
    Real.pi/M+Real.pi^2/(M : ℝ)^2+(1/2 : ℝ)^bits ≤ (ε : ℝ) →
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
      ((closurePMF (independentSampleLaw (fun _ : Fin N => p))).bind (fun ω =>
        riskNativeVaR (empiricalPrepare ω ebits) none loss xs q bits M r
          (empiricalPrepare_unitary ω ebits) hM))
      (fun z => z.1 ≥ xs.length ∨
        populationCDF p loss (xs.getD z.1 0) < (q : ℝ)-((ε : ℝ)+ν+64*(n : ℝ)/2^ebits) ∨
        (z.1 ≠ 0 ∧ (q : ℝ)+((ε : ℝ)+ν+64*(n : ℝ)/2^ebits) <
          populationCDF p loss (xs.getD (z.1-1) 0))) ≤
      ENNReal.ofReal ((xs.length : ℝ)/(4*(N : ℝ)*ν^2)+
        (Nat.clog 2 xs.length+1)*(8/9 : ℝ)^r)

end Qatlib.Papers.QRiskWoerner18.EmpiricalRisk
