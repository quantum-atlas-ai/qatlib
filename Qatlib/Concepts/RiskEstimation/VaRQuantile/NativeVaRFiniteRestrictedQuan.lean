/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.VaRQuantile.NativeVaRFiniteRestrictedStat
import Qatlib.Concepts.RiskEstimation.VaRQuantile.NativeRiskRoutingSubgoalQuan

/-!
# Rational readout value-at-risk bounds

This module proves `NativeVaRFiniteRestricted` by combining rational CDF readout with finite
quantile routing. The resulting approximate bracket has a failure bound proportional to the
bisection depth, and each supported run obeys explicit readout-call and counted-circuit query
budgets. This formalizes the finite precision bisection approach of [WoernerEgger2019].

## Main statements

* `riskNativeVaRFinite`: the finite rational readout accuracy and call-count contract.
* `risk_native_var_support_calls`: a logarithmic bound on calls for every supported output.
* `risk_native_var_query_budget`: a query bound including median repetitions and the
  amplitude-estimation circuit cost.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.RiskEstimation.CDFEstimation
open Qatlib.Concepts.RiskEstimation.PopulationGap
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.LinearLearning.ConcisePipeline

set_option autoImplicit false
namespace Qatlib.Concepts.RiskEstimation.VaRQuantile
open scoped Classical BigOperators ENNReal

/-- Finite rational CDF readout and bisection satisfy the approximate quantile-bracket failure
bound and the support call-count bound. This implements the finite precision search
associated with [Woerner and Egger, Section II][WoernerEgger2019]. -/
theorem riskNativeVaRFinite : NativeVaRFiniteRestricted := by
  intro I _ _ A j loss xs q ε bits M r hA hM hxs hs hloss hq0 hq1 heps hwindow
  change Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
      (riskNativeVaR A j loss xs q bits M r hA hM) _ ≤ _ ∧ _
  let sampler := fun t => riskNativeSample bits r (riskCDFLaw A j loss t M hA hM)
  have hsam : ∀ t, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (PMF.map (fun z : ℚ => (z : ℝ)) (sampler t))
      (fun z => (ε : ℝ) < |z-riskCDF A j loss t|) ≤ ENNReal.ofReal ((8/9 : ℝ)^r) := by
    intro t
    rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]
    apply le_trans (risk_event_mono _ (fun z hz => lt_of_le_of_lt hwindow hz))
    exact riskNativeCDFReadout I A j loss t bits M r hA hM
  have hroute := riskNativeRouting sampler xs q (Nat.clog 2 xs.length+1) 0 (xs.length-1)
  have ht : riskNativeBisect sampler xs q (Nat.clog 2 xs.length+1) 0 (xs.length-1) =
      riskBisect (fun t => PMF.map (fun z : ℚ => (z : ℝ)) (sampler t)) xs (q : ℝ)
        (Nat.clog 2 xs.length+1) 0 (xs.length-1) := by
    simpa only [riskNativeBisect, PMF.map, Function.comp_def, PMF.bind_pure] using! hroute.1
  refine ⟨?_, hroute.2⟩
  change Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
      (riskNativeBisect sampler xs q _ _ _) _ ≤ _
  rw [ht]
  simpa only [Nat.cast_add, Nat.cast_one] using!
    (riskBisectFiniteRouting _ xs (q : ℝ) (ε : ℝ) ((8/9 : ℝ)^r) (riskCDF A j loss)
    hxs hs (by exact_mod_cast hq0) (by exact_mod_cast hq1)
    (by exact_mod_cast heps.le) (by positivity) (riskCDF_monotone A j loss)
    (riskCDF_last A j loss xs hA hxs hs hloss) hsam).1

/-- Every supported output of `riskNativeVaR` records at most `Nat.clog 2 xs.length + 1`
bisection calls. -/
theorem risk_native_var_support_calls {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (loss : I → ℚ) (xs : List ℚ) (q : ℚ)
    (bits M r : ℕ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (hM : 2 ≤ M) :
    ∀ z ∈ (riskNativeVaR A j loss xs q bits M r hA hM).support,
      z.2 ≤ Nat.clog 2 xs.length+1 := by
  simpa only [riskNativeVaR, riskNativeBisect] using!
    (riskNativeRouting (fun t => riskNativeSample bits r (riskCDFLaw A j loss t M hA hM))
      xs q (Nat.clog 2 xs.length+1) 0 (xs.length-1)).2

/-- For a supported native value-at-risk output, multiplying its call count by the median
repetition count and the counted amplitude-estimation circuit cost is bounded by `(Nat.clog
2 xs.length + 1) * (2*r + 1) * (M - 1)`. -/
theorem risk_native_var_query_budget {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (loss : I → ℚ) (xs : List ℚ) (q t : ℚ)
    (bits M r : ℕ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (hM : 2 ≤ M)
    (z : ℕ × ℕ) (hz : z ∈ (riskNativeVaR A j loss xs q bits M r hA hM).support) :
    z.2*(2*r+1)*QueryCount (countedAECircuit M (payoffPreparation A (riskCDFPayoff loss t)) (j,false)) ≤
      (Nat.clog 2 xs.length+1)*(2*r+1)*(M-1) := by
  have hc :=
      risk_native_readout_charges (payoffPreparation A (riskCDFPayoff loss t)) (j,false) M r z.2 hM
  rw [hc.2.2.1]
  exact Nat.mul_le_mul_right (M-1) (Nat.mul_le_mul_right (2*r+1)
    (risk_native_var_support_calls A j loss xs q bits M r hA hM z hz))

end Qatlib.Concepts.RiskEstimation.VaRQuantile
