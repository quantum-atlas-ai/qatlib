/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.CDFEstimation.NativeCDFReadoutRestrictedStat
import Qatlib.Concepts.RiskEstimation.PopulationGap.NativeRiskDefs

/-!
# Finite-precision CDF readout bounds

This module proves a median tail bound for native amplitude-estimation decoding and applies it
to `riskCDF`. The error window includes both amplitude-estimation error and the finite decoding
precision.

The quantum risk-analysis setting is described in [WoernerEgger2019].

## Main statements

* `risk_native_median_tail`: If a single amplitude-estimation sample is within error `e` with
  mass at least `8 / π²`, the native median exceeds error `e + 2⁻ᵇⁱᵗˢ` with probability at most
  `(8 / 9) ^ r`.
* `riskNativeCDFReadout`: The native CDF median readout satisfies its finite-precision error
  bound with failure probability at most `(8 / 9) ^ r`; see [WoernerEgger2019].

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.RiskEstimation.PopulationGap
open Qatlib.Concepts.RiskEstimation.VaRQuantile
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.LinearLearning.ConcisePipeline

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Qatlib.Concepts.RiskEstimation.CDFEstimation
open scoped Classical BigOperators ENNReal

/-- If a single amplitude-estimation sample is within error `e` with mass at least `8 / π²`, the
native median exceeds error `e + 2⁻ᵇⁱᵗˢ` with probability at most `(8 / 9) ^ r`. -/
theorem risk_native_median_tail {M : ℕ} (p : FinDist (Fin M)) (bits r : ℕ) (μ e : ℝ)
    (he : 0 ≤ e)
    (hgood : 8/Real.pi^2 ≤ Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass p (fun z => |aeEstimate M z-μ| ≤ e)) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (riskNativeSample bits r p)
      (fun z => e+(1/2 : ℝ)^bits < |(z : ℝ)-μ|) ≤ ENNReal.ofReal ((8/9 : ℝ)^r) := by
  classical
  have hdecode : 8/Real.pi^2 ≤ Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass p
      (fun z => |(nativeAEDecode M bits z : ℝ)-μ| ≤ e+(1/2 : ℝ)^bits) := by
    apply hgood.trans
    apply Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass_mono
    intro z hz
    have hd : |(nativeAEDecode M bits z : ℝ)-aeEstimate M z| ≤ (1/2 : ℝ)^bits :=
      by simpa only [one_div] using! (native_ae_computed_scalar_precision M bits z).2.2
    have ht := abs_sub_le (nativeAEDecode M bits z : ℝ) (aeEstimate M z) μ
    linarith
  have hp : (2/3 : ℝ) ≤ 8/Real.pi^2 := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < Real.pi^2)).mpr
    nlinarith [Real.pi_pos, Real.pi_lt_d2]
  have hc := Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass_complement p
    (fun z => |(nativeAEDecode M bits z : ℝ)-μ| ≤ e+(1/2 : ℝ)^bits)
  simp only [not_le] at hc
  have hb : Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass p
      (fun z => e+(1/2 : ℝ)^bits < |(nativeAEDecode M bits z : ℝ)-μ|) ≤ 1/3 := by
    linarith
  have hm := Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.sorted_median_failure p (fun z => (nativeAEDecode M bits z : ℝ)) r μ
    (e+(1/2 : ℝ)^bits) (by positivity) hb
  unfold riskNativeSample
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map, risk_closure_event]
  apply ENNReal.ofReal_le_ofReal
  simpa only [risk_native_median_cast, Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass,
      FinDist.probEvent] using! hm

/-- The native CDF median readout satisfies its finite-precision error bound with failure
probability at most `(8 / 9) ^ r`; see [WoernerEgger2019]. -/
theorem riskNativeCDFReadout : NativeCDFReadoutRestricted := by
  intro I _ _ A j loss t bits M r hA hM
  change Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
      (riskNativeSample bits r (riskCDFLaw A j loss t M hA hM)) _ ≤ _
  apply risk_native_median_tail
  · positivity
  · rw [riskCDF_eq]
    exact risk_mean_good A j (riskCDFPayoff loss t) M hA (riskCDFPayoff_bounds loss t) hM

end Qatlib.Concepts.RiskEstimation.CDFEstimation
