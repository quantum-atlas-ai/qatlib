/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QRiskWoerner18.EmpiricalRisk.EmpiricalNativeCDFReadoutJointStat
import Qatlib.Concepts.RiskEstimation.CDFEstimation.NativeCDFReadoutRestrictedQuan
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.FairRandomBits.EmpiricalWeight
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.NativeNumerics.EmpiricalRisk
open Qatlib.Concepts.SqEstimation.HierarchicalSQ
open Qatlib.Concepts.RiskEstimation.CDFEstimation
open Qatlib.Concepts.RiskEstimation.PopulationGap
open Qatlib.Concepts.RiskEstimation.VaRQuantile
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.LinearLearning.ConcisePipeline

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QRiskWoerner18.EmpiricalRisk
open scoped Classical BigOperators ENNReal
set_option warningAsError false

theorem empiricalNativeCDFReadoutJoint : EmpiricalNativeCDFReadoutJoint := by
  intro n N ebits bits M r p loss t ν hN hν hM
  let B : (Fin N → Option (Fin n)) → Prop := fun ω =>
    ν < |(empiricalCDF ω loss t : ℝ)-populationCDF p loss t|
  let E : ℝ → Prop := fun z => ν+64*(n : ℝ)/2^ebits+
    (Real.pi/M+Real.pi^2/(M : ℝ)^2+(1/2 : ℝ)^bits) < |z-populationCDF p loss t|
  let f := fun ω : Fin N → Option (Fin n) =>
    (riskNativeSample bits r (riskCDFLaw (empiricalPrepare ω ebits) none loss t M
      (empiricalPrepare_unitary ω ebits) hM)).map (fun z : ℚ => (z : ℝ))
  have hgood (ω : Fin N → Option (Fin n)) (hω : ¬ B ω) :
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (f ω) E ≤ ENNReal.ofReal ((8/9 : ℝ)^r) := by
    have hs : |(empiricalCDF ω loss t : ℝ)-populationCDF p loss t| ≤ ν := le_of_not_gt hω
    have hb := (empirical_actual_preparation_cdf_bias n N ebits ω loss t hN).2
    dsimp only [f]
    rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]
    apply (risk_event_mono _ (fun z hz => ?_)).trans
      (riskNativeCDFReadout (Option (Fin n)) (empiricalPrepare ω ebits) none loss t
        bits M r (empiricalPrepare_unitary ω ebits) hM)
    change E (z : ℝ) at hz
    dsimp only [E] at hz
    have htri₁ := abs_sub_le (z : ℝ) (riskCDF (empiricalPrepare ω ebits) none loss t)
      (populationCDF p loss t)
    have htri₂ := abs_sub_le (riskCDF (empiricalPrepare ω ebits) none loss t)
      (empiricalCDF ω loss t : ℝ) (populationCDF p loss t)
    linarith
  have hb := risk_bind_failure (closurePMF (independentSampleLaw (fun _ : Fin N => p)))
    f B E (ENNReal.ofReal ((8/9 : ℝ)^r)) hgood
  apply hb.trans
  rw [risk_closure_event, ENNReal.ofReal_add (by positivity) (by positivity)]
  have hs := empirical_cdf_sampling_bound p loss t ν hN hν
  have hs' : Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass (independentSampleLaw (fun _ : Fin N => p)) B ≤
      1/(4*(N : ℝ)*ν^2) := by
    simpa only [Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass, B, FinDist.probEvent, FinDist.probOf,
      independentSampleLaw] using! hs
  exact add_le_add (ENNReal.ofReal_le_ofReal hs') le_rfl

end Qatlib.Papers.QRiskWoerner18.EmpiricalRisk
