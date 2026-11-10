/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NativeNumerics.EmpiricalRisk.EmpiricalRiskConsumers
import Qatlib.Concepts.RiskEstimation.PopulationGap.NativeRiskDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.FairRandomBits.EmpiricalWeight
open Qatlib.Concepts.NativeNumerics.EmpiricalRisk
open Qatlib.Concepts.SqEstimation.HierarchicalSQ
open Qatlib.Concepts.RiskEstimation.PopulationGap
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.LinearLearning.ConcisePipeline

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QRiskWoerner18.EmpiricalRisk
open Matrix
open scoped Classical BigOperators ENNReal

def EmpiricalNativeCDFReadoutJoint : Prop :=
  ∀ (n N ebits bits M r : ℕ) (p : FinDist (Option (Fin n))) (loss : Option (Fin n) → ℚ)
    (t : ℚ) (ν : ℝ), 0 < N → 0 < ν → (hM : 2 ≤ M) →
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
      ((closurePMF (independentSampleLaw (fun _ : Fin N => p))).bind (fun ω =>
        (riskNativeSample bits r
          (riskCDFLaw (empiricalPrepare ω ebits) none loss t M
            (empiricalPrepare_unitary ω ebits) hM)).map
          (fun z : ℚ => (z : ℝ))))
      (fun z => ν+64*(n : ℝ)/2^ebits+
        (Real.pi/M+Real.pi^2/(M : ℝ)^2+(1/2 : ℝ)^bits) < |z-populationCDF p loss t|) ≤
      ENNReal.ofReal (1/(4*(N : ℝ)*ν^2)+(8/9 : ℝ)^r)

end Qatlib.Papers.QRiskWoerner18.EmpiricalRisk
