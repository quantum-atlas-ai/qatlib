/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.VaRQuantile.RiskDefs
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

def ReadoutMedianFiniteSubgoal : Prop :=
∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j : I) (loss : I  → ℚ)
  (t : ℚ) (M r : ℕ) (hA : A∈Matrix.unitaryGroup I ℂ) (hM : 2 ≤ M),
  Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (riskMedianPMF (riskCDFLaw A j loss t M hA hM) r)
    (fun z => Real.pi/M+Real.pi^2/(M:ℝ)^2 < |z-riskCDF A j loss t|)
     ≤ ENNReal.ofReal ((8/9:ℝ)^r)
end Qatlib.Concepts.RiskEstimation.VaRQuantile
