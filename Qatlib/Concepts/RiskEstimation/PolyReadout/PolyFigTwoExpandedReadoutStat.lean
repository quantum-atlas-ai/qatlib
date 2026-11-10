/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PolyReadout.PolyFigTwoExpandedDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.NativeRiskDefs
import Qatlib.Concepts.RiskEstimation.PolyReadout.PolyRotationDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.RiskEstimation.PolyRotation
open Qatlib.Concepts.RiskEstimation.PopulationGap

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.RiskEstimation.PolyReadout
open Matrix
open scoped Classical BigOperators ENNReal

def PolyFigTwoExpandedReadout : Prop :=
  ∀ (n : ℕ) (A : Matrix (Reg n) (Reg n) ℂ) (j : Reg n) (u : ℕ) (c : ℝ) (fp : Polynomial ℝ)
    (M r bits : ℕ), (hA : A ∈ Matrix.unitaryGroup (Reg n) ℂ) → (hM : 2 ≤ M) →
    (∀ x : Reg n, fp.eval (figTwoRegEval x : ℝ) ∈ Set.Icc (0 : ℝ) 1) → 0 < c → c ≤ 1 →
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
      ((riskNativeSample bits r (figTwoExpandedLaw n A j u c fp M hA hM)).map
        (fun z : ℚ => ((z : ℝ)-1/2)/c+1/2))
      (fun w => riskPolyReadoutWindow u c M bits <
        |w-∑ x, BornProb (A*ᵥKet j) x*fp.eval (figTwoRegEval x : ℝ)|) ≤
      ENNReal.ofReal ((8/9 : ℝ)^r)

end Qatlib.Concepts.RiskEstimation.PolyReadout
