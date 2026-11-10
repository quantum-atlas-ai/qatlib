/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.StopModel.VariableTimeDefs
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.VariableTimeProgramDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement

namespace Qatlib.Papers.VarTimeAmpAmp10.StopModel

open Matrix

section Program

variable {C : Type} [Fintype C] [DecidableEq C]

end Program

def coherentVariableTimeAmplification : Prop :=
  ∀ (C : Type) [Fintype C] [DecidableEq C]
    (stages : List (Matrix (Fin 3 × C) (Fin 3 × C) ℂ)),
    (∀ U ∈ stages, IsVtStage U) → 1 ≤ stages.length →
    ∀ (j₀ : Fin 3 × C), j₀.1 = vtRunningFlag →
    let Ψ := vtState stages stages.length (Ket j₀)
    MeasureProb Ψ (runningSet C) = 0 →
    1 / (10 ^ 12 * (stages.length : ℝ) ^ 3) ≤ MeasureProb Ψ (goodSet C) →
    ∃ (Ω : Type) (_ : Fintype Ω) (w : Ω → ℝ) (good : Finset Ω)
      (W : Type) (_ : Fintype W) (_ : DecidableEq W) (w₀ : W)
      (prog : Ω → List (VtStep W C)),
      (∑ ω, w ω = 1) ∧ (∀ ω, 0 ≤ w ω) ∧
      (∀ ω, WordLegal stages (prog ω)) ∧
      (∀ ω, (wordStageTime (prog ω) : ℝ) ≤
        4000000 * (stages.length : ℝ) * Real.sqrt (stages.length : ℝ) *
          (vtTmax stages + vtTav stages j₀ / Real.sqrt (MeasureProb Ψ (goodSet C)))) ∧
      (1 - 1 / 10 ≤ ∑ ω ∈ good, w ω) ∧
      (∀ ω ∈ good,
        let out := Run 1 (compileWord stages (prog ω)) (Ket (w₀, (false, j₀)))
        2 / 5 ≤ MeasureProb out
          (Finset.univ.filter (fun p : VtReg W C => p.2.2.1 = vtGoodFlag)) ∧
        MeasureProb out
          (Finset.univ.filter (fun p : VtReg W C => p.2.2.1 = vtRunningFlag)) ≤ 3 / 5 ∧
        ∃ c : ℂ, Collapse out
            (Finset.univ.filter (fun p : VtReg W C => p.2.2.1 = vtGoodFlag))
          = c • embedState w₀ (Collapse Ψ (goodSet C)))

end Qatlib.Papers.VarTimeAmpAmp10.StopModel
