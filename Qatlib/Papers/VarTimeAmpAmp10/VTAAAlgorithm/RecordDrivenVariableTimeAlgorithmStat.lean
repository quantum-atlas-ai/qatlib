/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.RecordDrivenCascade
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree

open Qatlib.Papers.VarTimeAmpAmp10.StopModel

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement

set_option autoImplicit false
namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm

def RecordDrivenVariableTimeAlgorithm : Prop :=
  ∀ (C : Type) [Fintype C] [DecidableEq C]
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C),
    GrowingVtLegal stages history → 1 ≤ stages.length →
    ∀ (j₀ : VtSpace C), j₀.1 = vtRunningFlag →
    GrowingVtSupported stages history j₀ →
    let m := stages.length
    let Ψ := vtState stages m (Ket j₀)
    let p := MeasureProb Ψ (goodSet C)
    MeasureProb Ψ (runningSet C) = 0 →
    1 / (10 ^ 12 * (m : ℝ) ^ 3) ≤ p →
    (∑ record : RecordDrivenRecord m, recordDrivenLaw stages history j₀ record = 1) ∧
    (∀ record : RecordDrivenRecord m, 0 ≤ recordDrivenLaw stages history j₀ record) ∧
    (∀ record : RecordDrivenRecord m,
      (∀ i : Fin (m + 1), DataVtWordLegal stages (recordDrivenInputWord m record i)) ∧
      DataVtWordLegal stages (recordDrivenOutputWord m record)) ∧
    ∃ good : Finset (RecordDrivenRecord m),
      9 / 10 ≤ ∑ record ∈ good, recordDrivenLaw stages history j₀ record ∧
      ∀ record ∈ good,
        let out := dataVtWordState stages history j₀ (recordDrivenOutputWord m record)
        2 / 5 ≤ MeasureProb out (goodSet C) ∧
        MeasureProb out (runningSet C) ≤ 3 / 5 ∧
        (∃ c : ℂ, Collapse out (goodSet C) = c • Collapse Ψ (goodSet C)) ∧
        (dataVtWordTime (recordDrivenOutputWord m record) : ℝ) ≤
          1000 * (m : ℝ) ^ 2 * (vtTmax stages + reachedTav stages history j₀ / Real.sqrt p) ∧
        (recordDrivenTotalTime m record : ℝ) ≤
          1000000000000000000 * (m : ℝ) ^ 6 * Real.sqrt (m : ℝ) *
            (vtTmax stages + reachedTav stages history j₀ / Real.sqrt p)

end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
