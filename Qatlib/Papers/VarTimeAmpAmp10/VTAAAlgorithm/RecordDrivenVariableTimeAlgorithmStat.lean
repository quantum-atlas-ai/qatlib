/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.RecordDrivenCascade

/-!
# Specification of the record-driven variable-time algorithm

The proposition `RecordDrivenVariableTimeAlgorithm` states a finite-record amplification
guarantee for a nonempty legal supported growing-stop pipeline starting in the running sector.
It assumes complete final stopping and a success floor `1 / (10^12 * m³)`, and requires a
probability law, legal words, good-record mass at least `9 / 10`, output success at least `2 /
5`, preservation of the good-state direction, and explicit time bounds.

This is the record-driven specification associated with the variable-time construction of
[Ambainis2012]. Its output-word and total-time bounds have different polynomial factors in the
stage count.

## Main statements

* `RecordDrivenVariableTimeAlgorithm`: the record-law, legality, output-state, and runtime
  specification.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree

open Qatlib.Papers.VarTimeAmpAmp10.StopModel

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement

set_option autoImplicit false
namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm

/-- The record-driven amplification specification for nonempty legal supported growing-stop
pipelines starting in the running sector, with zero final running mass and success `p ≥ 1 /
(10^12 * m³)`. It requires normalized nonnegative record weights, legal words, and a set of
record mass at least `9 / 10` with success at least `2 / 5`, running mass at most `3 / 5`,
the original good-state direction, output-word time at most `1000 * m² * (Tmax + reachedTav
/ sqrt p)`, and total time at most `10^18 * m^6 * sqrt m * (Tmax + reachedTav / sqrt p)`. -/
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
