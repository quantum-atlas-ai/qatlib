/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.StopModel.LiveVtProgram
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.StructuralEstimateInterface

/-!
# Record-driven variable-time cascade definitions

This module defines the finite estimation records, bounded round searches, and cascade words for
a record-driven variable-time amplification construction associated with [Ambainis2012]. The
conditional kernels determine `recordDrivenLaw`, and separate time functions charge the
estimation words and the final output word.

## Main statements

* `recordDrivenSchedule`: the prefix round schedule selected from a record.
* `recordDrivenOutputWord`: the final good-amplification word.
* `recordDrivenLaw`: the product of record-dependent sampling kernels.
* `recordDrivenTotalTime`: estimation time plus output-word time.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration

open Qatlib.Papers.VarTimeAmpAmp10.StopModel

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open Matrix
open scoped Classical

/-- The estimation resolution `10^9 * m² + 2` for a pipeline of length `m`. -/
def recordDrivenResolution (m : ℕ) : ℕ := 1000000000 * m ^ 2 + 2

/-- The median repetition parameter `1000 * m`. -/
def recordDrivenRepetitions (m : ℕ) : ℕ := 1000 * m

/-- The round-search cap `10^9 * m²`. -/
def recordDrivenRoundCap (m : ℕ) : ℕ := 1000000000 * m ^ 2

/-- A vector of `2 * recordDrivenRepetitions m + 1` estimation labels at the prescribed
resolution. -/
abbrev RecordDrivenLabels (m : ℕ) :=
  Fin (2 * recordDrivenRepetitions m + 1) → Fin (recordDrivenResolution m)

/-- A record containing one estimation-label vector at each of `m + 1` positions. -/
abbrev RecordDrivenRecord (m : ℕ) := Fin (m + 1) → RecordDrivenLabels m

/-- The median amplitude estimate computed from a label vector at the prescribed resolution and
repetition parameter. -/
def recordDrivenEstimate (m : ℕ) (labels : RecordDrivenLabels m) : ℝ :=
  vtMedianEstimate (recordDrivenResolution m) (recordDrivenRepetitions m) labels

/-- The first round count within the cap whose estimated ideal gain reaches `1 / (6 * m)`,
defaulting to zero if none exists and always zero for `m ≤ 16`. -/
def recordDrivenPrefixRounds (m : ℕ) (labels : RecordDrivenLabels m) : ℕ :=
  if m ≤ 16 then 0 else
    ((List.range (recordDrivenRoundCap m + 1)).find? fun k =>
      decide (1 / (6 * (m : ℝ)) ≤
        ((2 * k + 1 : ℕ) : ℝ) ^ 2 * recordDrivenEstimate m labels)).getD 0

/-- The prefix-round schedule read from valid record positions, extended by zero for indices at
least `m`. -/
def recordDrivenSchedule (m : ℕ) (record : RecordDrivenRecord m) (i : ℕ) : ℕ :=
  if h : i < m then recordDrivenPrefixRounds m (record ⟨i, by omega⟩) else 0

/-- The estimation input word: a cascade prefix followed by its next forward stage, or the full
cascade at the final record position. -/
def recordDrivenInputWord (m : ℕ) (record : RecordDrivenRecord m)
    (i : Fin (m + 1)) : List DataVtStep :=
  if i.val < m then
    cascadeWord (recordDrivenSchedule m record) i.val ++ [.stageF i.val]
  else cascadeWord (recordDrivenSchedule m record) m

/-- The first round count within the cap whose estimated amplified good mass reaches `1 / 2`,
defaulting to zero when none is found. -/
def recordDrivenFinalRounds (m : ℕ) (labels : RecordDrivenLabels m) : ℕ :=
  ((List.range (recordDrivenRoundCap m + 1)).find? fun k =>
    decide ((1 / 2 : ℝ) ≤
      (Real.sin (((2 * k + 1 : ℕ) : ℝ) *
        Real.arcsin (Real.sqrt (recordDrivenEstimate m labels)))) ^ 2)).getD 0

/-- One good-amplification round consisting of a good reflection, the inverse input word, a
source reflection, and the input word. -/
def goodAARound (word : List DataVtStep) : List DataVtStep :=
  [.goodReflection] ++ dataVtWordInverse word ++ [.sourceReflection] ++ word

/-- The input word followed by `k` repetitions of its good-amplification round. -/
def goodAAWord (word : List DataVtStep) (k : ℕ) : List DataVtStep :=
  word ++ (List.replicate k (goodAARound word)).flatten

/-- The full scheduled cascade followed by the number of good-amplification rounds chosen from
the final record labels. -/
def recordDrivenOutputWord (m : ℕ) (record : RecordDrivenRecord m) : List DataVtStep :=
  goodAAWord (cascadeWord (recordDrivenSchedule m record) m)
    (recordDrivenFinalRounds m (record (Fin.last m)))

variable {C : Type} [Fintype C] [DecidableEq C]

/-- The fresh-estimation kernel for the input word determined by the record and its current
position. -/
def recordDrivenKernel (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C)
    (record : RecordDrivenRecord stages.length) (i : Fin (stages.length + 1))
    (labels : RecordDrivenLabels stages.length) : ℝ :=
  dataFreshKernel (recordDrivenResolution stages.length)
    (by unfold recordDrivenResolution; omega) (recordDrivenRepetitions stages.length)
    stages history j₀ (recordDrivenInputWord stages.length record i) labels

/-- The product of the record-dependent estimation kernels evaluated at the recorded label
vectors. -/
def recordDrivenLaw (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C)
    (record : RecordDrivenRecord stages.length) : ℝ :=
  ∏ i : Fin (stages.length + 1), recordDrivenKernel stages history j₀ record i (record i)

/-- The sum of input-word times weighted by their prescribed fresh-estimation repetition and
resolution factors. -/
def recordDrivenEstimateTime (m : ℕ) (record : RecordDrivenRecord m) : ℕ :=
  ∑ i : Fin (m + 1),
    (2 * recordDrivenRepetitions m + 1) *
      (2 * (recordDrivenResolution m - 1) + 1) *
        dataVtWordTime (recordDrivenInputWord m record i)

/-- The estimation time plus the time of the record-driven output word. -/
def recordDrivenTotalTime (m : ℕ) (record : RecordDrivenRecord m) : ℕ :=
  recordDrivenEstimateTime m record + dataVtWordTime (recordDrivenOutputWord m record)

end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
