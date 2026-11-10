/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.StopModel.LiveVtProgram
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.StructuralEstimateInterface
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration

open Qatlib.Papers.VarTimeAmpAmp10.StopModel

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open Matrix
open scoped Classical

def recordDrivenResolution (m : ℕ) : ℕ := 1000000000 * m ^ 2 + 2

def recordDrivenRepetitions (m : ℕ) : ℕ := 1000 * m

def recordDrivenRoundCap (m : ℕ) : ℕ := 1000000000 * m ^ 2

abbrev RecordDrivenLabels (m : ℕ) :=
  Fin (2 * recordDrivenRepetitions m + 1) → Fin (recordDrivenResolution m)

abbrev RecordDrivenRecord (m : ℕ) := Fin (m + 1) → RecordDrivenLabels m

def recordDrivenEstimate (m : ℕ) (labels : RecordDrivenLabels m) : ℝ :=
  vtMedianEstimate (recordDrivenResolution m) (recordDrivenRepetitions m) labels

def recordDrivenPrefixRounds (m : ℕ) (labels : RecordDrivenLabels m) : ℕ :=
  if m ≤ 16 then 0 else
    ((List.range (recordDrivenRoundCap m + 1)).find? fun k =>
      decide (1 / (6 * (m : ℝ)) ≤
        ((2 * k + 1 : ℕ) : ℝ) ^ 2 * recordDrivenEstimate m labels)).getD 0

def recordDrivenSchedule (m : ℕ) (record : RecordDrivenRecord m) (i : ℕ) : ℕ :=
  if h : i < m then recordDrivenPrefixRounds m (record ⟨i, by omega⟩) else 0

def recordDrivenInputWord (m : ℕ) (record : RecordDrivenRecord m)
    (i : Fin (m + 1)) : List DataVtStep :=
  if i.val < m then
    cascadeWord (recordDrivenSchedule m record) i.val ++ [.stageF i.val]
  else cascadeWord (recordDrivenSchedule m record) m

def recordDrivenFinalRounds (m : ℕ) (labels : RecordDrivenLabels m) : ℕ :=
  ((List.range (recordDrivenRoundCap m + 1)).find? fun k =>
    decide ((1 / 2 : ℝ) ≤
      (Real.sin (((2 * k + 1 : ℕ) : ℝ) *
        Real.arcsin (Real.sqrt (recordDrivenEstimate m labels)))) ^ 2)).getD 0

def goodAARound (word : List DataVtStep) : List DataVtStep :=
  [.goodReflection] ++ dataVtWordInverse word ++ [.sourceReflection] ++ word

def goodAAWord (word : List DataVtStep) (k : ℕ) : List DataVtStep :=
  word ++ (List.replicate k (goodAARound word)).flatten

def recordDrivenOutputWord (m : ℕ) (record : RecordDrivenRecord m) : List DataVtStep :=
  goodAAWord (cascadeWord (recordDrivenSchedule m record) m)
    (recordDrivenFinalRounds m (record (Fin.last m)))

variable {C : Type} [Fintype C] [DecidableEq C]

def recordDrivenKernel (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C)
    (record : RecordDrivenRecord stages.length) (i : Fin (stages.length + 1))
    (labels : RecordDrivenLabels stages.length) : ℝ :=
  dataFreshKernel (recordDrivenResolution stages.length)
    (by unfold recordDrivenResolution; omega) (recordDrivenRepetitions stages.length)
    stages history j₀ (recordDrivenInputWord stages.length record i) labels

def recordDrivenLaw (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C)
    (record : RecordDrivenRecord stages.length) : ℝ :=
  ∏ i : Fin (stages.length + 1), recordDrivenKernel stages history j₀ record i (record i)

def recordDrivenEstimateTime (m : ℕ) (record : RecordDrivenRecord m) : ℕ :=
  ∑ i : Fin (m + 1),
    (2 * recordDrivenRepetitions m + 1) *
      (2 * (recordDrivenResolution m - 1) + 1) *
        dataVtWordTime (recordDrivenInputWord m record i)

def recordDrivenTotalTime (m : ℕ) (record : RecordDrivenRecord m) : ℕ :=
  recordDrivenEstimateTime m record + dataVtWordTime (recordDrivenOutputWord m record)

end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
