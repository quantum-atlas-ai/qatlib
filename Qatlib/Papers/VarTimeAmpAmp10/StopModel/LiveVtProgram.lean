/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.StopModel.StructuralProgram

/-!
# Live amplification program words

`DataVtStep` describes data-register stage calls and source, good, live, and reached-set
reflections. The module assigns matrix semantics, legality, and dyadic access time to words,
then builds live amplitude-amplification words and recursively amplified cascade prefixes.

This development concerns variable-time amplitude amplification in [Ambainis2012].

## Main statements

* `liveAAWord`: a preparation word followed by live amplification rounds.
* `cascadeWord`: recursive stage extension and amplification.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.VarTimeAmpAmp10.StopModel
open Matrix
open scoped Classical

/-- The union of the good and running basis-label sets. -/
def liveSet (C : Type) [Fintype C] [DecidableEq C] : Finset (VtSpace C) :=
  goodSet C ∪ runningSet C

/-- The instruction type for forward and backward stage calls and source, good, live, and
reached-set reflections on the data register. -/
inductive DataVtStep where
  | stageF : ℕ → DataVtStep
  | stageB : ℕ → DataVtStep
  | sourceReflection : DataVtStep
  | goodReflection : DataVtStep
  | liveReflection : DataVtStep
  | reachedReflection : ℕ → DataVtStep

/-- Exchanges forward and backward stage calls and leaves each reflection instruction unchanged. -/
def dataVtStepInverse : DataVtStep → DataVtStep
  | .stageF i => .stageB i
  | .stageB i => .stageF i
  | .sourceReflection => .sourceReflection
  | .goodReflection => .goodReflection
  | .liveReflection => .liveReflection
  | .reachedReflection i => .reachedReflection i

/-- Reverses a word and replaces every instruction by its inverse instruction. -/
def dataVtWordInverse (word : List DataVtStep) : List DataVtStep :=
  word.reverse.map dataVtStepInverse

/-- Charges a stage call at index `i` the dyadic time `2^i` and charges reflections zero access
time. -/
def dataVtStepTime : DataVtStep → ℕ
  | .stageF i | .stageB i => 2 ^ i
  | _ => 0

/-- The sum of the access times of the instructions in a data-register word. -/
def dataVtWordTime (word : List DataVtStep) : ℕ :=
  (word.map dataVtStepTime).sum

variable {C : Type} [Fintype C] [DecidableEq C]

/-- Requires stage-call indices to be below the stage count and reached-reflection indices to be
at most that count. -/
def DataVtStepLegal (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) :
    DataVtStep → Prop
  | .stageF i | .stageB i => i < stages.length
  | .reachedReflection i => i ≤ stages.length
  | _ => True

/-- The condition that every instruction of a data-register word is legal for the stage list. -/
def DataVtWordLegal (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (word : List DataVtStep) : Prop :=
  ∀ step ∈ word, DataVtStepLegal stages step

/-- The matrix interpretation of a data-register instruction using the supplied stages, history,
and source basis label. -/
def dataVtStepMatrix (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C) :
    DataVtStep → Matrix (VtSpace C) (VtSpace C) ℂ
  | .stageF i => stages.getD i 1
  | .stageB i => (stages.getD i 1)ᴴ
  | .sourceReflection => ReflectionAbout (outerProduct (Ket j₀))
  | .goodReflection => preparedMark (goodSet C)
  | .liveReflection => preparedMark (liveSet C)
  | .reachedReflection i => preparedMark (reachedStoppedSet history i)

/-- The ordered product of instruction matrices, with later instructions multiplying on the
left. -/
def dataVtWordMatrix (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C) (word : List DataVtStep) :
    Matrix (VtSpace C) (VtSpace C) ℂ :=
  word.foldl (fun A step => dataVtStepMatrix stages history j₀ step * A) 1

/-- The state obtained by applying a data-register word's matrix to the source ket. -/
def dataVtWordState (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C) (word : List DataVtStep) :
    QState (VtSpace C) :=
  ApplyGate (dataVtWordMatrix stages history j₀ word) (Ket j₀)

/-- One live amplification round consisting of live reflection, inverse preparation, source
reflection, and preparation. -/
def liveAARound (word : List DataVtStep) : List DataVtStep :=
  [.liveReflection] ++ dataVtWordInverse word ++ [.sourceReflection] ++ word

/-- A preparation word followed by `k` copies of its live amplification round. -/
def liveAAWord (word : List DataVtStep) (k : ℕ) : List DataVtStep :=
  word ++ (List.replicate k (liveAARound word)).flatten

/-- Recursively appends the next forward stage to the previous cascade and applies the scheduled
number of live amplification rounds. -/
def cascadeWord (schedule : ℕ → ℕ) : ℕ → List DataVtStep
  | 0 => []
  | i + 1 => liveAAWord (cascadeWord schedule i ++ [.stageF i]) (schedule i)

end Qatlib.Papers.VarTimeAmpAmp10.StopModel
