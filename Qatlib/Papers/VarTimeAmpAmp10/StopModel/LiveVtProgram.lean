/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.StopModel.StructuralProgram
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.VarTimeAmpAmp10.StopModel
open Matrix
open scoped Classical

def liveSet (C : Type) [Fintype C] [DecidableEq C] : Finset (VtSpace C) :=
  goodSet C ∪ runningSet C

inductive DataVtStep where
  | stageF : ℕ → DataVtStep
  | stageB : ℕ → DataVtStep
  | sourceReflection : DataVtStep
  | goodReflection : DataVtStep
  | liveReflection : DataVtStep
  | reachedReflection : ℕ → DataVtStep

def dataVtStepInverse : DataVtStep → DataVtStep
  | .stageF i => .stageB i
  | .stageB i => .stageF i
  | .sourceReflection => .sourceReflection
  | .goodReflection => .goodReflection
  | .liveReflection => .liveReflection
  | .reachedReflection i => .reachedReflection i

def dataVtWordInverse (word : List DataVtStep) : List DataVtStep :=
  word.reverse.map dataVtStepInverse

def dataVtStepTime : DataVtStep → ℕ
  | .stageF i | .stageB i => 2 ^ i
  | _ => 0

def dataVtWordTime (word : List DataVtStep) : ℕ :=
  (word.map dataVtStepTime).sum

variable {C : Type} [Fintype C] [DecidableEq C]

def DataVtStepLegal (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) :
    DataVtStep → Prop
  | .stageF i | .stageB i => i < stages.length
  | .reachedReflection i => i ≤ stages.length
  | _ => True

def DataVtWordLegal (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (word : List DataVtStep) : Prop :=
  ∀ step ∈ word, DataVtStepLegal stages step

def dataVtStepMatrix (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C) :
    DataVtStep → Matrix (VtSpace C) (VtSpace C) ℂ
  | .stageF i => stages.getD i 1
  | .stageB i => (stages.getD i 1)ᴴ
  | .sourceReflection => ReflectionAbout (outerProduct (Ket j₀))
  | .goodReflection => preparedMark (goodSet C)
  | .liveReflection => preparedMark (liveSet C)
  | .reachedReflection i => preparedMark (reachedStoppedSet history i)

def dataVtWordMatrix (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C) (word : List DataVtStep) :
    Matrix (VtSpace C) (VtSpace C) ℂ :=
  word.foldl (fun A step => dataVtStepMatrix stages history j₀ step * A) 1

def dataVtWordState (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C) (word : List DataVtStep) :
    QState (VtSpace C) :=
  ApplyGate (dataVtWordMatrix stages history j₀ word) (Ket j₀)

def liveAARound (word : List DataVtStep) : List DataVtStep :=
  [.liveReflection] ++ dataVtWordInverse word ++ [.sourceReflection] ++ word

def liveAAWord (word : List DataVtStep) (k : ℕ) : List DataVtStep :=
  word ++ (List.replicate k (liveAARound word)).flatten

def cascadeWord (schedule : ℕ → ℕ) : ℕ → List DataVtStep
  | 0 => []
  | i + 1 => liveAAWord (cascadeWord schedule i ++ [.stageF i]) (schedule i)

end Qatlib.Papers.VarTimeAmpAmp10.StopModel
