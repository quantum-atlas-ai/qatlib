/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.StopModel.VariableTimeAlgorithmContracts
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.GrowingStopDefs

/-!
# Structural variable-time programs

`StructuralVtStep` provides stage access, controlled access, workspace gates, and specified
reflections with matrix semantics and legality conditions. `GrowingVtSupported` links nonzero
prefix amplitudes to the reached history, allowing reached stopped mass to be identified with
total stopped mass.

This development concerns variable-time amplitude amplification in [Ambainis2012].

## Main statements

* `structural_workspace_no_data_transfer`: workspace gates preserve data labels.
* `growing_supported_stopping_mass`: equality of reached and total stopped mass.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LocalMachine.LocalTransport

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.VarTimeAmpAmp10.StopModel
open Matrix
open scoped Classical

/-- Instructions for forward, backward, and controlled stage access, workspace gates, and
source, good, and reached-set reflections with controlled variants. -/
inductive StructuralVtStep (W C : Type) [Fintype C] where
  | stageF : ℕ → StructuralVtStep W C
  | stageB : ℕ → StructuralVtStep W C
  | cstageF : ℕ → StructuralVtStep W C
  | cstageB : ℕ → StructuralVtStep W C
  | workspaceGate : Matrix (W × Bool) (W × Bool) ℂ → StructuralVtStep W C
  | sourceReflection : StructuralVtStep W C
  | csourceReflection : StructuralVtStep W C
  | goodReflection : StructuralVtStep W C
  | cgoodReflection : StructuralVtStep W C
  | reachedReflection : ℕ → StructuralVtStep W C
  | creachedReflection : ℕ → StructuralVtStep W C

variable {W C : Type} [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C]

/-- Charges each stage access, including controlled access, the dyadic time `2^j` and all other
structural instructions zero access time. -/
def structuralStepTime : StructuralVtStep W C → ℕ
  | .stageF j | .stageB j | .cstageF j | .cstageB j=>2^j
  | _=>0

/-- The sum of structural instruction access times in a word. -/
def structuralWordTime (word : List (StructuralVtStep W C)) : ℕ :=
  (word.map structuralStepTime).sum

/-- Extends a matrix on the workspace and control bit by the identity on the variable-time data
register. -/
def structuralWorkspaceGate (U : Matrix (W × Bool) (W × Bool) ℂ) : Matrix (VtReg W C) (VtReg W C) ℂ :=
  fun p q=>U (p.1,p.2.1) (q.1,q.2.1) * (1 : Matrix (VtSpace C) (VtSpace C) ℂ) p.2.2 q.2.2

/-- Interprets a structural instruction as a matrix on the workspace, control bit, and
variable-time data register. -/
def structuralStepMatrix (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C) :
    StructuralVtStep W C → Matrix (VtReg W C) (VtReg W C) ℂ
  | .stageF j=>stepMatrix stages (.stageF j)
  | .stageB j=>stepMatrix stages (.stageB j)
  | .cstageF j=>stepMatrix stages (.cstageF j)
  | .cstageB j=>stepMatrix stages (.cstageB j)
  | .workspaceGate U=>structuralWorkspaceGate U
  | .sourceReflection=>TensorGate 1 (TensorGate 1 (ReflectionAbout (outerProduct (Ket j₀))))
  | .csourceReflection=>TensorGate 1 (Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle (ReflectionAbout (outerProduct (Ket j₀))))
  | .goodReflection=>TensorGate 1 (TensorGate 1 (preparedMark (goodSet C)))
  | .cgoodReflection=>TensorGate 1 (Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle (preparedMark (goodSet C)))
  | .reachedReflection k=>TensorGate 1 (TensorGate 1 (preparedMark (reachedStoppedSet history k)))
  | .creachedReflection k=>TensorGate 1 (Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle (preparedMark (reachedStoppedSet history k)))

/-- Requires valid stage and reached-history indices and unitary workspace gates for a
structural instruction. -/
def StructuralStepLegal (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) : StructuralVtStep W C → Prop
  | .stageF j | .stageB j | .cstageF j | .cstageB j=>j < stages.length
  | .workspaceGate U=>U∈Matrix.unitaryGroup (W × Bool) ℂ
  | .reachedReflection k | .creachedReflection k=>k ≤ stages.length
  | _=>True

/-- The condition that every instruction in a structural word is legal for the given stages. -/
def StructuralWordLegal (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (word : List (StructuralVtStep W C)) : Prop := ∀ s∈word,StructuralStepLegal stages s

/-- Compiles a structural word into a circuit by interpreting each instruction as a gate. -/
def compileStructuralWord (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C) (word : List (StructuralVtStep W C)) : Circuit (VtReg W C) :=
  word.map fun s=>Step.gate (structuralStepMatrix stages history j₀ s)

omit [Fintype W] [DecidableEq W] in

/-- A lifted workspace gate has zero matrix entry between distinct variable-time data labels. -/
theorem structural_workspace_no_data_transfer (U : Matrix (W × Bool) (W × Bool) ℂ)
    (p q : VtReg W C) (h : p.2.2≠q.2.2) : structuralWorkspaceGate U p q=0 := by
  simp [structuralWorkspaceGate,h]

/-- The support condition that stopped prefix amplitudes have payloads in the current history
and running prefix amplitudes have payloads outside it. -/
def GrowingVtSupported (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C) : Prop :=
  ∀ k,k ≤ stages.length → ∀ p : VtSpace C,
    vtState stages k (Ket j₀) p≠0 →
      (p.1≠vtRunningFlag → p.2∈history k) ∧
      (p.1=vtRunningFlag → p.2∉history k)

omit [Fintype W] [DecidableEq W] in

/-- Under the growing-history support condition, reached stopped mass equals total stopped mass
at every valid prefix. -/
theorem growing_supported_stopping_mass (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (history : ℕ → Finset C) (j₀ : VtSpace C) (hs : GrowingVtSupported stages history j₀)
    (k : ℕ) (hk : k ≤ stages.length) :
    reachedStoppedMass stages history (Ket j₀) k=stoppedMass stages j₀ k := by
  unfold reachedStoppedMass stoppedMass MeasureProb
  rw [reachedStoppedSet,stoppedSet,Finset.sum_filter,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hf : p.1=vtRunningFlag
  · simp [hf]
  · by_cases hp : p.2∈history k
    · simp [hf,hp]
    · have hz : vtState stages k (Ket j₀) p=0 := by
        by_contra hn
        exact hp ((hs k hk p hn).1 hf)
      simp [hf,hp,BornProb,hz]
end Qatlib.Papers.VarTimeAmpAmp10.StopModel
