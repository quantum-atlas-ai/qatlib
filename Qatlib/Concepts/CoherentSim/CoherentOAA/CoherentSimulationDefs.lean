/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.CoherentOAA.ScaleEightCoherentAmplification
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
import Qatlib.Concepts.BlockEncoding.Basic
import Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding

set_option autoImplicit false

namespace Qatlib.Concepts.CoherentSim.CoherentOAA

open Qatlib
open Matrix Encoding SignalProcessing
open scoped Classical Matrix.Norms.L2Operator BigOperators

noncomputable def generalScaleAngle (k : ℕ) : ℝ := Real.pi / (2 * 3 ^ k)

noncomputable def generalScaleAttenuation (s : ℝ) (k : ℕ) : Matrix Bool Bool ℂ :=
  scaleEightRotation (s * Real.sin (generalScaleAngle k))

noncomputable def generalScaleLiftWord {H : Type} (cs : List (AdjointStep H)) :
    List (AdjointStep (Bool × H)) :=
  cs.map scaleEightLiftStep

noncomputable def generalScaleAttenuationWord {H : Type} (s : ℝ) (k : ℕ)
    (cs : List (AdjointStep H)) : List (AdjointStep (Bool × H)) :=
  generalScaleLiftWord cs ++ [.gate (TensorGate (generalScaleAttenuation s k) 1)]

noncomputable def generalScaleAmplifyWord {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (s : ℝ) (k : ℕ) (R : Matrix H I ℂ)
    (cs : List (AdjointStep H)) : List (AdjointStep (Bool × H)) :=
  scaleEightLevels (scaleEightFrame R) k (generalScaleAttenuationWord s k cs)

def generalScaleAdmissible (s : ℝ) (k : ℕ) : Prop :=
  0 ≤ s ∧ s * Real.sin (generalScaleAngle k) ≤ 1

noncomputable def successConditionedState {I : Type} [Fintype I] [DecidableEq I]
    (P : Matrix I I ℂ) (ψ : QState I) : Option (QState I) :=
  ProjectiveConditionalState P true ψ

noncomputable def normalizedSuccessBranch {I : Type} [Fintype I] [DecidableEq I]
    (P : Matrix I I ℂ) (ψ : QState I) : QState I :=
  let b := ProjectiveBranch P true ψ
  let m := MeasureProb b Finset.univ
  if 0 < m then (Real.sqrt m : ℂ)⁻¹ • b else 0

def demoLeakProjector : Matrix Bool Bool ℂ := fun i j =>
  if i = j then (if i = false then (1 : ℂ) else 0) else 0

def demoSuccessState : QState Bool := fun i => if i = false then (1 : ℂ) else 0

def demoLeakState : QState Bool := fun i => if i = true then (1 : ℂ) else 0

noncomputable def quantizedReal (θ : ℝ) (bits : ℕ) : ℝ := (⌊θ * 2 ^ bits⌋ : ℤ) / 2 ^ bits

noncomputable def cosTruncation (θ : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1), (-1) ^ j * θ ^ (2 * j) / Nat.factorial (2 * j)

noncomputable def cosTruncationTail (θ : ℝ) (N : ℕ) : ℝ :=
  θ ^ (2 * (N + 1)) / Nat.factorial (2 * (N + 1))

noncomputable def cosTruncationAccuracy (θ : ℝ) (N : ℕ) : ℝ := cosTruncationTail θ N

def factorialBitLength (n : ℕ) : ℕ := n * n

structure ComplexAmplitude where

  realInt : ℤ

  realFrac : ℕ

  imagInt : ℤ

  imagFrac : ℕ

  bits : ℕ
  deriving DecidableEq, Repr

noncomputable def ComplexAmplitude.realValue (a : ComplexAmplitude) : ℝ :=
  (a.realInt : ℝ) + (a.realFrac : ℝ) / 2 ^ a.bits

noncomputable def ComplexAmplitude.imagValue (a : ComplexAmplitude) : ℝ :=
  (a.imagInt : ℝ) + (a.imagFrac : ℝ) / 2 ^ a.bits

def ComplexAmplitude.prepareGateCount (a : ComplexAmplitude) : ℕ := a.bits + 1

def ComplexAmplitude.prepareBitCount (a : ComplexAmplitude) : ℕ :=
  2 * a.bits + 2

structure ResetDiscardReceipt where

  measured : ℕ

  corrections : ℕ

  ancillas : ℕ
  deriving DecidableEq, Repr

def ResetDiscardReceipt.gateCount (r : ResetDiscardReceipt) : ℕ :=
  r.measured + r.corrections

structure TimeVaryingSegment where

  length : ℝ

  repeats : ℕ

  term : ℕ

noncomputable def TimeVaryingSegment.totalTime (segs : List TimeVaryingSegment) : ℝ :=
  segs.foldl (fun acc s => acc + s.length) 0

def TimeVaryingSegment.totalRepeats (segs : List TimeVaryingSegment) : ℕ :=
  segs.foldl (fun acc s => acc + s.repeats) 0

end Qatlib.Concepts.CoherentSim.CoherentOAA
