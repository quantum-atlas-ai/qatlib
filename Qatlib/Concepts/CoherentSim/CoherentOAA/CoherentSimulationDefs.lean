/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.CoherentOAA.ScaleEightCoherentAmplification
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
import Qatlib.Concepts.BlockEncoding.Basic
import Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding

/-!
# Data for coherent simulation and amplification

This module defines the angle, attenuation word, and repeated cubic amplification word for a
general scale. These constructions extend the amplitude amplification setup of
[BrassardEtAl2002] by making the attenuation parameter and iteration count explicit.

It also supplies success-branch normalization, binary fixed-point amplitude data, cosine
truncation quantities, and resource records for reset operations and time-varying segments. The
structures record data and prescribed counts without asserting additional accuracy or physical
implementation properties.

## Main definitions

* `generalScaleAmplifyWord`: an attenuated lifted circuit followed by the prescribed
  amplification levels.
* `successConditionedState`: the optional normalized successful projective branch.
* `ComplexAmplitude`: integer and binary fractional parts of a complex amplitude.
* `TimeVaryingSegment`: duration, repetition count, and term label for a segment.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

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

/-- The angle `π / (2 * 3 ^ k)` used for `k` levels of cubic amplification. -/
noncomputable def generalScaleAngle (k : ℕ) : ℝ := Real.pi / (2 * 3 ^ k)

/-- The matrix `scaleEightRotation (s * Real.sin (generalScaleAngle k))` used to attenuate the
added Boolean register. -/
noncomputable def generalScaleAttenuation (s : ℝ) (k : ℕ) : Matrix Bool Bool ℂ :=
  scaleEightRotation (s * Real.sin (generalScaleAngle k))

/-- The circuit word obtained by lifting every instruction to an additional Boolean register. -/
noncomputable def generalScaleLiftWord {H : Type} (cs : List (AdjointStep H)) :
    List (AdjointStep (Bool × H)) :=
  cs.map scaleEightLiftStep

/-- The lifted circuit word followed by a gate applying the general-scale attenuation on the
added register. -/
noncomputable def generalScaleAttenuationWord {H : Type} (s : ℝ) (k : ℕ)
    (cs : List (AdjointStep H)) : List (AdjointStep (Bool × H)) :=
  generalScaleLiftWord cs ++ [.gate (TensorGate (generalScaleAttenuation s k) 1)]

/-- The general-scale attenuation word amplified through `k` levels using the lifted frame. -/
noncomputable def generalScaleAmplifyWord {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (s : ℝ) (k : ℕ) (R : Matrix H I ℂ)
    (cs : List (AdjointStep H)) : List (AdjointStep (Bool × H)) :=
  scaleEightLevels (scaleEightFrame R) k (generalScaleAttenuationWord s k cs)

/-- The condition that `s` is nonnegative and `s * sin (generalScaleAngle k)` is at most one. -/
def generalScaleAdmissible (s : ℝ) (k : ℕ) : Prop :=
  0 ≤ s ∧ s * Real.sin (generalScaleAngle k) ≤ 1

/-- The optional conditional state for the successful branch of the projective measurement
specified by `P`. -/
noncomputable def successConditionedState {I : Type} [Fintype I] [DecidableEq I]
    (P : Matrix I I ℂ) (ψ : QState I) : Option (QState I) :=
  ProjectiveConditionalState P true ψ

/-- The successful projective branch divided by the square root of its total mass, or zero when
that mass is not positive. -/
noncomputable def normalizedSuccessBranch {I : Type} [Fintype I] [DecidableEq I]
    (P : Matrix I I ℂ) (ψ : QState I) : QState I :=
  let b := ProjectiveBranch P true ψ
  let m := MeasureProb b Finset.univ
  if 0 < m then (Real.sqrt m : ℂ)⁻¹ • b else 0

/-- The diagonal projector onto the false coordinate of the Boolean state space. -/
def demoLeakProjector : Matrix Bool Bool ℂ := fun i j =>
  if i = j then (if i = false then (1 : ℂ) else 0) else 0

/-- The Boolean basis state supported at false. -/
def demoSuccessState : QState Bool := fun i => if i = false then (1 : ℂ) else 0

/-- The Boolean basis state supported at true. -/
def demoLeakState : QState Bool := fun i => if i = true then (1 : ℂ) else 0

/-- The lower binary grid approximation `floor (θ * 2 ^ bits) / 2 ^ bits`. -/
noncomputable def quantizedReal (θ : ℝ) (bits : ℕ) : ℝ := (⌊θ * 2 ^ bits⌋ : ℤ) / 2 ^ bits

/-- The cosine Taylor sum through the term of degree `2 * N`. -/
noncomputable def cosTruncation (θ : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1), (-1) ^ j * θ ^ (2 * j) / Nat.factorial (2 * j)

/-- The quantity `θ ^ (2 * (N + 1)) / (2 * (N + 1))!` corresponding to the next unsigned cosine
term. -/
noncomputable def cosTruncationTail (θ : ℝ) (N : ℕ) : ℝ :=
  θ ^ (2 * (N + 1)) / Nat.factorial (2 * (N + 1))

/-- The prescribed cosine truncation accuracy quantity, defined as `cosTruncationTail θ N`. -/
noncomputable def cosTruncationAccuracy (θ : ℝ) (N : ℕ) : ℝ := cosTruncationTail θ N

/-- The prescribed bit-length budget `n * n`. -/
def factorialBitLength (n : ℕ) : ℕ := n * n

/-- Integer and natural fractional components for the real and imaginary parts of an amplitude,
with a shared binary precision. -/
structure ComplexAmplitude where

  realInt : ℤ

  realFrac : ℕ

  imagInt : ℤ

  imagFrac : ℕ

  bits : ℕ
  deriving DecidableEq, Repr

/-- The real component decoded as its integer part plus its fractional numerator divided by `2 ^
bits`. -/
noncomputable def ComplexAmplitude.realValue (a : ComplexAmplitude) : ℝ :=
  (a.realInt : ℝ) + (a.realFrac : ℝ) / 2 ^ a.bits

/-- The imaginary component decoded as its integer part plus its fractional numerator divided by
`2 ^ bits`. -/
noncomputable def ComplexAmplitude.imagValue (a : ComplexAmplitude) : ℝ :=
  (a.imagInt : ℝ) + (a.imagFrac : ℝ) / 2 ^ a.bits

/-- The prescribed preparation gate count `a.bits + 1`. -/
def ComplexAmplitude.prepareGateCount (a : ComplexAmplitude) : ℕ := a.bits + 1

/-- The prescribed preparation bit count `2 * a.bits + 2`. -/
def ComplexAmplitude.prepareBitCount (a : ComplexAmplitude) : ℕ :=
  2 * a.bits + 2

/-- A record of measurement, correction, and ancillary-register counts for a reset-and-discard
operation. -/
structure ResetDiscardReceipt where

  measured : ℕ

  corrections : ℕ

  ancillas : ℕ
  deriving DecidableEq, Repr

/-- The sum of the measured and correction counts in a reset-and-discard receipt. -/
def ResetDiscardReceipt.gateCount (r : ResetDiscardReceipt) : ℕ :=
  r.measured + r.corrections

/-- A time-varying segment specified by a real duration, a repetition count, and a term index. -/
structure TimeVaryingSegment where

  length : ℝ

  repeats : ℕ

  term : ℕ

/-- The sum of the durations of the listed segments. -/
noncomputable def TimeVaryingSegment.totalTime (segs : List TimeVaryingSegment) : ℝ :=
  segs.foldl (fun acc s => acc + s.length) 0

/-- The sum of the repetition counts of the listed segments. -/
def TimeVaryingSegment.totalRepeats (segs : List TimeVaryingSegment) : ℕ :=
  segs.foldl (fun acc s => acc + s.repeats) 0

end Qatlib.Concepts.CoherentSim.CoherentOAA
