/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeCountingConsumers
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LocalMachine.LocalTransport

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

set_option autoImplicit false

open Matrix
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open scoped Classical

variable {I : Type} [Fintype I] [DecidableEq I]

def BooleanEvaluationOracle (O : Matrix I I ℂ) (S : Finset I) : Prop :=
  O = preparedMark S ∧
    (∀ x : I, O x x = if x ∈ S then (-1 : ℂ) else 1) ∧
    (∀ x y : I, x ≠ y → O x y = 0)

def ControlledPhaseImplementation (O : Matrix I I ℂ) (S : Finset I) : Prop :=
  O = preparedMark S ∧
    controlOracle O ∈ Matrix.unitaryGroup (Bool × I) ℂ ∧
    (∀ x y : I,
      controlOracle O (false, x) (false, y) = if x = y then (1 : ℂ) else 0) ∧
    (∀ x y : I, controlOracle O (true, x) (true, y) = O x y) ∧
    (∀ x y : I,
      controlOracle O (false, x) (true, y) = 0 ∧
        controlOracle O (true, x) (false, y) = 0)

structure OracleCostLedger where
  sourceEvaluations : ℕ
  controlledMarks : ℕ
  prepAccesses : ℕ
  sourceReflections : ℕ
  controlMacros : ℕ
  validationQueries : ℕ
  finalEvaluations : ℕ
  fixedGates : ℕ

def sourceGridEvaluations (G : ℕ) : ℕ := G

def RecordLedgerTransport (G : ℕ) (L : OracleCostLedger) : Prop :=
  L.sourceEvaluations = sourceGridEvaluations G ∧
    L.controlledMarks = G - 1 ∧
    L.finalEvaluations = 1 ∧
    L.sourceEvaluations = L.controlledMarks + L.finalEvaluations ∧
    L.prepAccesses = 2 * (G - 1) + 1 ∧
    L.sourceReflections = G - 1 ∧
    L.controlMacros = G - 1 ∧
    L.validationQueries = 0 ∧
    L.fixedGates = 5 * (G - 1) + 3

def CircuitRealizesLedger (G : ℕ) (A : Matrix I I ℂ) (j : I)
    (L : OracleCostLedger) : Prop :=
  L.controlledMarks = QueryCount (countedAECircuit G A j) ∧
    L.fixedGates = GateCount (countedAECircuit G A j) ∧
    L.prepAccesses = aeInputAccesses (aeAccessWord (I := I) G) ∧
    L.sourceReflections = aeSourceReflections (aeAccessWord (I := I) G)

noncomputable def RecordValidates (G : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hG : 2 ≤ G) : Prop :=
  let input : QState (Fin G × (Bool × I)) :=
    TensorState (Ket (⟨0, by omega⟩ : Fin G)) (TensorState (Ket false) (Ket j))
  let out := Run (aeControlledGate G (preparedMark S)) (countedAECircuit G A j) input
  IsUnitaryCircuit (countedAECircuit G A j) ∧
    Normalized out ∧
    (∀ z : Fin G, ∀ i : I, out (z, true, i) = 0) ∧
    (∀ z : Fin G,
      (aeLaw G A j S hA hG).prob z =
        MeasureProb out (Finset.univ.filter (fun p => p.1 = z)))

def RecordOracleCostTransport (G : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (O : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (hG : 2 ≤ G) : Prop :=
  BooleanEvaluationOracle O S ∧
    ControlledPhaseImplementation O S ∧
    ∃ L : OracleCostLedger,
      RecordLedgerTransport G L ∧
        CircuitRealizesLedger G A j L ∧
        RecordValidates G A j S hA hG

def recordGrids {n : ℕ} (grid : Fin n → ℕ) (exec : Fin n → Bool) (Mfin : ℕ) :
    List ℕ :=
  ((List.ofFn fun l : Fin n => if exec l then some (grid l) else none).filterMap id)
    ++ [Mfin]

def pathMarks (grids : List ℕ) : ℕ := (grids.map (fun G => G - 1)).sum

def pathPrep (grids : List ℕ) : ℕ := (grids.map (fun G => 2 * (G - 1) + 1)).sum

def pathFixed (grids : List ℕ) : ℕ := (grids.map (fun G => 5 * (G - 1) + 3)).sum

def pathControl (grids : List ℕ) : ℕ := pathMarks grids

def PathLedgerTransport (grids : List ℕ) (L : OracleCostLedger) : Prop :=
  L.sourceEvaluations = grids.sum ∧
    L.controlledMarks = pathMarks grids ∧
    L.finalEvaluations = grids.length ∧
    L.sourceEvaluations = L.controlledMarks + L.finalEvaluations ∧
    L.prepAccesses = pathPrep grids ∧
    L.sourceReflections = L.controlledMarks ∧
    L.controlMacros = pathControl grids ∧
    L.validationQueries = 0 ∧
    L.fixedGates = pathFixed grids

def ExpectedLedgerTransport {Ω : Type} [Fintype Ω] (w : Ω → ℝ)
    (gridsOf : Ω → List ℕ) : Prop :=
  let marks : ℝ := ∑ ω, w ω * (pathMarks (gridsOf ω) : ℝ)
  let finals : ℝ := ∑ ω, w ω * ((gridsOf ω).length : ℝ)
  let control : ℝ := ∑ ω, w ω * (pathControl (gridsOf ω) : ℝ)
  (∑ ω, w ω * ((gridsOf ω).sum : ℝ)) = marks + finals ∧
    (∑ ω, w ω * (pathPrep (gridsOf ω) : ℝ)) = 2 * marks + finals ∧
    control = marks ∧
    (∑ ω, w ω * (0 : ℝ)) = 0 ∧
    (∑ ω, w ω * (pathFixed (gridsOf ω) : ℝ)) = 5 * marks + 3 * finals

def JointRecordOracleCostTransport {Ω : Type} [Fintype Ω] (w : Ω → ℝ)
    (gridsOf : Ω → List ℕ) (sourceLedger : Ω → ℕ) : Prop :=
  (∀ ω : Ω, ∃ L : OracleCostLedger,
    PathLedgerTransport (gridsOf ω) L ∧
      L.sourceEvaluations = sourceLedger ω) ∧
    ExpectedLedgerTransport w gridsOf ∧
    ((∑ ω, w ω * ((gridsOf ω).sum : ℝ)) = ∑ ω, w ω * (sourceLedger ω : ℝ))

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
