/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvtDefs
import Qatlib.Concepts.QsvtCore.QsVtMain.CPPPhaseCompiler
import Qatlib.Concepts.QsvtCore.QsVtMain.LengthQSVT
set_option warningAsError false


open Qatlib.Concepts.QsvtCore.QsVtMain

set_option autoImplicit false

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Matrix Polynomial
open Qatlib
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib
open Qatlib
open Qatlib
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
open scoped Classical BigOperators Kronecker

inductive Def15Parity where
  | odd
  | even

def def15Steps (Φ : List ℝ) : Def15Parity → List (CPPStep Bool)
  | .odd => cppCompile (sourceRealFamily Φ)
  | .even => (cppCompile (sourceRealFamily Φ)).map cppSwapData

noncomputable def def15Word {H : Type} [Fintype H] [DecidableEq H]
    (U P Q : Matrix H H ℂ) (Φ : List ℝ) (p : Def15Parity) :
    Matrix (Bool × (Bool × H)) (Bool × (Bool × H)) ℂ :=
  match p with
  | .odd => cppEvaluate U P Q (def15Steps Φ .odd)
  | .even => cppEvaluate U Q P (def15Steps Φ .even)

structure SourceLedger where

  forwardQueries : ℕ

  adjointQueries : ℕ

  projectorNotP : ℕ

  projectorNotQ : ℕ

  phaseMacros : ℕ
  deriving DecidableEq, Repr

def def15Ledger {J : Type} : List (CPPStep J) → SourceLedger
  | [] => ⟨0, 0, 0, 0, 0⟩
  | s :: ss =>
    let c := def15Ledger ss
    match s with
    | .forward => ⟨c.forwardQueries + 1, c.adjointQueries, c.projectorNotP,
        c.projectorNotQ, c.phaseMacros⟩
    | .backward => ⟨c.forwardQueries, c.adjointQueries + 1, c.projectorNotP,
        c.projectorNotQ, c.phaseMacros⟩
    | .projectorP => ⟨c.forwardQueries, c.adjointQueries, c.projectorNotP + 1,
        c.projectorNotQ, c.phaseMacros⟩
    | .projectorQ => ⟨c.forwardQueries, c.adjointQueries, c.projectorNotP,
        c.projectorNotQ + 1, c.phaseMacros⟩
    | .phase _ => ⟨c.forwardQueries, c.adjointQueries, c.projectorNotP,
        c.projectorNotQ, c.phaseMacros + 1⟩

theorem def15Ledger_append {J : Type} (ss ts : List (CPPStep J)) :
    def15Ledger (ss ++ ts) =
      { forwardQueries := (def15Ledger ss).forwardQueries + (def15Ledger ts).forwardQueries
        adjointQueries := (def15Ledger ss).adjointQueries + (def15Ledger ts).adjointQueries
        projectorNotP := (def15Ledger ss).projectorNotP + (def15Ledger ts).projectorNotP
        projectorNotQ := (def15Ledger ss).projectorNotQ + (def15Ledger ts).projectorNotQ
        phaseMacros := (def15Ledger ss).phaseMacros + (def15Ledger ts).phaseMacros } := by
  induction ss with
  | nil => simp [def15Ledger]
  | cons s ss ih => cases s <;> simp [def15Ledger, ih] <;> omega

theorem def15Ledger_swapData {J : Type} (ss : List (CPPStep J)) :
    def15Ledger (ss.map cppSwapData) =
      { forwardQueries := (def15Ledger ss).adjointQueries
        adjointQueries := (def15Ledger ss).forwardQueries
        projectorNotP := (def15Ledger ss).projectorNotP
        projectorNotQ := (def15Ledger ss).projectorNotQ
        phaseMacros := (def15Ledger ss).phaseMacros } := by
  induction ss with
  | nil => simp [def15Ledger]
  | cons s ss ih => cases s <;> simp [def15Ledger, cppSwapData, ih]

theorem def15Ledger_swap {J : Type} (ss : List (CPPStep J)) :
    def15Ledger (ss.map cppSwap) =
      { forwardQueries := (def15Ledger ss).adjointQueries
        adjointQueries := (def15Ledger ss).forwardQueries
        projectorNotP := (def15Ledger ss).projectorNotQ
        projectorNotQ := (def15Ledger ss).projectorNotP
        phaseMacros := (def15Ledger ss).phaseMacros } := by
  induction ss with
  | nil => simp [def15Ledger]
  | cons s ss ih => cases s <;> simp [def15Ledger, cppSwap, ih]

inductive CtrlStep (J : Type) where
  | projectorP
  | projectorQ
  | forward
  | backward
  | phase : (J → ℝ) → CtrlStep J
  | controlledPhase : (J → ℝ) → CtrlStep J
  | multiplyControlledPhase : (J → ℝ) → CtrlStep J
  | controlledForward
  | controlledBackward

def ctrlSwap {J : Type} : CtrlStep J → CtrlStep J
  | .projectorP => .projectorQ
  | .projectorQ => .projectorP
  | .forward => .backward
  | .backward => .forward
  | .phase f => .phase f
  | .controlledPhase f => .controlledPhase f
  | .multiplyControlledPhase f => .multiplyControlledPhase f
  | .controlledForward => .controlledBackward
  | .controlledBackward => .controlledForward

def ctrlSwapData {J : Type} : CtrlStep J → CtrlStep J
  | .forward => .backward
  | .backward => .forward
  | .controlledForward => .controlledBackward
  | .controlledBackward => .controlledForward
  | s => s

def ctrlCompileControlled {J : Type} : List (J → ℝ) → List (CtrlStep J)
  | [] => []
  | f :: fs =>
      [.projectorQ, .controlledPhase f, .projectorQ, .forward] ++
        (ctrlCompileControlled fs).map ctrlSwap

def ctrlCompileMultiplyControlled {J : Type} : List (J → ℝ) → List (CtrlStep J)
  | [] => []
  | f :: fs =>
      [.projectorQ, .multiplyControlledPhase f, .projectorQ, .forward] ++
        (ctrlCompileMultiplyControlled fs).map ctrlSwap

structure CtrlLedger where

  dataQueries : ℕ

  adjointQueries : ℕ

  projectorNots : ℕ

  phaseGates : ℕ

  controlledPhaseGates : ℕ

  multiplyControlledPhaseGates : ℕ

  controlledDataQueries : ℕ

  controlledAdjointQueries : ℕ
  deriving DecidableEq, Repr

def ctrlCounts {J : Type} : List (CtrlStep J) → CtrlLedger
  | [] => ⟨0, 0, 0, 0, 0, 0, 0, 0⟩
  | s :: ss =>
    let c := ctrlCounts ss
    match s with
    | .forward => ⟨c.dataQueries + 1, c.adjointQueries, c.projectorNots,
        c.phaseGates, c.controlledPhaseGates, c.multiplyControlledPhaseGates,
        c.controlledDataQueries, c.controlledAdjointQueries⟩
    | .backward => ⟨c.dataQueries, c.adjointQueries + 1, c.projectorNots,
        c.phaseGates, c.controlledPhaseGates, c.multiplyControlledPhaseGates,
        c.controlledDataQueries, c.controlledAdjointQueries⟩
    | .projectorP => ⟨c.dataQueries, c.adjointQueries, c.projectorNots + 1,
        c.phaseGates, c.controlledPhaseGates, c.multiplyControlledPhaseGates,
        c.controlledDataQueries, c.controlledAdjointQueries⟩
    | .projectorQ => ⟨c.dataQueries, c.adjointQueries, c.projectorNots + 1,
        c.phaseGates, c.controlledPhaseGates, c.multiplyControlledPhaseGates,
        c.controlledDataQueries, c.controlledAdjointQueries⟩
    | .phase _ => ⟨c.dataQueries, c.adjointQueries, c.projectorNots,
        c.phaseGates + 1, c.controlledPhaseGates, c.multiplyControlledPhaseGates,
        c.controlledDataQueries, c.controlledAdjointQueries⟩
    | .controlledPhase _ => ⟨c.dataQueries, c.adjointQueries, c.projectorNots,
        c.phaseGates, c.controlledPhaseGates + 1, c.multiplyControlledPhaseGates,
        c.controlledDataQueries, c.controlledAdjointQueries⟩
    | .multiplyControlledPhase _ => ⟨c.dataQueries, c.adjointQueries,
        c.projectorNots, c.phaseGates, c.controlledPhaseGates,
        c.multiplyControlledPhaseGates + 1, c.controlledDataQueries,
        c.controlledAdjointQueries⟩
    | .controlledForward => ⟨c.dataQueries, c.adjointQueries, c.projectorNots,
        c.phaseGates, c.controlledPhaseGates, c.multiplyControlledPhaseGates,
        c.controlledDataQueries + 1, c.controlledAdjointQueries⟩
    | .controlledBackward => ⟨c.dataQueries, c.adjointQueries, c.projectorNots,
        c.phaseGates, c.controlledPhaseGates, c.multiplyControlledPhaseGates,
        c.controlledDataQueries, c.controlledAdjointQueries + 1⟩

def ctrlSourceFamily (Φ : List ℝ) : List ((Bool × Bool) → ℝ) :=
  Φ.map (fun φ j => if j.1 then -φ else φ)

def ctrlIndex {m : ℕ} (c : Fin m → Bool) : ℕ :=
  List.foldl (fun acc k => 2 * acc + (if c k then 1 else 0)) 0 (List.finRange m)

def mulCtrlTable {m : ℕ} (Φs : List (List ℝ)) (c : Fin m → Bool) : List ℝ :=
  if h : ctrlIndex c < Φs.length then Φs[ctrlIndex c] else []

def mulCtrlSourceFamily {m : ℕ} (Φs : List (List ℝ)) (d : ℕ) :
    List ((Fin m → Bool) × Bool → ℝ) :=
  (List.range d).map (fun i => fun j =>
    if h : i < (mulCtrlTable Φs j.1).length then
      let φ := (mulCtrlTable Φs j.1)[i]
      if j.2 then -φ else φ
    else 0)

theorem ctrlCounts_append {J : Type} (ss ts : List (CtrlStep J)) :
    ctrlCounts (ss ++ ts) =
      { dataQueries := (ctrlCounts ss).dataQueries + (ctrlCounts ts).dataQueries
        adjointQueries := (ctrlCounts ss).adjointQueries + (ctrlCounts ts).adjointQueries
        projectorNots := (ctrlCounts ss).projectorNots + (ctrlCounts ts).projectorNots
        phaseGates := (ctrlCounts ss).phaseGates + (ctrlCounts ts).phaseGates
        controlledPhaseGates :=
          (ctrlCounts ss).controlledPhaseGates + (ctrlCounts ts).controlledPhaseGates
        multiplyControlledPhaseGates :=
          (ctrlCounts ss).multiplyControlledPhaseGates +
            (ctrlCounts ts).multiplyControlledPhaseGates
        controlledDataQueries :=
          (ctrlCounts ss).controlledDataQueries + (ctrlCounts ts).controlledDataQueries
        controlledAdjointQueries :=
          (ctrlCounts ss).controlledAdjointQueries + (ctrlCounts ts).controlledAdjointQueries } := by
  induction ss with
  | nil => simp [ctrlCounts]
  | cons s ss ih => cases s <;> simp [ctrlCounts, ih] <;> omega

theorem ctrlCounts_swap {J : Type} (ss : List (CtrlStep J)) :
    ctrlCounts (ss.map ctrlSwap) =
      { ctrlCounts ss with
        dataQueries := (ctrlCounts ss).adjointQueries
        adjointQueries := (ctrlCounts ss).dataQueries
        controlledDataQueries := (ctrlCounts ss).controlledAdjointQueries
        controlledAdjointQueries := (ctrlCounts ss).controlledDataQueries } := by
  induction ss with
  | nil => simp [ctrlCounts]
  | cons s ss ih => cases s <;> simp [ctrlCounts, ctrlSwap, ih]

theorem ctrlCounts_swapData {J : Type} (ss : List (CtrlStep J)) :
    ctrlCounts (ss.map ctrlSwapData) =
      { ctrlCounts ss with
        dataQueries := (ctrlCounts ss).adjointQueries
        adjointQueries := (ctrlCounts ss).dataQueries
        controlledDataQueries := (ctrlCounts ss).controlledAdjointQueries
        controlledAdjointQueries := (ctrlCounts ss).controlledDataQueries } := by
  induction ss with
  | nil => simp [ctrlCounts]
  | cons s ss ih => cases s <;> simp [ctrlCounts, ctrlSwapData, ih]

def ctrlDef15Steps (Φ : List ℝ) : Def15Parity → List (CtrlStep (Bool × Bool))
  | .odd => ctrlCompileControlled (ctrlSourceFamily Φ)
  | .even => (ctrlCompileControlled (ctrlSourceFamily Φ)).map ctrlSwapData

def mulCtrlDef15Steps (m : ℕ) (Φs : List (List ℝ)) (d : ℕ) :
    Def15Parity → List (CtrlStep ((Fin m → Bool) × Bool))
  | .odd => ctrlCompileMultiplyControlled (mulCtrlSourceFamily (m := m) Φs d)
  | .even =>
      (ctrlCompileMultiplyControlled (mulCtrlSourceFamily (m := m) Φs d)).map ctrlSwapData

end Qatlib.Concepts.QsvtCore.PhaseExistence
