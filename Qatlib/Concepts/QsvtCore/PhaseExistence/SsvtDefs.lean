/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvtDefs
import Qatlib.Concepts.QsvtCore.QsVtMain.CPPPhaseCompiler
import Qatlib.Concepts.QsvtCore.QsVtMain.LengthQSVT

/-!
# Definitions of parity-selected transformation words

`Def15Parity` selects the two compiled forms of the singular value transformation word, and
`def15Word` supplies their matrix interpretation. `SourceLedger` and `def15Ledger` count data
queries, projector-NOT steps, and phase macros.

`CtrlStep` extends the symbolic language with controlled and multiply controlled phase
operations. The module defines phase tables, controlled compilers, and `CtrlLedger`, and proves
additivity and swap identities for their resource counts. See [GilyenSuLowWiebe2019].

## Main statements

* `def15Steps` and `def15Word`: define the parity-selected compiled words.
* `def15Ledger_append`: add resource counts under concatenation.
* `ctrlDef15Steps` and `mulCtrlDef15Steps`: define controlled variants.
* `ctrlCounts_append`: add controlled resource counts under concatenation.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

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

/-- The odd and even parity tags selecting the two Definition 15 compilation conventions. -/
inductive Def15Parity where
  | odd
  | even

/-- The compiled source phase family for odd parity, or the same list with data-query directions
interchanged for even parity. -/
def def15Steps (Φ : List ℝ) : Def15Parity → List (CPPStep Bool)
  | .odd => cppCompile (sourceRealFamily Φ)
  | .even => (cppCompile (sourceRealFamily Φ)).map cppSwapData

/-- The matrix interpretation of the parity-selected step list, using projectors `P`, `Q` for
odd parity and `Q`, `P` for even parity. -/
noncomputable def def15Word {H : Type} [Fintype H] [DecidableEq H]
    (U P Q : Matrix H H ℂ) (Φ : List ℝ) (p : Def15Parity) :
    Matrix (Bool × (Bool × H)) (Bool × (Bool × H)) ℂ :=
  match p with
  | .odd => cppEvaluate U P Q (def15Steps Φ .odd)
  | .even => cppEvaluate U Q P (def15Steps Φ .even)

/-- A record of forward and adjoint data queries, separate `P` and `Q` projector-NOT counts, and
phase-macro counts. -/
structure SourceLedger where

  forwardQueries : ℕ

  adjointQueries : ℕ

  projectorNotP : ℕ

  projectorNotQ : ℕ

  phaseMacros : ℕ
  deriving DecidableEq, Repr

/-- Count each type of data query, projector-NOT step, and phase macro in a `CPPStep` list. -/
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

/-- Concatenating step lists adds all five components of their source resource ledgers. -/
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

/-- Interchanging data-query directions swaps the forward and adjoint counts and preserves
projector and phase counts. -/
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

/-- Applying `cppSwap` exchanges both data-query directions and the two projector counts, while
preserving the phase count. -/
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

/-- The symbolic projector, data-query, phase, controlled-phase, multiply controlled phase, and
controlled data-query operations. -/
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

/-- Interchange the two projectors and both ordinary and controlled data-query directions,
preserving all phase operations. -/
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

/-- Interchange ordinary and controlled data-query directions while preserving projector and
phase operations. -/
def ctrlSwapData {J : Type} : CtrlStep J → CtrlStep J
  | .forward => .backward
  | .backward => .forward
  | .controlledForward => .controlledBackward
  | .controlledBackward => .controlledForward
  | s => s

/-- Compile a phase family using controlled phases between two projector steps and alternating
data-query directions. -/
def ctrlCompileControlled {J : Type} : List (J → ℝ) → List (CtrlStep J)
  | [] => []
  | f :: fs =>
      [.projectorQ, .controlledPhase f, .projectorQ, .forward] ++
        (ctrlCompileControlled fs).map ctrlSwap

/-- Compile a phase family using multiply controlled phases between two projector steps and
alternating data-query directions. -/
def ctrlCompileMultiplyControlled {J : Type} : List (J → ℝ) → List (CtrlStep J)
  | [] => []
  | f :: fs =>
      [.projectorQ, .multiplyControlledPhase f, .projectorQ, .forward] ++
        (ctrlCompileMultiplyControlled fs).map ctrlSwap

/-- A record of ordinary and controlled forward and adjoint queries, total projector-NOT steps,
and ordinary, controlled, and multiply controlled phase counts. -/
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

/-- Compute the eight resource counts of a list of controlled symbolic steps. -/
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

/-- The phase family assigning each angle or its negative according to the first Boolean
coordinate. -/
def ctrlSourceFamily (Φ : List ℝ) : List ((Bool × Bool) → ℝ) :=
  Φ.map (fun φ j => if j.1 then -φ else φ)

/-- Interpret a Boolean control assignment as a natural binary index by folding over
`List.finRange m`. -/
def ctrlIndex {m : ℕ} (c : Fin m → Bool) : ℕ :=
  List.foldl (fun acc k => 2 * acc + (if c k then 1 else 0)) 0 (List.finRange m)

/-- Select the phase list indexed by the Boolean control assignment, using the empty list when
its index is out of range. -/
def mulCtrlTable {m : ℕ} (Φs : List (List ℝ)) (c : Fin m → Bool) : List ℝ :=
  if h : ctrlIndex c < Φs.length then Φs[ctrlIndex c] else []

/-- The length-`d` phase family selected by the control table, negated according to the final
Boolean coordinate and padded by zero beyond each selected list. -/
def mulCtrlSourceFamily {m : ℕ} (Φs : List (List ℝ)) (d : ℕ) :
    List ((Fin m → Bool) × Bool → ℝ) :=
  (List.range d).map (fun i => fun j =>
    if h : i < (mulCtrlTable Φs j.1).length then
      let φ := (mulCtrlTable Φs j.1)[i]
      if j.2 then -φ else φ
    else 0)

/-- Concatenating controlled step lists adds all eight components of their resource ledgers. -/
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

/-- Applying `ctrlSwap` exchanges the ordinary and controlled forward and adjoint counts and
preserves all other ledger fields. -/
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

/-- Applying `ctrlSwapData` exchanges the ordinary and controlled forward and adjoint counts and
preserves all other ledger fields. -/
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

/-- The parity-selected controlled compilation of `ctrlSourceFamily Φ`, with data-query
directions interchanged for even parity. -/
def ctrlDef15Steps (Φ : List ℝ) : Def15Parity → List (CtrlStep (Bool × Bool))
  | .odd => ctrlCompileControlled (ctrlSourceFamily Φ)
  | .even => (ctrlCompileControlled (ctrlSourceFamily Φ)).map ctrlSwapData

/-- The parity-selected multiply controlled compilation of the length-`d` source family selected
by an `m`-bit control table. -/
def mulCtrlDef15Steps (m : ℕ) (Φs : List (List ℝ)) (d : ℕ) :
    Def15Parity → List (CtrlStep ((Fin m → Bool) × Bool))
  | .odd => ctrlCompileMultiplyControlled (mulCtrlSourceFamily (m := m) Φs d)
  | .even =>
      (ctrlCompileMultiplyControlled (mulCtrlSourceFamily (m := m) Φs d)).map ctrlSwapData

end Qatlib.Concepts.QsvtCore.PhaseExistence
