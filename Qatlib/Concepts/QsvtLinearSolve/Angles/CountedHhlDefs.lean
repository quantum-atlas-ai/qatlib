/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL
import Qatlib.Concepts.NativeNumerics.LayeredMean.CountedHHLProgram
import Qatlib.Concepts.HhlAlgorithms.Postselection.RationalHHLNoiseConsumers
import Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointWord
import Qatlib.Concepts.LocalMachine.LocalTransport.ControlledQueryCircuit
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.NativeNumerics.LayeredMean
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.HhlAlgorithms.Postselection.HHLUnknown.Probe

set_option autoImplicit false

namespace Qatlib.Concepts.QsvtLinearSolve.AnglesCore

open Matrix Qatlib
open scoped Classical Matrix.Norms.L2Operator

structure AccessLedger where

  gridSize : ℕ

  prepGates : ℕ

  runGates : ℕ

  forwardQueries : ℕ

  inverseQueries : ℕ

  controlledPrepQueries : ℕ

  amplificationRounds : ℕ

  amplificationGates : ℕ

  freshRetries : ℕ

  workspaceBits : ℕ

  classicalBits : ℕ
  deriving DecidableEq, Repr

def AccessLedger.runQueries (L : AccessLedger) : ℕ :=
  L.forwardQueries + L.inverseQueries

def AccessLedger.totalQueries (L : AccessLedger) : ℕ :=
  (L.runQueries * (L.amplificationRounds + 1) + L.controlledPrepQueries)
    * (L.freshRetries + 1)

def AccessLedger.totalGates (L : AccessLedger) : ℕ :=
  (L.prepGates + L.runGates + L.amplificationRounds * L.amplificationGates)
    * (L.freshRetries + 1)

def countedLedger (D M : ℕ) (prepGates : ℕ) : AccessLedger where
  gridSize := M
  prepGates := prepGates
  runGates := 4 * (M - 1) + 6
  forwardQueries := M - 1
  inverseQueries := M - 1
  controlledPrepQueries := M - 1
  amplificationRounds := 0
  amplificationGates := 0
  freshRetries := 0
  workspaceBits := M + 2 + D
  classicalBits := M

theorem fwdCount_single_gate {I : Type} (U : Matrix I I ℂ) : fwdCount [.gate U] = 0 := by
  simp [fwdCount]

theorem bwdCount_single_gate {I : Type} (U : Matrix I I ℂ) : bwdCount [.gate U] = 0 := by
  simp [bwdCount]

theorem fwdCount_cons {I : Type} (c : AdjointStep I) (cs : List (AdjointStep I)) :
    fwdCount (c :: cs) =
      fwdCount cs + (if (match c with | .forward => true | _ => false) = true then 1 else 0) := by
  cases c <;> simp [fwdCount, Bool.false_eq_true]

theorem bwdCount_cons {I : Type} (c : AdjointStep I) (cs : List (AdjointStep I)) :
    bwdCount (c :: cs) =
      bwdCount cs + (if (match c with | .backward => true | _ => false) = true then 1 else 0) := by
  cases c <;> simp [bwdCount, Bool.false_eq_true]

theorem fwdCount_append {I : Type} (l1 l2 : List (AdjointStep I)) :
    fwdCount (l1 ++ l2) = fwdCount l1 + fwdCount l2 := by
  simp [fwdCount, List.countP_append]

theorem bwdCount_append {I : Type} (l1 l2 : List (AdjointStep I)) :
    bwdCount (l1 ++ l2) = bwdCount l1 + bwdCount l2 := by
  simp [bwdCount, List.countP_append]

theorem fwdCount_map_stepToAdjoint {I : Type} (C : Circuit I) :
    fwdCount (C.map stepToAdjoint) = QueryCount C := by
  induction C with
  | nil => rfl
  | cons s C ih =>
      cases s with
      | gate U =>
          rw [List.map_cons, fwdCount_cons]
          simp [stepToAdjoint, QueryCount]
          exact ih
      | query =>
          rw [List.map_cons, fwdCount_cons]
          simp [stepToAdjoint, QueryCount]
          omega

theorem bwdCount_map_stepToAdjoint {I : Type} (C : Circuit I) :
    bwdCount (C.map stepToAdjoint) = 0 := by
  induction C with
  | nil => rfl
  | cons s C ih =>
      cases s with
      | gate U =>
          rw [List.map_cons, bwdCount_cons]
          simp [stepToAdjoint]
          exact ih
      | query =>
          rw [List.map_cons, bwdCount_cons]
          simp [stepToAdjoint]
          omega

theorem fwdCount_reverse {I : Type} (cs : List (AdjointStep I)) :
    fwdCount cs.reverse = fwdCount cs := by
  induction cs with
  | nil => simp [fwdCount]
  | cons c cs ih =>
      rw [List.reverse_cons, fwdCount_append, ih]
      cases c <;> simp [fwdCount]

theorem bwdCount_reverse {I : Type} (cs : List (AdjointStep I)) :
    bwdCount cs.reverse = bwdCount cs := by
  induction cs with
  | nil => simp [bwdCount]
  | cons c cs ih =>
      rw [List.reverse_cons, bwdCount_append, ih]
      cases c <;> simp [bwdCount]

theorem countedPhaseCircuit_queryCount (D M : ℕ) (hM : 0 < M) :
    QueryCount (countedPhaseCircuit (I := Bool × Fin D) M) = M - 1 := by
  have h := (countedQPEWord_counts D M hM).1
  simp only [countedQPEWord, adjointQueryCount_reverse,
    adjointQueryCount_map_stepToAdjoint] at h
  exact h

theorem countedQPEWord_forward_only (D M : ℕ) (hM : 0 < M) :
    fwdCount (countedQPEWord D M) = M - 1 ∧
      bwdCount (countedQPEWord D M) = 0 := by
  constructor
  · simp only [countedQPEWord, fwdCount_reverse, fwdCount_map_stepToAdjoint,
      countedPhaseCircuit_queryCount D M hM]
  · simp only [countedQPEWord, bwdCount_reverse, bwdCount_map_stepToAdjoint]

theorem countedQPEWord_adjoint_backward_only (D M : ℕ) (hM : 0 < M) :
    fwdCount (adjointCircuit (countedQPEWord D M)) = 0 ∧
      bwdCount (adjointCircuit (countedQPEWord D M)) = M - 1 := by
  rw [fwdCount_adjointCircuit, bwdCount_adjointCircuit]
  have hq := countedQPEWord_forward_only D M hM
  rw [hq.1, hq.2]
  exact ⟨rfl, rfl⟩

theorem countedHHLWord_forward_backward_split {D : ℕ} (M : ℕ) (c : ℝ) (B : Operator D)
    (hM : 0 < M) :
    fwdCount (countedHHLWord (D := D) M c B) = M - 1 ∧
      bwdCount (countedHHLWord (D := D) M c B) = M - 1 := by
  have hq := countedQPEWord_forward_only D M hM
  have hb := countedQPEWord_adjoint_backward_only D M hM
  constructor
  · simp only [countedHHLWord, fwdCount_append]
    rw [hb.1, hq.1, fwdCount_single_gate, fwdCount_single_gate]
    omega
  · simp only [countedHHLWord, bwdCount_append]
    rw [hb.2, hq.2, bwdCount_single_gate, bwdCount_single_gate]
    omega

theorem countedLedger_totalGates (D M : ℕ) (tB : ℕ) :
    (countedLedger D M tB).totalGates = tB + 4 * (M - 1) + 6 := by
  simp [countedLedger, AccessLedger.totalGates]
  omega

theorem countedLedger_totalQueries (D M : ℕ) (tB : ℕ) :
    (countedLedger D M tB).totalQueries = 2 * (M - 1) + (M - 1) := by
  simp [countedLedger, AccessLedger.totalQueries, AccessLedger.runQueries]
  omega

theorem countedLedger_charges_input_preparation {D : ℕ} (M : ℕ) (c : ℝ)
    (B : Operator D) (hM : 0 < M) (tB : ℕ) :
    (countedLedger D M tB).totalGates
      = tB + adjointGateCount (countedHHLWord (D := D) M c B) := by
  rw [countedHHLWord_gateCount M c B hM]
  simp [countedLedger, AccessLedger.totalGates]

def freshRetryLedger (tB g r q : ℕ) : AccessLedger where
  gridSize := 0
  prepGates := tB
  runGates := g
  forwardQueries := q
  inverseQueries := 0
  controlledPrepQueries := 0
  amplificationRounds := 0
  amplificationGates := r
  freshRetries := 1
  workspaceBits := 0
  classicalBits := 0

def amplificationLedger (tB g r q : ℕ) : AccessLedger where
  gridSize := 0
  prepGates := tB
  runGates := g
  forwardQueries := q
  inverseQueries := 0
  controlledPrepQueries := 0
  amplificationRounds := 1
  amplificationGates := r
  freshRetries := 0
  workspaceBits := 0
  classicalBits := 0

theorem fresh_retry_is_not_amplification (tB g r q : ℕ) :
    (freshRetryLedger tB g r q).totalQueries
        = (amplificationLedger tB g r q).totalQueries ∧
      (freshRetryLedger tB g r q).totalGates = 2 * (tB + g) ∧
      (amplificationLedger tB g r q).totalGates = tB + g + r := by
  dsimp [freshRetryLedger, amplificationLedger, AccessLedger.totalQueries,
    AccessLedger.totalGates, AccessLedger.runQueries]
  omega

theorem countedHHLWord_queryCount_ge_accuracy_resolution (M : ℕ) (hM : 0 < M)
    {ε : ℝ} (hε : 0 < ε) (hres : (1 : ℝ) / (M : ℝ) ≤ ε) :
    ((2 * (M - 1) : ℕ) : ℝ) ≥ 2 / ε - 2 := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have h1 : (1 : ℝ) ≤ ε * (M : ℝ) := (div_le_iff₀ hMpos).mp hres
  have hMinv : (1 : ℝ) / ε ≤ (M : ℝ) :=
    (div_le_iff₀ hε).mpr (by simpa [mul_comm] using! h1)
  have h3 : (2 : ℝ) / ε = 2 * ((1 : ℝ) / ε) := by ring
  have h2 : (2 : ℝ) * (M : ℝ) ≥ 2 / ε := by linarith
  have hcast : ((2 * (M - 1) : ℕ) : ℝ) = (2 : ℝ) * (M : ℝ) - 2 := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : (1 : ℕ) ≤ M), Nat.cast_one]
    ring
  rw [hcast]
  linarith

theorem controlled_preparation_is_unitary {D M : ℕ} {B : Operator D}
    (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    controlOracle (countedHHLPrepMain (D := D) (M := M) B)
      ∈ Matrix.unitaryGroup (Bool × (Fin M × (Bool × Fin D))) ℂ :=
  controlOracle_unitary (countedHHLPrepMain_unitary hB)

end Qatlib.Concepts.QsvtLinearSolve.AnglesCore
