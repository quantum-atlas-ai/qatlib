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

/-!
# Access ledgers for counted HHL circuits

This module defines `AccessLedger` to account for preparation, forward and inverse queries,
amplification, retries, and storage. It derives exact counts for the counted HHL construction
motivated by [HarrowHassidimLloyd2009] and compares retry and amplification ledgers.

## Main statements

* `countedHHLWord_forward_backward_split`: Equal forward and inverse query counts.
* `countedLedger_charges_input_preparation`: The gate total includes the input preparation cost.
* `fresh_retry_is_not_amplification`: Equal query totals can accompany different gate totals.

## References

* [Harrow, Hassidim and Lloyd, 2009][HarrowHassidimLloyd2009]
-/

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

/-- Resource data for a counted linear-system routine, including preparation and execution
gates, oracle accesses, amplification, retries, and storage. -/
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

/-- The sum of the forward and inverse query counts for one run. -/
def AccessLedger.runQueries (L : AccessLedger) : ℕ :=
  L.forwardQueries + L.inverseQueries

/-- The total query charge after amplification rounds, controlled preparation, and fresh
retries. -/
def AccessLedger.totalQueries (L : AccessLedger) : ℕ :=
  (L.runQueries * (L.amplificationRounds + 1) + L.controlledPrepQueries)
    * (L.freshRetries + 1)

/-- The preparation, run, and amplification gate charge multiplied by the number of fresh
attempts. -/
def AccessLedger.totalGates (L : AccessLedger) : ℕ :=
  (L.prepGates + L.runGates + L.amplificationRounds * L.amplificationGates)
    * (L.freshRetries + 1)

/-- The explicit HHL resource ledger with grid size `M`, preparation cost `prepGates`, and no
amplification or retries. -/
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

/-- A singleton fixed-gate word contains no forward oracle queries. -/
theorem fwdCount_single_gate {I : Type} (U : Matrix I I ℂ) : fwdCount [.gate U] = 0 := by
  simp [fwdCount]

/-- A singleton fixed-gate word contains no backward oracle queries. -/
theorem bwdCount_single_gate {I : Type} (U : Matrix I I ℂ) : bwdCount [.gate U] = 0 := by
  simp [bwdCount]

/-- Prepending an instruction increases the forward count exactly when the instruction is a
forward query. -/
theorem fwdCount_cons {I : Type} (c : AdjointStep I) (cs : List (AdjointStep I)) :
    fwdCount (c :: cs) =
      fwdCount cs + (if (match c with | .forward => true | _ => false) = true then 1 else 0) := by
  cases c <;> simp [fwdCount, Bool.false_eq_true]

/-- Prepending an instruction increases the backward count exactly when the instruction is a
backward query. -/
theorem bwdCount_cons {I : Type} (c : AdjointStep I) (cs : List (AdjointStep I)) :
    bwdCount (c :: cs) =
      bwdCount cs + (if (match c with | .backward => true | _ => false) = true then 1 else 0) := by
  cases c <;> simp [bwdCount, Bool.false_eq_true]

/-- Forward query counts add under concatenation. -/
theorem fwdCount_append {I : Type} (l1 l2 : List (AdjointStep I)) :
    fwdCount (l1 ++ l2) = fwdCount l1 + fwdCount l2 := by
  simp [fwdCount, List.countP_append]

/-- Backward query counts add under concatenation. -/
theorem bwdCount_append {I : Type} (l1 l2 : List (AdjointStep I)) :
    bwdCount (l1 ++ l2) = bwdCount l1 + bwdCount l2 := by
  simp [bwdCount, List.countP_append]

/-- Embedding an ordinary circuit into adjoint syntax preserves its query count as the forward
count. -/
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

/-- Embedding an ordinary circuit into adjoint syntax introduces no backward queries. -/
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

/-- Reversing instruction order preserves the forward query count. -/
theorem fwdCount_reverse {I : Type} (cs : List (AdjointStep I)) :
    fwdCount cs.reverse = fwdCount cs := by
  induction cs with
  | nil => simp [fwdCount]
  | cons c cs ih =>
      rw [List.reverse_cons, fwdCount_append, ih]
      cases c <;> simp [fwdCount]

/-- Reversing instruction order preserves the backward query count. -/
theorem bwdCount_reverse {I : Type} (cs : List (AdjointStep I)) :
    bwdCount cs.reverse = bwdCount cs := by
  induction cs with
  | nil => simp [bwdCount]
  | cons c cs ih =>
      rw [List.reverse_cons, bwdCount_append, ih]
      cases c <;> simp [bwdCount]

/-- For positive grid size `M`, the counted phase circuit uses `M - 1` queries. -/
theorem countedPhaseCircuit_queryCount (D M : ℕ) (hM : 0 < M) :
    QueryCount (countedPhaseCircuit (I := Bool × Fin D) M) = M - 1 := by
  have h := (countedQPEWord_counts D M hM).1
  simp only [countedQPEWord, adjointQueryCount_reverse,
    adjointQueryCount_map_stepToAdjoint] at h
  exact h

/-- For positive `M`, the counted phase-estimation word uses `M - 1` forward queries and no
backward queries. -/
theorem countedQPEWord_forward_only (D M : ℕ) (hM : 0 < M) :
    fwdCount (countedQPEWord D M) = M - 1 ∧
      bwdCount (countedQPEWord D M) = 0 := by
  constructor
  · simp only [countedQPEWord, fwdCount_reverse, fwdCount_map_stepToAdjoint,
      countedPhaseCircuit_queryCount D M hM]
  · simp only [countedQPEWord, bwdCount_reverse, bwdCount_map_stepToAdjoint]

/-- For positive `M`, the adjoint phase-estimation word uses no forward queries and `M - 1`
backward queries. -/
theorem countedQPEWord_adjoint_backward_only (D M : ℕ) (hM : 0 < M) :
    fwdCount (adjointCircuit (countedQPEWord D M)) = 0 ∧
      bwdCount (adjointCircuit (countedQPEWord D M)) = M - 1 := by
  rw [fwdCount_adjointCircuit, bwdCount_adjointCircuit]
  have hq := countedQPEWord_forward_only D M hM
  rw [hq.1, hq.2]
  exact ⟨rfl, rfl⟩

/-- For positive `M`, the counted HHL word has exactly `M - 1` forward and `M - 1` backward
queries. -/
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

/-- The counted HHL ledger has total gate charge `tB + 4 * (M - 1) + 6`. -/
theorem countedLedger_totalGates (D M : ℕ) (tB : ℕ) :
    (countedLedger D M tB).totalGates = tB + 4 * (M - 1) + 6 := by
  simp [countedLedger, AccessLedger.totalGates]
  omega

/-- The counted HHL ledger charges `2 * (M - 1) + (M - 1)` total queries, including controlled
preparation. -/
theorem countedLedger_totalQueries (D M : ℕ) (tB : ℕ) :
    (countedLedger D M tB).totalQueries = 2 * (M - 1) + (M - 1) := by
  simp [countedLedger, AccessLedger.totalQueries, AccessLedger.runQueries]
  omega

/-- For positive `M`, the ledger's total gates equal the input preparation cost plus the actual
counted HHL word's gate count. -/
theorem countedLedger_charges_input_preparation {D : ℕ} (M : ℕ) (c : ℝ)
    (B : Operator D) (hM : 0 < M) (tB : ℕ) :
    (countedLedger D M tB).totalGates
      = tB + adjointGateCount (countedHHLWord (D := D) M c B) := by
  rw [countedHHLWord_gateCount M c B hM]
  simp [countedLedger, AccessLedger.totalGates]

/-- A ledger charging two fresh runs, each with preparation cost `tB`, run cost `g`, and `q`
forward queries. -/
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

/-- A ledger charging one preparation, one run, and one amplification round with gate cost `r`. -/
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

/-- The fresh-retry and amplification ledgers have equal query totals, while their gate totals
are respectively `2 * (tB + g)` and `tB + g + r`. -/
theorem fresh_retry_is_not_amplification (tB g r q : ℕ) :
    (freshRetryLedger tB g r q).totalQueries
        = (amplificationLedger tB g r q).totalQueries ∧
      (freshRetryLedger tB g r q).totalGates = 2 * (tB + g) ∧
      (amplificationLedger tB g r q).totalGates = tB + g + r := by
  dsimp [freshRetryLedger, amplificationLedger, AccessLedger.totalQueries,
    AccessLedger.totalGates, AccessLedger.runQueries]
  omega

/-- If the positive grid resolves accuracy `ε` through `1 / M ≤ ε`, then `2 * (M - 1) ≥ 2 / ε -
2`. -/
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

/-- A unitary input preparation matrix induces a unitary controlled counted HHL preparation. -/
theorem controlled_preparation_is_unitary {D M : ℕ} {B : Operator D}
    (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    controlOracle (countedHHLPrepMain (D := D) (M := M) B)
      ∈ Matrix.unitaryGroup (Bool × (Fin M × (Bool × Fin D))) ℂ :=
  controlOracle_unitary (countedHHLPrepMain_unitary hB)

end Qatlib.Concepts.QsvtLinearSolve.AnglesCore
