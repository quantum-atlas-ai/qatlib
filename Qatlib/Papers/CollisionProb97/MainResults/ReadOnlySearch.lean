/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionProb97.MainResults.ReadOnlyTable
import Qatlib.Papers.CollisionProb97.MainResults.ActualSearchProtocol
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib.Concepts.AmplitudeSearch.InterruptMin

namespace Qatlib.Papers.CollisionProb97.MainResults.ReadOnlySearch
variable {S X R : Type} [Fintype S] [DecidableEq S] [Fintype X] [DecidableEq X]
    [AddCommGroup R] [Fintype R] [DecidableEq R]

def searchState (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (j : ℕ) :
    QState ((X × R) × ReadOnlyTable.Memory (X := S) (R := R) k) :=
  ApplyGate (evaluate (ReadOnlyTable.oracle F k) (ReadOnlyTable.compile K k (SearchCircuit X j)))
    (TensorState (TensorState (Uniform X) (Qatlib.Foundations.PureStateMath.Ket 0))
      (Qatlib.Foundations.PureStateMath.Ket L))

theorem searchState_eq (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (j : ℕ) :
    searchState F K L j = TensorState (ActualSearch.searchState F K (ReadOnlyTable.values L) j)
      (Qatlib.Foundations.PureStateMath.Ket L) := by
  rw [searchState, ReadOnlyTable.compile_run, ActualSearch.searchState, PhaseCompile.compile_run]

theorem searchState_born (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (j : ℕ) (x : X) :
    (∑ z : R, ∑ M : ReadOnlyTable.Memory (X := S) (R := R) k,
      BornProb (searchState F K L j) ((x, z), M)) =
      BornProb (SearchState (ActualSearch.marked F K (ReadOnlyTable.values L)) j) x := by
  rw [searchState_eq, ActualSearch.searchState_eq]
  simp [bornProb_tensorState, bornProb_ket]

def verificationState (F : X → R) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (x : X) :
    QState ((X × R) × ReadOnlyTable.Memory (X := S) (R := R) k) :=
  Run (ReadOnlyTable.oracle F k) [Step.query]
    (Qatlib.Foundations.PureStateMath.Ket ((x, 0), L))

theorem verificationState_eq (F : X → R) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (x : X) :
    verificationState F L x = Qatlib.Foundations.PureStateMath.Ket ((x, F x), L) := by
  rw [verificationState, run_query, run_nil, ReadOnlyTable.oracle_ket]
  simp

def verificationMass (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (x : X) : ℝ :=
  MeasureProb (verificationState F L x)
    (Finset.univ.filter fun p => p.1.1 ∉ K ∧ p.1.2 ∈ ReadOnlyTable.values p.2)

theorem verificationMass_eq (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (x : X) :
    verificationMass F K L x = ActualSearch.verificationMass F K (ReadOnlyTable.values L) x := by
  rw [verificationMass, verificationState_eq, ActualSearch.verificationMass_eq]
  simp [MeasureProb, bornProb_ket, ActualSearch.marked]

def checkedOutput (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (j : ℕ) (x : X) : ℝ :=
  (∑ z : R, ∑ M : ReadOnlyTable.Memory (X := S) (R := R) k,
    BornProb (searchState F K L j) ((x, z), M)) * verificationMass F K L x

theorem checkedOutput_eq (hN : 0 < Fintype.card X) (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (j : ℕ) (x : X) :
    checkedOutput F K L j x = CheckedOutputMass (ActualSearch.marked F K (ReadOnlyTable.values L)) j x := by
  rw [checkedOutput, searchState_born, verificationMass_eq]
  rw [← ActualSearch.searchState_born F K (ReadOnlyTable.values L) j x]
  exact ActualSearch.checkedOutput_eq hN F K (ReadOnlyTable.values L) j x

def checkedReject (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (j : ℕ) : ℝ :=
  ∑ x : X, (∑ z : R, ∑ M : ReadOnlyTable.Memory (X := S) (R := R) k,
    BornProb (searchState F K L j) ((x, z), M)) * (1 - verificationMass F K L x)

theorem checkedReject_eq (hN : 0 < Fintype.card X) (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (j : ℕ) :
    checkedReject F K L j = CheckedRejectMass (ActualSearch.marked F K (ReadOnlyTable.values L)) j := by
  rw [checkedReject, ← ActualSearch.checkedReject_eq hN F K (ReadOnlyTable.values L) j]
  unfold ActualSearch.checkedReject
  simp only [searchState_born, verificationMass_eq, ActualSearch.searchState_born]

def attemptMass (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (m : ℕ) (a : Fin m × Option X) : ℝ :=
  (match a.2 with | none => checkedReject F K L a.1.val | some x => checkedOutput F K L a.1.val x) / m

theorem attemptMass_eq (hN : 0 < Fintype.card X) (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (m : ℕ) (a : Fin m × Option X) :
    attemptMass F K L m a = AttemptMass (ActualSearch.marked F K (ReadOnlyTable.values L)) m a := by
  unfold attemptMass AttemptMass
  cases a.2 <;> simp only [checkedReject_eq hN, checkedOutput_eq hN]

def terminalMass (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (sizes : ℕ → ℕ) (x : TerminalTrace X sizes) : ℝ :=
  (∏ i : Fin x.1, attemptMass F K L (sizes i.val) (x.2.1 i, none)) *
    attemptMass F K L (sizes x.1) (x.2.2.1, some x.2.2.2)

theorem terminalMass_eq (hN : 0 < Fintype.card X) (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (sizes : ℕ → ℕ) (x : TerminalTrace X sizes) :
    terminalMass F K L sizes x = TerminalMass (ActualSearch.marked F K (ReadOnlyTable.values L)) sizes x := by
  simp only [terminalMass, attemptMass_eq hN, TerminalMass, TerminalStageMass, FailureHistoryMass]

def attemptQueries (K : Finset X) (k j : ℕ) : ℕ :=
  adjointQueryCount (ReadOnlyTable.compile (S := S) (R := R) K k (SearchCircuit X j)) +
    QueryCount ([Step.query] : Circuit ((X × R) × ReadOnlyTable.Memory (X := S) (R := R) k))

omit [AddCommGroup R] [Fintype S] [Fintype R] in

theorem attemptQueries_eq (K : Finset X) (k j : ℕ) : attemptQueries (S := S) (R := R) K k j = 2*j + 1 := by
  rw [attemptQueries, ReadOnlyTable.compile_queries, queryCount_groverCircuit]
  rfl

def terminalQueries (K : Finset X) (k : ℕ) (sizes : ℕ → ℕ) (x : TerminalTrace X sizes) : ℕ :=
  (∑ i : Fin x.1, attemptQueries (S := S) (R := R) K k (x.2.1 i).val) +
    attemptQueries (S := S) (R := R) K k x.2.2.1.val

omit [AddCommGroup R] [Fintype S] [Fintype R] in

theorem terminalQueries_eq (K : Finset X) (k : ℕ) (sizes : ℕ → ℕ) (x : TerminalTrace X sizes) :
    terminalQueries (S := S) (R := R) K k sizes x = SourceLookupClock sizes x := by
  simp only [terminalQueries, attemptQueries_eq, SourceLookupClock, TerminalCost,
      TerminalIterations, HistoryIterations]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]
  omega

theorem terminal_law (hN : 0 < Fintype.card X) (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3)
    (hA : 0 < (ActualSearch.marked F K (ReadOnlyTable.values L)).card) :
    HasSum (terminalMass F K L (SourceSizes (Fintype.card X) l)) 1 ∧
    ∀ x, 0 ≤ terminalMass F K L (SourceSizes (Fintype.card X) l) x ∧
      (TerminalOutput x ∉ ActualSearch.marked F K (ReadOnlyTable.values L) →
        terminalMass F K L (SourceSizes (Fintype.card X) l) x = 0) := by
  have he : terminalMass F K L (SourceSizes (Fintype.card X) l) =
      TerminalMass (ActualSearch.marked F K (ReadOnlyTable.values L)) (SourceSizes (Fintype.card X) l) := by
    funext x
    exact terminalMass_eq hN F K L _ x
  rw [he]
  exact search_source_terminal_law_nonempty l hl hl4
      (ActualSearch.marked F K (ReadOnlyTable.values L)) hA

theorem expected_queries (hN : 0 < Fintype.card X) (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3)
    (hA : 0 < (ActualSearch.marked F K (ReadOnlyTable.values L)).card) :
    ∃ q : ℝ, HasSum (fun x : TerminalTrace X (SourceSizes (Fintype.card X) l) =>
      terminalMass F K L _ x * (terminalQueries (S := S) (R := R) K k _ x : ℝ)) q ∧
      0 ≤ q ∧ q ≤ (1 + 4*SourcePhaseConstant l) *
        Real.sqrt ((Fintype.card X : ℝ) / (ActualSearch.marked F K (ReadOnlyTable.values L)).card) := by
  simpa only [terminalMass_eq hN, terminalQueries_eq] using
    search_source_terminal_lookup_cost l hl hl4 (ActualSearch.marked F K (ReadOnlyTable.values L)) hA

end Qatlib.Papers.CollisionProb97.MainResults.ReadOnlySearch
