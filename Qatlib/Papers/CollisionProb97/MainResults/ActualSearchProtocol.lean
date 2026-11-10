/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionProb97.MainResults.ActualPhaseProgram
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
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Papers.CollisionProb97.MainResults.ActualSearch
variable {X R : Type} [Fintype X] [DecidableEq X]
    [AddCommGroup R] [Fintype R] [DecidableEq R]

def marked (F : X → R) (K : Finset X) (T : Finset R) : Finset X :=
  Finset.univ.filter fun x => x ∉ K ∧ F x ∈ T

omit [AddCommGroup R] [Fintype R] in

theorem table_phase_eq (F : X → R) (K : Finset X) (T : Finset R) :
    Matrix.diagonal (fun x => PhaseCompile.tableSign K T x (F x)) = SetOracle (marked F K T) := by
  simp only [SetOracle, PhaseOracle]
  congr 1
  funext x
  simp [PhaseCompile.tableSign, marked]

def searchState (F : X → R) (K : Finset X) (T : Finset R) (j : ℕ) : QState (X × R) :=
  ApplyGate (evaluate (AddOracle F) (PhaseCompile.compile K T (SearchCircuit X j)))
    (TensorState (Uniform X) (Ket 0))

theorem searchState_eq (F : X → R) (K : Finset X) (T : Finset R) (j : ℕ) :
    searchState F K T j = TensorState (SearchState (marked F K T) j) (Ket 0) := by
  rw [searchState, PhaseCompile.compile_run, table_phase_eq]
  rfl

theorem searchState_born (F : X → R) (K : Finset X) (T : Finset R) (j : ℕ) (x : X) :
    (∑ z : R, BornProb (searchState F K T j) (x, z)) = BornProb (SearchState (marked F K T) j) x := by
  rw [searchState_eq]
  simp [bornProb_tensorState, bornProb_ket]

def verifyState (F : X → R) (x : X) : QState (X × R) :=
  Run (AddOracle F) [Step.query] (Ket (x, 0))

theorem verifyState_eq (F : X → R) (x : X) : verifyState F x = Ket (x, F x) := by
  simp [verifyState, applyGate_addOracle_ket]

def verificationMass (F : X → R) (K : Finset X) (T : Finset R) (x : X) : ℝ :=
  MeasureProb (verifyState F x) (Finset.univ.filter fun p => p.1 ∉ K ∧ p.2 ∈ T)

theorem verificationMass_eq (F : X → R) (K : Finset X) (T : Finset R) (x : X) :
    verificationMass F K T x = if x ∈ marked F K T then 1 else 0 := by
  rw [verificationMass, verifyState_eq]
  simp [MeasureProb, bornProb_ket, marked]

def checkedOutput (F : X → R) (K : Finset X) (T : Finset R) (j : ℕ) (x : X) : ℝ :=
  (∑ z : R, BornProb (searchState F K T j) (x, z)) * verificationMass F K T x

theorem checkedOutput_eq (hN : 0 < Fintype.card X) (F : X → R) (K : Finset X) (T : Finset R)
    (j : ℕ) (x : X) : checkedOutput F K T j x = CheckedOutputMass (marked F K T) j x := by
  rw [checkedOutput, searchState_born, verificationMass_eq, (search_checked_attempt hN _ j).2.1]
  split_ifs <;> simp

def checkedReject (F : X → R) (K : Finset X) (T : Finset R) (j : ℕ) : ℝ :=
  ∑ x : X, (∑ z : R, BornProb (searchState F K T j) (x, z)) * (1 - verificationMass F K T x)

theorem checkedReject_eq (hN : 0 < Fintype.card X) (F : X → R) (K : Finset X) (T : Finset R)
    (j : ℕ) : checkedReject F K T j = CheckedRejectMass (marked F K T) j := by
  have hsum := (search_checked_attempt hN (marked F K T) j).2.2.2.1
  have hs : ∑ x : X, checkedOutput F K T j x =
      ∑ x : X, CheckedOutputMass (marked F K T) j x := by
    apply Finset.sum_congr rfl
    intro x _
    exact checkedOutput_eq hN F K T j x
  have hn := (search_circuit_laws hN (marked F K T) j).2.2.2
  have he : checkedReject F K T j + ∑ x : X, checkedOutput F K T j x = 1 := by
    simp only [checkedReject, checkedOutput, ← Finset.sum_add_distrib]
    simp_rw [searchState_born]
    have hz (x : X) : BornProb (SearchState (marked F K T) j) x * (1 - verificationMass F K T x) +
        BornProb (SearchState (marked F K T) j) x * verificationMass F K T x =
        BornProb (SearchState (marked F K T) j) x := by ring
    simp_rw [hz]
    exact hn
  linarith

def attemptMass (F : X → R) (K : Finset X) (T : Finset R) (m : ℕ) (a : Fin m × Option X) : ℝ :=
  (match a.2 with | none => checkedReject F K T a.1.val | some x => checkedOutput F K T a.1.val x) / m

theorem attemptMass_eq (hN : 0 < Fintype.card X) (F : X → R) (K : Finset X) (T : Finset R)
    (m : ℕ) (a : Fin m × Option X) : attemptMass F K T m a = AttemptMass (marked F K T) m a := by
  unfold attemptMass AttemptMass
  cases a.2 <;> simp only [checkedReject_eq hN, checkedOutput_eq hN]

def terminalMass (F : X → R) (K : Finset X) (T : Finset R) (sizes : ℕ → ℕ)
    (x : TerminalTrace X sizes) : ℝ :=
  (∏ i : Fin x.1, attemptMass F K T (sizes i.val) (x.2.1 i, none)) *
    attemptMass F K T (sizes x.1) (x.2.2.1, some x.2.2.2)

theorem terminalMass_eq (hN : 0 < Fintype.card X) (F : X → R) (K : Finset X) (T : Finset R)
    (sizes : ℕ → ℕ) (x : TerminalTrace X sizes) :
    terminalMass F K T sizes x = TerminalMass (marked F K T) sizes x := by
  simp only [terminalMass, attemptMass_eq hN, TerminalMass, TerminalStageMass, FailureHistoryMass]

def attemptQueries (K : Finset X) (T : Finset R) (j : ℕ) : ℕ :=
  adjointQueryCount (PhaseCompile.compile K T (SearchCircuit X j)) +
    QueryCount ([Step.query] : Circuit (X × R))

omit [AddCommGroup R] [Fintype R] in

theorem attemptQueries_eq (K : Finset X) (T : Finset R) (j : ℕ) :
    attemptQueries K T j = 2*j + 1 := by
  rw [attemptQueries, PhaseCompile.compile_queries, queryCount_groverCircuit]
  rfl

def terminalQueries (K : Finset X) (T : Finset R) (sizes : ℕ → ℕ)
    (x : TerminalTrace X sizes) : ℕ :=
  (∑ i : Fin x.1, attemptQueries K T (x.2.1 i).val) + attemptQueries K T x.2.2.1.val

omit [AddCommGroup R] [Fintype R] in

theorem terminalQueries_eq (K : Finset X) (T : Finset R)
    (sizes : ℕ → ℕ) (x : TerminalTrace X sizes) : terminalQueries K T sizes x = SourceLookupClock sizes x := by
  simp only [terminalQueries, attemptQueries_eq, SourceLookupClock, TerminalCost,
    TerminalIterations, HistoryIterations]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]
  omega

theorem expected_queries (hN : 0 < Fintype.card X) (F : X → R) (K : Finset X) (T : Finset R)
    (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3) (hA : 0 < (marked F K T).card) :
    ∃ q : ℝ, HasSum (fun x : TerminalTrace X (SourceSizes (Fintype.card X) l) =>
      terminalMass F K T _ x * (terminalQueries K T _ x : ℝ)) q ∧
      0 ≤ q ∧ q ≤ (1 + 4*SourcePhaseConstant l) *
        Real.sqrt ((Fintype.card X : ℝ) / (marked F K T).card) := by
  simpa only [terminalMass_eq hN, terminalQueries_eq] using
    search_source_terminal_lookup_cost l hl hl4 (marked F K T) hA

end Qatlib.Papers.CollisionProb97.MainResults.ActualSearch
