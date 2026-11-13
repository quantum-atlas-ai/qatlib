/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionProb97.MainResults.ActualPhaseProgram

/-!
# Compiled search and verification protocol

This module connects a compiled table-membership search circuit and its verification query to
abstract checked-search masses. It transports the attempt and terminal-trace laws, including all
failed attempts, to actual oracle query counts for the collision-search construction associated
with [BrassardHoyerTapp1998Collision].

## Main statements

* `searchState_eq`: agreement with the abstract search state and a zero value register.
* `attemptQueries_eq`: exactly `2*j+1` queries per checked attempt.
* `terminalQueries_eq` and `expected_queries`: exact terminal query accounting and its expected
  bound.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Collision]
-/

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

/-- The finite set of inputs outside `K` whose function values belong to `T`. -/
def marked (F : X → R) (K : Finset X) (T : Finset R) : Finset X :=
  Finset.univ.filter fun x => x ∉ K ∧ F x ∈ T

omit [AddCommGroup R] [Fintype R] in

/-- The diagonal gate formed from the table-membership signs is the phase oracle for `marked F K
T`. -/
theorem table_phase_eq (F : X → R) (K : Finset X) (T : Finset R) :
    Matrix.diagonal (fun x => PhaseCompile.tableSign K T x (F x)) = SetOracle (marked F K T) := by
  simp only [SetOracle, PhaseOracle]
  congr 1
  funext x
  simp [PhaseCompile.tableSign, marked]

/-- The state obtained by running the compiled search circuit for `j` iterations from a uniform
input and a zero value register. -/
def searchState (F : X → R) (K : Finset X) (T : Finset R) (j : ℕ) : QState (X × R) :=
  ApplyGate (evaluate (AddOracle F) (PhaseCompile.compile K T (SearchCircuit X j)))
    (TensorState (Uniform X) (Ket 0))

/-- The compiled search state equals the abstract marked-set search state tensored with a zero
value register. -/
theorem searchState_eq (F : X → R) (K : Finset X) (T : Finset R) (j : ℕ) :
    searchState F K T j = TensorState (SearchState (marked F K T) j) (Ket 0) := by
  rw [searchState, PhaseCompile.compile_run, table_phase_eq]
  rfl

/-- Marginalizing the compiled search state's Born probabilities over the value register gives
the abstract search state's Born probability. -/
theorem searchState_born (F : X → R) (K : Finset X) (T : Finset R) (j : ℕ) (x : X) :
    (∑ z : R, BornProb (searchState F K T j) (x, z)) = BornProb (SearchState (marked F K T) j) x := by
  rw [searchState_eq]
  simp [bornProb_tensorState, bornProb_ket]

/-- The state produced by a single additive-oracle query on the basis state `(x,0)`. -/
def verifyState (F : X → R) (x : X) : QState (X × R) :=
  Run (AddOracle F) [Step.query] (Ket (x, 0))

/-- The verification query maps `(x,0)` to the basis state `(x,F x)`. -/
theorem verifyState_eq (F : X → R) (x : X) : verifyState F x = Ket (x, F x) := by
  simp [verifyState, applyGate_addOracle_ket]

/-- The probability that the verification state has an input outside `K` and a value in `T`. -/
def verificationMass (F : X → R) (K : Finset X) (T : Finset R) (x : X) : ℝ :=
  MeasureProb (verifyState F x) (Finset.univ.filter fun p => p.1 ∉ K ∧ p.2 ∈ T)

/-- The verification acceptance probability is one for a marked input and zero otherwise. -/
theorem verificationMass_eq (F : X → R) (K : Finset X) (T : Finset R) (x : X) :
    verificationMass F K T x = if x ∈ marked F K T then 1 else 0 := by
  rw [verificationMass, verifyState_eq]
  simp [MeasureProb, bornProb_ket, marked]

/-- The mass of candidate `x` in the search output multiplied by its verification acceptance
probability. -/
def checkedOutput (F : X → R) (K : Finset X) (T : Finset R) (j : ℕ) (x : X) : ℝ :=
  (∑ z : R, BornProb (searchState F K T j) (x, z)) * verificationMass F K T x

/-- For a nonempty input type, the compiled and verified output mass equals the abstract
`CheckedOutputMass` for the marked set. -/
theorem checkedOutput_eq (hN : 0 < Fintype.card X) (F : X → R) (K : Finset X) (T : Finset R)
    (j : ℕ) (x : X) : checkedOutput F K T j x = CheckedOutputMass (marked F K T) j x := by
  rw [checkedOutput, searchState_born, verificationMass_eq, (search_checked_attempt hN _ j).2.1]
  split_ifs <;> simp

/-- The total mass of search candidates rejected by the verification query. -/
def checkedReject (F : X → R) (K : Finset X) (T : Finset R) (j : ℕ) : ℝ :=
  ∑ x : X, (∑ z : R, BornProb (searchState F K T j) (x, z)) * (1 - verificationMass F K T x)

/-- For a nonempty input type, the compiled rejection mass equals the abstract
`CheckedRejectMass` for the marked set. -/
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

/-- The mass of one search attempt with a uniformly chosen iteration count below `m`, recording
either rejection or a verified output. -/
def attemptMass (F : X → R) (K : Finset X) (T : Finset R) (m : ℕ) (a : Fin m × Option X) : ℝ :=
  (match a.2 with | none => checkedReject F K T a.1.val | some x => checkedOutput F K T a.1.val x) / m

/-- For a nonempty input type, the compiled attempt mass agrees with the abstract `AttemptMass`
for the marked set. -/
theorem attemptMass_eq (hN : 0 < Fintype.card X) (F : X → R) (K : Finset X) (T : Finset R)
    (m : ℕ) (a : Fin m × Option X) : attemptMass F K T m a = AttemptMass (marked F K T) m a := by
  unfold attemptMass AttemptMass
  cases a.2 <;> simp only [checkedReject_eq hN, checkedOutput_eq hN]

/-- The mass of a terminal search trace, given by the product of preceding rejected-attempt
masses and the final accepted-attempt mass. -/
def terminalMass (F : X → R) (K : Finset X) (T : Finset R) (sizes : ℕ → ℕ)
    (x : TerminalTrace X sizes) : ℝ :=
  (∏ i : Fin x.1, attemptMass F K T (sizes i.val) (x.2.1 i, none)) *
    attemptMass F K T (sizes x.1) (x.2.2.1, some x.2.2.2)

/-- For a nonempty input type, the compiled terminal-trace mass agrees with the abstract
`TerminalMass` for the marked set. -/
theorem terminalMass_eq (hN : 0 < Fintype.card X) (F : X → R) (K : Finset X) (T : Finset R)
    (sizes : ℕ → ℕ) (x : TerminalTrace X sizes) :
    terminalMass F K T sizes x = TerminalMass (marked F K T) sizes x := by
  simp only [terminalMass, attemptMass_eq hN, TerminalMass, TerminalStageMass, FailureHistoryMass]

/-- The query count of a compiled search attempt together with its single verification query. -/
def attemptQueries (K : Finset X) (T : Finset R) (j : ℕ) : ℕ :=
  adjointQueryCount (PhaseCompile.compile K T (SearchCircuit X j)) +
    QueryCount ([Step.query] : Circuit (X × R))

omit [AddCommGroup R] [Fintype R] in

/-- A search attempt with `j` iterations and verification uses exactly `2*j+1` queries. -/
theorem attemptQueries_eq (K : Finset X) (T : Finset R) (j : ℕ) :
    attemptQueries K T j = 2*j + 1 := by
  rw [attemptQueries, PhaseCompile.compile_queries, queryCount_groverCircuit]
  rfl

/-- The total query count along a terminal trace, including every failed attempt and the final
successful attempt. -/
def terminalQueries (K : Finset X) (T : Finset R) (sizes : ℕ → ℕ)
    (x : TerminalTrace X sizes) : ℕ :=
  (∑ i : Fin x.1, attemptQueries K T (x.2.1 i).val) + attemptQueries K T x.2.2.1.val

omit [AddCommGroup R] [Fintype R] in

/-- The actual query count along a terminal trace equals its `SourceLookupClock` value. -/
theorem terminalQueries_eq (K : Finset X) (T : Finset R)
    (sizes : ℕ → ℕ) (x : TerminalTrace X sizes) : terminalQueries K T sizes x = SourceLookupClock sizes x := by
  simp only [terminalQueries, attemptQueries_eq, SourceLookupClock, TerminalCost,
    TerminalIterations, HistoryIterations]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]
  omega

/-- For `1 < l < 4/3` and a nonempty marked set, the terminal-mass-weighted actual query counts
have a nonnegative sum bounded by `(1+4*SourcePhaseConstant l)*sqrt (|X|/|marked|)`. -/
theorem expected_queries (hN : 0 < Fintype.card X) (F : X → R) (K : Finset X) (T : Finset R)
    (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3) (hA : 0 < (marked F K T).card) :
    ∃ q : ℝ, HasSum (fun x : TerminalTrace X (SourceSizes (Fintype.card X) l) =>
      terminalMass F K T _ x * (terminalQueries K T _ x : ℝ)) q ∧
      0 ≤ q ∧ q ≤ (1 + 4*SourcePhaseConstant l) *
        Real.sqrt ((Fintype.card X : ℝ) / (marked F K T).card) := by
  simpa only [terminalMass_eq hN, terminalQueries_eq] using
    search_source_terminal_lookup_cost l hl hl4 (marked F K T) hA

end Qatlib.Papers.CollisionProb97.MainResults.ActualSearch
