/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionProb97.MainResults.ReadOnlyTable
import Qatlib.Papers.CollisionProb97.MainResults.ActualSearchProtocol

/-!
# Verified search with read-only table memory

This module executes quantum search and verification while retaining the table as an explicit
memory register. It identifies the resulting output and terminal-history masses with the
abstract marked-set search laws used in [BrassardHoyerTapp1998Collision].

The results `terminal_law` and `expected_queries` establish normalization, marked-output
support, and the expected query bound, charging both search queries and verification queries.

## Main statements

* `searchState_eq`: The compiled search state factors as the corresponding abstract search state
  tensored with the unchanged table basis state.
* `terminal_law`: For a nonempty marked set and `1 < l < 4 / 3`, the scheduled terminal masses
  sum to one, are nonnegative, and vanish on unmarked outputs.
* `expected_queries`: For a nonempty marked set, the query-weighted terminal masses have a
  nonnegative sum bounded by `(1 + 4 * SourcePhaseConstant l) * sqrt (|X| / |marked|)`.

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

namespace Qatlib.Papers.CollisionProb97.MainResults.ReadOnlySearch
variable {S X R : Type} [Fintype S] [DecidableEq S] [Fintype X] [DecidableEq X]
    [AddCommGroup R] [Fintype R] [DecidableEq R]

/-- The state obtained by running the compiled search circuit on a uniform input, a zero value
register, and fixed table memory. -/
def searchState (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (j : ℕ) :
    QState ((X × R) × ReadOnlyTable.Memory (X := S) (R := R) k) :=
  ApplyGate (evaluate (ReadOnlyTable.oracle F k) (ReadOnlyTable.compile K k (SearchCircuit X j)))
    (TensorState (TensorState (Uniform X) (Qatlib.Foundations.PureStateMath.Ket 0))
      (Qatlib.Foundations.PureStateMath.Ket L))

/-- The compiled search state factors as the corresponding abstract search state tensored with
the unchanged table basis state. -/
theorem searchState_eq (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (j : ℕ) :
    searchState F K L j = TensorState (ActualSearch.searchState F K (ReadOnlyTable.values L) j)
      (Qatlib.Foundations.PureStateMath.Ket L) := by
  rw [searchState, ReadOnlyTable.compile_run, ActualSearch.searchState, PhaseCompile.compile_run]

/-- Marginalizing the search state's Born probabilities over value and memory registers yields
the ideal marked-set search probability of `x`. -/
theorem searchState_born (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (j : ℕ) (x : X) :
    (∑ z : R, ∑ M : ReadOnlyTable.Memory (X := S) (R := R) k,
      BornProb (searchState F K L j) ((x, z), M)) =
      BornProb (SearchState (ActualSearch.marked F K (ReadOnlyTable.values L)) j) x := by
  rw [searchState_eq, ActualSearch.searchState_eq]
  simp [bornProb_tensorState, bornProb_ket]

/-- The state obtained by one evaluation query on input `x` with a zero value register and fixed
table memory. -/
def verificationState (F : X → R) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (x : X) :
    QState ((X × R) × ReadOnlyTable.Memory (X := S) (R := R) k) :=
  Run (ReadOnlyTable.oracle F k) [Step.query]
    (Qatlib.Foundations.PureStateMath.Ket ((x, 0), L))

/-- A verification query produces the basis state containing `x`, `F x`, and the unchanged table
memory. -/
theorem verificationState_eq (F : X → R) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (x : X) :
    verificationState F L x = Qatlib.Foundations.PureStateMath.Ket ((x, F x), L) := by
  rw [verificationState, run_query, run_nil, ReadOnlyTable.oracle_ket]
  simp

/-- The measurement probability that verification yields an input outside `K` with a value
stored in the table. -/
def verificationMass (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (x : X) : ℝ :=
  MeasureProb (verificationState F L x)
    (Finset.univ.filter fun p => p.1.1 ∉ K ∧ p.1.2 ∈ ReadOnlyTable.values p.2)

/-- The verification probability with explicit memory equals the abstract table-value
verification probability. -/
theorem verificationMass_eq (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (x : X) :
    verificationMass F K L x = ActualSearch.verificationMass F K (ReadOnlyTable.values L) x := by
  rw [verificationMass, verificationState_eq, ActualSearch.verificationMass_eq]
  simp [MeasureProb, bornProb_ket, ActualSearch.marked]

/-- The search probability of `x` multiplied by its verification acceptance probability. -/
def checkedOutput (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (j : ℕ) (x : X) : ℝ :=
  (∑ z : R, ∑ M : ReadOnlyTable.Memory (X := S) (R := R) k,
    BornProb (searchState F K L j) ((x, z), M)) * verificationMass F K L x

/-- For a nonempty search domain, `checkedOutput` equals the ideal checked-output mass for the
corresponding marked set. -/
theorem checkedOutput_eq (hN : 0 < Fintype.card X) (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (j : ℕ) (x : X) :
    checkedOutput F K L j x = CheckedOutputMass (ActualSearch.marked F K (ReadOnlyTable.values L)) j x := by
  rw [checkedOutput, searchState_born, verificationMass_eq]
  rw [← ActualSearch.searchState_born F K (ReadOnlyTable.values L) j x]
  exact ActualSearch.checkedOutput_eq hN F K (ReadOnlyTable.values L) j x

/-- The total search probability weighted by verification rejection over all measured inputs. -/
def checkedReject (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (j : ℕ) : ℝ :=
  ∑ x : X, (∑ z : R, ∑ M : ReadOnlyTable.Memory (X := S) (R := R) k,
    BornProb (searchState F K L j) ((x, z), M)) * (1 - verificationMass F K L x)

/-- For a nonempty search domain, `checkedReject` equals the ideal checked-rejection mass for
the corresponding marked set. -/
theorem checkedReject_eq (hN : 0 < Fintype.card X) (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (j : ℕ) :
    checkedReject F K L j = CheckedRejectMass (ActualSearch.marked F K (ReadOnlyTable.values L)) j := by
  rw [checkedReject, ← ActualSearch.checkedReject_eq hN F K (ReadOnlyTable.values L) j]
  unfold ActualSearch.checkedReject
  simp only [searchState_born, verificationMass_eq, ActualSearch.searchState_born]

/-- The mass of a checked attempt with a uniformly chosen iteration count below `m`, recording
either rejection or an accepted input. -/
def attemptMass (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (m : ℕ) (a : Fin m × Option X) : ℝ :=
  (match a.2 with | none => checkedReject F K L a.1.val | some x => checkedOutput F K L a.1.val x) / m

/-- For a nonempty search domain, the explicit-memory attempt mass equals the ideal marked-set
attempt mass. -/
theorem attemptMass_eq (hN : 0 < Fintype.card X) (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (m : ℕ) (a : Fin m × Option X) :
    attemptMass F K L m a = AttemptMass (ActualSearch.marked F K (ReadOnlyTable.values L)) m a := by
  unfold attemptMass AttemptMass
  cases a.2 <;> simp only [checkedReject_eq hN, checkedOutput_eq hN]

/-- The mass of a finite history of rejected attempts followed by an accepted attempt, using the
given size schedule. -/
def terminalMass (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (sizes : ℕ → ℕ) (x : TerminalTrace X sizes) : ℝ :=
  (∏ i : Fin x.1, attemptMass F K L (sizes i.val) (x.2.1 i, none)) *
    attemptMass F K L (sizes x.1) (x.2.2.1, some x.2.2.2)

/-- For a nonempty search domain, the explicit-memory terminal-history mass equals the ideal
marked-set terminal mass. -/
theorem terminalMass_eq (hN : 0 < Fintype.card X) (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (sizes : ℕ → ℕ) (x : TerminalTrace X sizes) :
    terminalMass F K L sizes x = TerminalMass (ActualSearch.marked F K (ReadOnlyTable.values L)) sizes x := by
  simp only [terminalMass, attemptMass_eq hN, TerminalMass, TerminalStageMass, FailureHistoryMass]

/-- The number of oracle queries in a compiled search attempt, including its final verification
query. -/
def attemptQueries (K : Finset X) (k j : ℕ) : ℕ :=
  adjointQueryCount (ReadOnlyTable.compile (S := S) (R := R) K k (SearchCircuit X j)) +
    QueryCount ([Step.query] : Circuit ((X × R) × ReadOnlyTable.Memory (X := S) (R := R) k))

omit [AddCommGroup R] [Fintype S] [Fintype R] in

/-- An attempt with `j` search iterations uses exactly `2 * j + 1` oracle queries. -/
theorem attemptQueries_eq (K : Finset X) (k j : ℕ) : attemptQueries (S := S) (R := R) K k j = 2*j + 1 := by
  rw [attemptQueries, ReadOnlyTable.compile_queries, queryCount_groverCircuit]
  rfl

/-- The sum of the query counts of all failed attempts and the final successful attempt in a
terminal trace. -/
def terminalQueries (K : Finset X) (k : ℕ) (sizes : ℕ → ℕ) (x : TerminalTrace X sizes) : ℕ :=
  (∑ i : Fin x.1, attemptQueries (S := S) (R := R) K k (x.2.1 i).val) +
    attemptQueries (S := S) (R := R) K k x.2.2.1.val

omit [AddCommGroup R] [Fintype S] [Fintype R] in

/-- The explicit terminal query count equals `SourceLookupClock` for the same trace. -/
theorem terminalQueries_eq (K : Finset X) (k : ℕ) (sizes : ℕ → ℕ) (x : TerminalTrace X sizes) :
    terminalQueries (S := S) (R := R) K k sizes x = SourceLookupClock sizes x := by
  simp only [terminalQueries, attemptQueries_eq, SourceLookupClock, TerminalCost,
      TerminalIterations, HistoryIterations]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]
  omega

/-- For a nonempty marked set and `1 < l < 4 / 3`, the scheduled terminal masses sum to one, are
nonnegative, and vanish on unmarked outputs. -/
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

/-- For a nonempty marked set, the query-weighted terminal masses have a nonnegative sum bounded
by `(1 + 4 * SourcePhaseConstant l) * sqrt (|X| / |marked|)`. -/
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
