/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.InterruptedCallLawsStat
import Qatlib.Concepts.AmplitudeSearch.InterruptMin.InterruptionCounterexampleContracts

/-!
# Circuit prefix laws for interrupted calls

This module proves that interrupting a circuit at a query budget is represented by its query
prefix. It establishes the trace, query-count, unitary-prefix, and prefix-suffix reconstruction
identities collected in `InterruptedCallLaws`.

These identities provide circuit semantics for interruptions in quantum minimum search
[DurrHoyer1996]. The module also refutes `InterruptedCallLawsLegacy`.

## Main statements

* `queryPrefix_queryCount`: The query count of a query prefix is the minimum of the circuit's
  query count and the budget.
* `queryPrefix_suffix_run`: Running the suffix after the prefix gives the same state as running
  the full circuit.
* `interruptedCallLaws`: Establishes the circuit trace, interruption, and prefix-suffix
  identities collected in `InterruptedCallLaws`, supporting the execution model for minimum
  search [DurrHoyer1996].

## References

* [Dürr and Høyer, 1996][DurrHoyer1996]
-/

set_option warningAsError false

open Qatlib.Concepts.QueryComplexity.AdaptiveQuery

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin

open Qatlib
open scoped Classical

/-- Executing a circuit followed by an accepting halt produces one trace with the final state,
full query and gate counts, and no measurements or outcomes. -/
theorem observedOfCircuit_single_trace {I : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (C : Circuit I) (ψ : QState I) :
    observedTraces O (observedOfCircuit C (ObservedCircuit.halt true)) ψ =
      [{ state := Run O C ψ, accepted := true, queries := QueryCount C, gates := GateCount C, measurements := 0, outcomes := [] }] := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | query => simp [observedOfCircuit, observedTraces, Run, QueryCount, GateCount, ih]
    | gate U => simp [observedOfCircuit, observedTraces, Run, QueryCount, GateCount, ih]

/-- The query count of a query prefix is the minimum of the circuit's query count and the
budget. -/
theorem queryPrefix_queryCount {I : Type} [Fintype I] [DecidableEq I]
    (C : Circuit I) (r : ℕ) : QueryCount (queryPrefix C r) = min (QueryCount C) r := by
  induction C generalizing r with
  | nil => simp [queryPrefix, QueryCount]
  | cons s C ih =>
    cases s with
    | gate U => simpa only [queryPrefix, QueryCount] using ih r
    | query =>
      cases r with
      | zero => simp [queryPrefix, QueryCount]
      | succ r => simp only [queryPrefix, QueryCount, ih]; omega

/-- Appending the query suffix to the query prefix reconstructs the original circuit. -/
theorem queryPrefix_append_querySuffix {I : Type} [Fintype I] [DecidableEq I]
    (C : Circuit I) (r : ℕ) : queryPrefix C r ++ querySuffix C r = C := by
  induction C generalizing r with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U => simpa only [queryPrefix, querySuffix, List.cons_append] using congrArg (List.cons (Step.gate U)) (ih r)
    | query =>
      cases r with
      | zero => rfl
      | succ r => simpa only [queryPrefix, querySuffix, List.cons_append] using congrArg (List.cons Step.query) (ih r)

/-- Running the suffix after the prefix gives the same state as running the full circuit. -/
theorem queryPrefix_suffix_run {I : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (C : Circuit I) (ψ : QState I) (r : ℕ) :
    Run O (querySuffix C r) (Run O (queryPrefix C r) ψ) = Run O C ψ := by
  rw [← run_append, queryPrefix_append_querySuffix]

/-- The query prefix followed by an accepting halt has one trace with query count `min
(QueryCount C) r` and no measurements or outcomes. -/
theorem queryPrefix_single_trace {I : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (C : Circuit I) (ψ : QState I) (r : ℕ) :
    observedTraces O (observedOfCircuit (queryPrefix C r) (ObservedCircuit.halt true)) ψ =
      [{ state := Run O (queryPrefix C r) ψ, accepted := true, queries := min (QueryCount C) r, gates := GateCount (queryPrefix C r), measurements := 0, outcomes := [] }] := by
  rw [observedOfCircuit_single_trace, queryPrefix_queryCount]

/-- The legacy interrupted-call contract is false. -/
theorem interruptedCallLaws_counterexample : ¬ InterruptedCallLawsLegacy := by
  intro h
  have he := (h (Fin 1) (1 : Matrix (Fin 1) (Fin 1) ℂ) [Step.query] (Ket 0) 0).2.1
  simp [observedOfCircuit, truncateObservedQueries, queryPrefix] at he

/-- Truncating a circuit followed by an accepting halt gives its query prefix, with the final
acceptance flag recording whether the full query count fits the budget. -/
theorem truncate_observedOfCircuit_halt {I : Type} [Fintype I] [DecidableEq I]
    (C : Circuit I) (r : ℕ) :
    truncateObservedQueries (observedOfCircuit C (ObservedCircuit.halt true)) r =
      observedOfCircuit (queryPrefix C r) (ObservedCircuit.halt (decide (QueryCount C ≤ r))) := by
  induction C generalizing r with
  | nil => simp [observedOfCircuit, truncateObservedQueries, queryPrefix, QueryCount]
  | cons s C ih =>
    cases s with
    | gate U => simpa only [observedOfCircuit, truncateObservedQueries, queryPrefix, QueryCount] using!
        congrArg (ObservedCircuit.step (.gate U)) (ih r)
    | query =>
      cases r with
      | zero => simp [observedOfCircuit, truncateObservedQueries, queryPrefix, QueryCount]
      | succ r => simpa only [observedOfCircuit, truncateObservedQueries, queryPrefix, QueryCount,
          Nat.add_le_add_iff_right] using congrArg (ObservedCircuit.step .query) (ih r)

/-- Interrupting a circuit at budget `r` is its query prefix followed by the supplied observed
continuation. -/
theorem interruptObservedCircuit_eq_prefix {I : Type} [Fintype I] [DecidableEq I]
    (C : Circuit I) (r : ℕ) (P : ObservedCircuit I) :
    interruptObservedCircuit C r P = observedOfCircuit (queryPrefix C r) P := by
  induction C generalizing r with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U => simpa only [interruptObservedCircuit, queryPrefix, observedOfCircuit] using
        congrArg (ObservedCircuit.step (.gate U)) (ih r)
    | query =>
      cases r with
      | zero => rfl
      | succ r => simpa only [interruptObservedCircuit, queryPrefix, observedOfCircuit] using
          congrArg (ObservedCircuit.step .query) (ih r)

/-- A query prefix equals the full circuit when the query count fits the budget. -/
theorem queryPrefix_eq_self {I : Type} [Fintype I] [DecidableEq I]
    (C : Circuit I) (r : ℕ) (h : QueryCount C ≤ r) : queryPrefix C r = C := by
  induction C generalizing r with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U => simpa only [queryPrefix] using congrArg (List.cons (.gate U)) (ih r h)
    | query =>
      cases r with
      | zero => simp only [QueryCount] at h; omega
      | succ r =>
        have hh : QueryCount C ≤ r := by simp only [QueryCount] at h; omega
        simpa only [queryPrefix] using congrArg (List.cons .query) (ih r hh)

/-- A query prefix of a unitary circuit is unitary. -/
theorem queryPrefix_unitary {I : Type} [Fintype I] [DecidableEq I]
    (C : Circuit I) (r : ℕ) (h : IsUnitaryCircuit C) : IsUnitaryCircuit (queryPrefix C r) := by
  induction C generalizing r with
  | nil => exact isUnitaryCircuit_nil
  | cons s C ih =>
    cases s with
    | gate U =>
      obtain ⟨hU, hC⟩ := (isUnitaryCircuit_gate U C).mp h
      exact (isUnitaryCircuit_gate U _).mpr ⟨hU, ih r hC⟩
    | query =>
      cases r with
      | zero => exact isUnitaryCircuit_nil
      | succ r => exact (isUnitaryCircuit_query _).mpr (ih r ((isUnitaryCircuit_query C).mp h))

/-- Establishes the circuit trace, interruption, and prefix-suffix identities collected in
`InterruptedCallLaws`, supporting the execution model for minimum search [DurrHoyer1996]. -/
theorem interruptedCallLaws : InterruptedCallLaws := by
  intro I _ _ O C ψ r
  exact ⟨observedOfCircuit_single_trace O C ψ,
    interruptObservedCircuit_eq_prefix C r _, queryPrefix_single_trace O C ψ r,
    queryPrefix_append_querySuffix C r, queryPrefix_suffix_run O C ψ r⟩

end Qatlib.Concepts.AmplitudeSearch.InterruptMin
