/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.InterruptedCallLawsStat
import Qatlib.Concepts.AmplitudeSearch.InterruptMin.InterruptionCounterexampleContracts
set_option warningAsError false

open Qatlib.Concepts.QueryComplexity.AdaptiveQuery

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin

open Qatlib
open scoped Classical

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

theorem queryPrefix_suffix_run {I : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (C : Circuit I) (ψ : QState I) (r : ℕ) :
    Run O (querySuffix C r) (Run O (queryPrefix C r) ψ) = Run O C ψ := by
  rw [← run_append, queryPrefix_append_querySuffix]

theorem queryPrefix_single_trace {I : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (C : Circuit I) (ψ : QState I) (r : ℕ) :
    observedTraces O (observedOfCircuit (queryPrefix C r) (ObservedCircuit.halt true)) ψ =
      [{ state := Run O (queryPrefix C r) ψ, accepted := true, queries := min (QueryCount C) r, gates := GateCount (queryPrefix C r), measurements := 0, outcomes := [] }] := by
  rw [observedOfCircuit_single_trace, queryPrefix_queryCount]

theorem interruptedCallLaws_counterexample : ¬ InterruptedCallLawsLegacy := by
  intro h
  have he := (h (Fin 1) (1 : Matrix (Fin 1) (Fin 1) ℂ) [Step.query] (Ket 0) 0).2.1
  simp [observedOfCircuit, truncateObservedQueries, queryPrefix] at he

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

theorem interruptedCallLaws : InterruptedCallLaws := by
  intro I _ _ O C ψ r
  exact ⟨observedOfCircuit_single_trace O C ψ,
    interruptObservedCircuit_eq_prefix C r _, queryPrefix_single_trace O C ψ r,
    queryPrefix_append_querySuffix C r, queryPrefix_suffix_run O C ψ r⟩

end Qatlib.Concepts.AmplitudeSearch.InterruptMin
