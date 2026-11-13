/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.InterruptedCall
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedQueryBudget

/-!
# The interrupted-call contract

This module defines `InterruptedCallLaws`, a proposition collecting trace semantics and
prefix-suffix identities for a circuit interrupted after a query budget. The contract records
the exact minimum query count and reconstruction of the full execution.

It supplies a circuit-level interface for interrupted minimum-search procedures [DurrHoyer1996].

## Main statements

* `InterruptedCallLaws`: The contract asserting full-circuit and query-prefix trace formulas,
  the prefix representation of interruption, and prefix-suffix reconstruction of circuits and
  their execution.

## References

* [Dürr and Høyer, 1996][DurrHoyer1996]
-/

open Qatlib.Concepts.QueryComplexity.AdaptiveQuery

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin

open Qatlib

/-- The contract asserting full-circuit and query-prefix trace formulas, the prefix
representation of interruption, and prefix-suffix reconstruction of circuits and their
execution. -/
def InterruptedCallLaws : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (O : Matrix I I ℂ) (C : Circuit I)
    (ψ : QState I) (r : ℕ),
    observedTraces O (observedOfCircuit C (ObservedCircuit.halt true)) ψ
      = [{ state := Run O C ψ, accepted := true, queries := QueryCount C, gates := GateCount C, measurements := 0, outcomes := [] }] ∧
    interruptObservedCircuit C r (ObservedCircuit.halt true)
      = observedOfCircuit (queryPrefix C r) (ObservedCircuit.halt true) ∧
    observedTraces O (observedOfCircuit (queryPrefix C r) (ObservedCircuit.halt true)) ψ
      = [{ state := Run O (queryPrefix C r) ψ, accepted := true, queries := min (QueryCount C) r, gates := GateCount (queryPrefix C r), measurements := 0, outcomes := [] }] ∧
    queryPrefix C r ++ querySuffix C r = C ∧
    Run O (querySuffix C r) (Run O (queryPrefix C r) ψ) = Run O C ψ

end Qatlib.Concepts.AmplitudeSearch.InterruptMin
