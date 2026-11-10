/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.InterruptedCall
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedQueryBudget
set_option warningAsError false

open Qatlib.Concepts.QueryComplexity.AdaptiveQuery

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin

open Qatlib

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
