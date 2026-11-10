/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.InterruptedCall
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedQueryBudget
set_option warningAsError false

open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin

open Qatlib.Concepts.SearchStopping.GroverSuccess

def InterruptedSearchAttempt : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (_hN : 0 < Fintype.card I) (A : Finset I)
    (j r : ℕ),
    let O := BitOracleOn (fun x => decide (x ∈ A))
    let ψ := (WithMinus (Uniform I) : QState (I × Bool))
    (observedAcceptance O
        (interruptedSearchPhaseAttempt A j r) ψ
      = MeasureProb (Run O
          (queryPrefix (LiftCircuit (SearchCircuit I j)) r) ψ)
        (A ×ˢ Finset.univ)) ∧
    (∀ t ∈ observedTraces O
        (interruptedSearchPhaseAttempt A j r) ψ,
      t.queries = min j r) ∧
    (((observedTraces O
        (interruptedSearchPhaseAttempt A j r) ψ).map
        (fun t => branchMass t.state)).sum = 1) ∧
    (MeasureProb (SearchState A j) A - (j : ℝ) / (r + 1)
      ≤ observedAcceptance O
        (interruptedSearchPhaseAttempt A j r) ψ) ∧
    (j ≤ r →
      observedAcceptance O
        (interruptedSearchPhaseAttempt A j r) ψ
        = MeasureProb (SearchState A j) A) ∧
    (Run O (querySuffix (LiftCircuit (SearchCircuit I j)) r)
        (Run O (queryPrefix (LiftCircuit (SearchCircuit I j)) r) ψ)
      = Run O (LiftCircuit (SearchCircuit I j)) ψ)

end Qatlib.Concepts.AmplitudeSearch.InterruptMin
