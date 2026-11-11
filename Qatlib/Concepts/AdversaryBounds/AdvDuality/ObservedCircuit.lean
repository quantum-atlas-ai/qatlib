/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement

/-!
# Observed adaptive circuits

`ObservedCircuit` describes finite circuits with oracle queries, ordinary gates, labeled
measurements, binary projective measurements, and Boolean termination. `observedTraces`
enumerates their branches as `BranchTrace` records, retaining unnormalized states, resource
counts, and measurement outcomes. This branch semantics follows the measurement formalism
discussed in [NielsenChuang2010].

`observedAcceptance` and `expectedObservedQueries` weight branch metadata by `branchMass`, while
`maximumObservedQueries` and `maximumObservedGates` take maxima over the enumerated traces.
`observedWellFormed` records the local unitary and projector conditions.

## Main statements

* `observedTraces` gives recursive execution semantics for every circuit constructor.
* `observedWellFormed` specifies admissible gates and projectors throughout a circuit.
* `branchMass_nonneg` proves that every branch has nonnegative mass.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

/-- A finite adaptive circuit with Boolean termination, gate or oracle steps, labeled
measurements, and binary projective measurements. -/
inductive ObservedCircuit (I : Type*) where
  | halt : Bool → ObservedCircuit I
  | step : Step I → ObservedCircuit I → ObservedCircuit I
  | measure : (outcomes : ℕ) → (I → Fin outcomes) →
      (Fin outcomes → ObservedCircuit I) → ObservedCircuit I
  | project : Matrix I I ℂ → ObservedCircuit I → ObservedCircuit I → ObservedCircuit I

/-- A terminal branch record containing its unnormalized pure state, acceptance flag, resource
counts, and measurement outcome record. -/
structure BranchTrace (I : Type*) where
  state : QState I
  accepted : Bool
  queries : ℕ
  gates : ℕ
  measurements : ℕ
  outcomes : List (ℕ × ℕ)

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The total Born mass of a branch state, obtained by measuring over the entire basis. -/
noncomputable abbrev branchMass (v : QState I) : ℝ := MeasureProb v Finset.univ

/-- The optional normalized conditional state associated with a branch, as provided by
`ConditionalState`. -/
noncomputable abbrev normalizedBranch (v : QState I) : Option (QState I) :=
  ConditionalState v

/-- Enumerates all terminal branches of an observed circuit for a given oracle and input state.
Each trace retains the unnormalized branch state and accumulates operation counts and
measurement outcomes. -/
noncomputable def observedTraces (oracle : Matrix I I ℂ) :
    ObservedCircuit I → QState I → List (BranchTrace I)
  | .halt accepted, psi =>
      [{ state := psi
         accepted := accepted
         queries := 0
         gates := 0
         measurements := 0
         outcomes := [] }]
  | .step (.gate U) next, psi =>
      (observedTraces oracle next (ApplyGate U psi)).map
        (fun trace => { trace with gates := trace.gates + 1 })
  | .step .query next, psi =>
      (observedTraces oracle next (ApplyGate oracle psi)).map
        (fun trace => { trace with queries := trace.queries + 1 })
  | .measure outcomes label next, psi =>
      (List.ofFn (fun o : Fin outcomes =>
        (observedTraces oracle (next o)
          (Collapse psi (Finset.univ.filter (fun i => label i = o)))).map
            (fun trace => { trace with measurements := trace.measurements + 1, outcomes := (outcomes, o.val) :: trace.outcomes }))).flatten
  | .project P onFalse onTrue, psi =>
      (observedTraces oracle onFalse (ProjectiveBranch P false psi)).map
        (fun trace => { trace with measurements := trace.measurements + 1, outcomes := (2, 0) :: trace.outcomes }) ++
      (observedTraces oracle onTrue (ProjectiveBranch P true psi)).map
        (fun trace => { trace with measurements := trace.measurements + 1, outcomes := (2, 1) :: trace.outcomes })

/-- Sums the masses of terminal branches whose acceptance flag is true. -/
noncomputable def observedAcceptance (oracle : Matrix I I ℂ)
    (program : ObservedCircuit I) (psi : QState I) : ℝ :=
  ((observedTraces oracle program psi).filter (fun t => t.accepted)).foldl
    (fun total t => total + branchMass t.state) 0

/-- Requires every explicit gate to be unitary, every binary measurement matrix to be an
orthogonal projector, and every continuation to satisfy the same conditions. -/
def observedWellFormed : ObservedCircuit I → Prop
  | .halt _ => True
  | .step (.gate U) next => U ∈ Matrix.unitaryGroup I ℂ ∧ observedWellFormed next
  | .step .query next => observedWellFormed next
  | .measure _ _ next => ∀ o, observedWellFormed (next o)
  | .project P onFalse onTrue =>
      IsOrthogonalProjector P ∧ observedWellFormed onFalse ∧ observedWellFormed onTrue

/-- The largest query count among the enumerated terminal traces, with initial maximum zero. -/
noncomputable def maximumObservedQueries (oracle : Matrix I I ℂ)
    (program : ObservedCircuit I) (psi : QState I) : ℕ :=
  (observedTraces oracle program psi).foldl (fun n t => max n t.queries) 0

/-- The largest ordinary gate count among the enumerated terminal traces, with initial maximum
zero. -/
noncomputable def maximumObservedGates (oracle : Matrix I I ℂ)
    (program : ObservedCircuit I) (psi : QState I) : ℕ :=
  (observedTraces oracle program psi).foldl (fun n t => max n t.gates) 0

/-- The sum of each terminal branch's query count multiplied by its Born mass. -/
noncomputable def expectedObservedQueries (oracle : Matrix I I ℂ)
    (program : ObservedCircuit I) (psi : QState I) : ℝ :=
  (observedTraces oracle program psi).foldl
    (fun total trace => total + branchMass trace.state * trace.queries) 0

/-- The Born mass of every pure branch state is nonnegative. -/
theorem branchMass_nonneg (psi : QState I) : 0 ≤ branchMass psi := measureProb_nonneg _ _

end Qatlib.Concepts.AdversaryBounds.AdvDuality
