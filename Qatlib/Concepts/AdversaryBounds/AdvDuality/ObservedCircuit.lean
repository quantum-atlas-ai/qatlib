/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

inductive ObservedCircuit (I : Type*) where
  | halt : Bool → ObservedCircuit I
  | step : Step I → ObservedCircuit I → ObservedCircuit I
  | measure : (outcomes : ℕ) → (I → Fin outcomes) →
      (Fin outcomes → ObservedCircuit I) → ObservedCircuit I
  | project : Matrix I I ℂ → ObservedCircuit I → ObservedCircuit I → ObservedCircuit I

structure BranchTrace (I : Type*) where
  state : QState I
  accepted : Bool
  queries : ℕ
  gates : ℕ
  measurements : ℕ
  outcomes : List (ℕ × ℕ)

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable abbrev branchMass (v : QState I) : ℝ := MeasureProb v Finset.univ

noncomputable abbrev normalizedBranch (v : QState I) : Option (QState I) :=
  ConditionalState v

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

noncomputable def observedAcceptance (oracle : Matrix I I ℂ)
    (program : ObservedCircuit I) (psi : QState I) : ℝ :=
  ((observedTraces oracle program psi).filter (fun t => t.accepted)).foldl
    (fun total t => total + branchMass t.state) 0

def observedWellFormed : ObservedCircuit I → Prop
  | .halt _ => True
  | .step (.gate U) next => U ∈ Matrix.unitaryGroup I ℂ ∧ observedWellFormed next
  | .step .query next => observedWellFormed next
  | .measure _ _ next => ∀ o, observedWellFormed (next o)
  | .project P onFalse onTrue =>
      IsOrthogonalProjector P ∧ observedWellFormed onFalse ∧ observedWellFormed onTrue

noncomputable def maximumObservedQueries (oracle : Matrix I I ℂ)
    (program : ObservedCircuit I) (psi : QState I) : ℕ :=
  (observedTraces oracle program psi).foldl (fun n t => max n t.queries) 0

noncomputable def maximumObservedGates (oracle : Matrix I I ℂ)
    (program : ObservedCircuit I) (psi : QState I) : ℕ :=
  (observedTraces oracle program psi).foldl (fun n t => max n t.gates) 0

noncomputable def expectedObservedQueries (oracle : Matrix I I ℂ)
    (program : ObservedCircuit I) (psi : QState I) : ℝ :=
  (observedTraces oracle program psi).foldl
    (fun total trace => total + branchMass trace.state * trace.queries) 0

theorem branchMass_nonneg (psi : QState I) : 0 ≤ branchMass psi := measureProb_nonneg _ _

end Qatlib.Concepts.AdversaryBounds.AdvDuality
