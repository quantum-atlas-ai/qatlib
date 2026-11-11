/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedCircuit
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.SearchAttempt
import Qatlib.Foundations.QueryWordCore.Circuit

/-!
# Interrupting search circuits at query boundaries

This module embeds circuit words into observed circuits and splits words at a specified oracle
query budget. The constructions retain the gates preceding the next unpaid query and attach an
observation continuation at the interruption point.

It defines full and interrupted lifted search attempts with a final address measurement and
acceptance determined by membership in the marked set. These constructions provide query budget
interfaces for the search procedures studied in [BoyerEtAl1998].

## Main statements

* `queryPrefix`: the circuit prefix allowed by a query budget.
* `interruptObservedCircuit`: an observed prefix with a chosen continuation at interruption.
* `interruptedSearchPhaseAttempt`: a lifted search prefix followed by a marked address
  observation.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option warningAsError false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AdversaryBounds.AdvDuality

set_option autoImplicit false

namespace Qatlib.Concepts.QueryComplexity.AdaptiveQuery

open Qatlib.Concepts.SearchStopping.GroverSuccess

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Prepend every step of a circuit word to an observed continuation. -/
def observedOfCircuit (C : Circuit I) (P : ObservedCircuit I) :
    ObservedCircuit I :=
  match C with
  | [] => P
  | Step.gate U :: C' => ObservedCircuit.step (.gate U) (observedOfCircuit C' P)
  | Step.query :: C' => ObservedCircuit.step .query (observedOfCircuit C' P)

/-- The circuit prefix containing up to `r` queries and all gates before the next query, or the
whole circuit if it ends first. -/
def queryPrefix : Circuit I → ℕ → Circuit I
  | [], _ => []
  | Step.gate U :: C, r => Step.gate U :: queryPrefix C r
  | Step.query :: _, 0 => []
  | Step.query :: C, r + 1 => Step.query :: queryPrefix C r

/-- The circuit suffix starting at the first query beyond the budget `r`, or the empty word if
no such query exists. -/
def querySuffix : Circuit I → ℕ → Circuit I
  | [], _ => []
  | Step.gate _ :: C, r => querySuffix C r
  | Step.query :: C, 0 => Step.query :: C
  | Step.query :: C, r + 1 => querySuffix C r

/-- Run the lifted `j` iteration search circuit, then measure the address and accept exactly
when it belongs to `A`. -/
noncomputable def searchPhaseAttempt (A : Finset I) (j : ℕ) :
    ObservedCircuit (I × Bool) :=
  observedOfCircuit (LiftCircuit (SearchCircuit I j))
    (ObservedCircuit.measure (Fintype.card I)
      (fun x => Fintype.equivFin I x.1)
      (fun o => if (Fintype.equivFin I).symm o ∈ A then ObservedCircuit.halt true
        else ObservedCircuit.halt false))

/-- Convert a circuit prefix into observed steps, stopping before the first query beyond the
budget and attaching the continuation there, or after the circuit ends. -/
def interruptObservedCircuit : Circuit I → ℕ → ObservedCircuit I → ObservedCircuit I
  | [], _, P => P
  | Step.gate U :: C, r, P => .step (.gate U) (interruptObservedCircuit C r P)
  | Step.query :: _, 0, P => P
  | Step.query :: C, r + 1, P => .step .query (interruptObservedCircuit C r P)

/-- Measure the address register and halt with acceptance exactly when the measured address
belongs to `A`. -/
noncomputable def searchPhaseObservation (A : Finset I) : ObservedCircuit (I × Bool) :=
  .measure (Fintype.card I) (fun x => Fintype.equivFin I x.1)
    (fun o => .halt (decide ((Fintype.equivFin I).symm o ∈ A)))

/-- Run the lifted search circuit up to the query budget `r`, then measure the address and
accept exactly on `A`. -/
noncomputable def interruptedSearchPhaseAttempt (A : Finset I) (j r : ℕ) :
    ObservedCircuit (I × Bool) :=
  interruptObservedCircuit (LiftCircuit (SearchCircuit I j)) r (searchPhaseObservation A)

end Qatlib.Concepts.QueryComplexity.AdaptiveQuery
