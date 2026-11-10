/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedCircuit
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.SearchAttempt
import Qatlib.Foundations.QueryWordCore.Circuit
set_option warningAsError false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AdversaryBounds.AdvDuality

set_option autoImplicit false

namespace Qatlib.Concepts.QueryComplexity.AdaptiveQuery

open Qatlib.Concepts.SearchStopping.GroverSuccess

variable {I : Type*} [Fintype I] [DecidableEq I]

def observedOfCircuit (C : Circuit I) (P : ObservedCircuit I) :
    ObservedCircuit I :=
  match C with
  | [] => P
  | Step.gate U :: C' => ObservedCircuit.step (.gate U) (observedOfCircuit C' P)
  | Step.query :: C' => ObservedCircuit.step .query (observedOfCircuit C' P)

def queryPrefix : Circuit I → ℕ → Circuit I
  | [], _ => []
  | Step.gate U :: C, r => Step.gate U :: queryPrefix C r
  | Step.query :: _, 0 => []
  | Step.query :: C, r + 1 => Step.query :: queryPrefix C r

def querySuffix : Circuit I → ℕ → Circuit I
  | [], _ => []
  | Step.gate _ :: C, r => querySuffix C r
  | Step.query :: C, 0 => Step.query :: C
  | Step.query :: C, r + 1 => querySuffix C r

noncomputable def searchPhaseAttempt (A : Finset I) (j : ℕ) :
    ObservedCircuit (I × Bool) :=
  observedOfCircuit (LiftCircuit (SearchCircuit I j))
    (ObservedCircuit.measure (Fintype.card I)
      (fun x => Fintype.equivFin I x.1)
      (fun o => if (Fintype.equivFin I).symm o ∈ A then ObservedCircuit.halt true
        else ObservedCircuit.halt false))

def interruptObservedCircuit : Circuit I → ℕ → ObservedCircuit I → ObservedCircuit I
  | [], _, P => P
  | Step.gate U :: C, r, P => .step (.gate U) (interruptObservedCircuit C r P)
  | Step.query :: _, 0, P => P
  | Step.query :: C, r + 1, P => .step .query (interruptObservedCircuit C r P)

noncomputable def searchPhaseObservation (A : Finset I) : ObservedCircuit (I × Bool) :=
  .measure (Fintype.card I) (fun x => Fintype.equivFin I x.1)
    (fun o => .halt (decide ((Fintype.equivFin I).symm o ∈ A)))

noncomputable def interruptedSearchPhaseAttempt (A : Finset I) (j r : ℕ) :
    ObservedCircuit (I × Bool) :=
  interruptObservedCircuit (LiftCircuit (SearchCircuit I j)) r (searchPhaseObservation A)

end Qatlib.Concepts.QueryComplexity.AdaptiveQuery
