/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedQueryBudget
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.AdaptiveQuery.RawProcess
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ShadowModels.ShadowChannel

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

variable {I : Type*}

noncomputable def observedQueryRightFactor (K : Matrix I I ℂ) :
    ObservedCircuit I → ObservedCircuit I
  | .halt accepted => .halt accepted
  | .step (.gate U) next => .step (.gate U) (observedQueryRightFactor K next)
  | .step .query next => .step (.gate K) (.step .query (observedQueryRightFactor K next))
  | .measure n label next => .measure n label (fun o => observedQueryRightFactor K (next o))
  | .project M onFalse onTrue =>
      .project M (observedQueryRightFactor K onFalse) (observedQueryRightFactor K onTrue)

def addQueryGates (t : BranchTrace I) : BranchTrace I :=
  { t with gates := t.gates + t.queries }

theorem observedQueryRightFactor_traces [Fintype I] [DecidableEq I]
    (O K : Matrix I I ℂ) (P : ObservedCircuit I) (psi : QState I) :
    observedTraces O (observedQueryRightFactor K P) psi =
      (observedTraces (O * K) P psi).map addQueryGates := by
  induction P generalizing psi with
  | halt accepted => simp [observedQueryRightFactor, observedTraces, addQueryGates]
  | step s next ih =>
    cases s with
    | gate U =>
      simp only [observedQueryRightFactor, observedTraces, ih, List.map_map,
        Function.comp_def, addQueryGates, Nat.add_right_comm]
    | query =>
      simp only [observedQueryRightFactor, observedTraces, ← applyGate_mul, ih,
        List.map_map, Function.comp_def, addQueryGates, Nat.add_assoc]
  | measure n label next ih =>
    simp only [observedQueryRightFactor, observedTraces, ih, List.map_flatten,
      List.map_ofFn, List.map_map, Function.comp_def, addQueryGates]
  | project M onFalse onTrue ihFalse ihTrue =>
    simp only [observedQueryRightFactor, observedTraces, ihFalse, ihTrue,
      List.map_append, List.map_map, Function.comp_def, addQueryGates]

theorem observedQueryRightFactor_budget [Fintype I] [DecidableEq I]
    (K : Matrix I I ℂ) (P : ObservedCircuit I) :
    observedQueryBudget (observedQueryRightFactor K P) = observedQueryBudget P := by
  induction P with
  | halt accepted => rfl
  | step s next ih =>
    cases s <;> simp only [observedQueryRightFactor, observedQueryBudget, ih]
  | measure n label next ih =>
    simp only [observedQueryRightFactor, observedQueryBudget, ih]
  | project M onFalse onTrue ihFalse ihTrue =>
    simp only [observedQueryRightFactor, observedQueryBudget, ihFalse, ihTrue]

theorem observedQueryRightFactor_wellFormed [Fintype I] [DecidableEq I]
    (K : Matrix I I ℂ) (hK : K ∈ Matrix.unitaryGroup I ℂ)
    (P : ObservedCircuit I) (hP : observedWellFormed P) :
    observedWellFormed (observedQueryRightFactor K P) := by
  induction P with
  | halt accepted => trivial
  | step s next ih =>
    cases s with
    | gate U => exact ⟨hP.1, ih hP.2⟩
    | query => exact ⟨hK, ih hP⟩
  | measure n label next ih => exact fun o => ih o (hP o)
  | project M onFalse onTrue ihFalse ihTrue =>
    exact ⟨hP.1, ihFalse hP.2.1, ihTrue hP.2.2⟩

theorem observedQueryRightFactor_expected [Fintype I] [DecidableEq I]
    (O K : Matrix I I ℂ) (P : ObservedCircuit I) (psi : QState I) :
    expectedObservedQueries O (observedQueryRightFactor K P) psi =
      expectedObservedQueries (O * K) P psi := by
  simp only [expectedObservedQueries_eq_sum, observedQueryRightFactor_traces,
    List.map_map, Function.comp_def, addQueryGates]

theorem observedQueryRightFactor_event [Fintype I] [DecidableEq I]
    (O K : Matrix I I ℂ) (P : ObservedCircuit I) (psi : QState I)
    (event : Bool → List (ℕ × ℕ) → Bool) :
    observedEventMass O (observedQueryRightFactor K P) psi
        (fun t => event t.accepted t.outcomes) =
      observedEventMass (O * K) P psi (fun t => event t.accepted t.outcomes) := by
  simp only [observedEventMass, observedQueryRightFactor_traces, List.map_map,
    Function.comp_def, addQueryGates]

end Qatlib.Concepts.AdversaryBounds.AdvDuality
