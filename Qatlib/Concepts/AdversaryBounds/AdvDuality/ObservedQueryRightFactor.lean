/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedQueryBudget

/-!
# Right factors of observed oracle queries

`observedQueryRightFactor` inserts a fixed gate before each query, implementing the product
oracle `O * K`. `addQueryGates` records the resulting increase in gate counts, and the trace
correspondence preserves query budgets, expected query counts, and events determined by
classical outcomes and acceptance. The construction uses the matrix composition convention of
[NielsenChuang2010].

## Main statements

* `observedQueryRightFactor_traces`: Traces agree with the product-oracle execution after
  adjusting gate counts.
* `observedQueryRightFactor_wellFormed`: A unitary right factor preserves well-formedness.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.AdaptiveQuery.RawProcess
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ShadowModels.ShadowChannel

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

variable {I : Type*}

/-- Inserts the gate `K` before every oracle query of an observed circuit, implementing right
multiplication of the oracle by `K`. -/
noncomputable def observedQueryRightFactor (K : Matrix I I ℂ) :
    ObservedCircuit I → ObservedCircuit I
  | .halt accepted => .halt accepted
  | .step (.gate U) next => .step (.gate U) (observedQueryRightFactor K next)
  | .step .query next => .step (.gate K) (.step .query (observedQueryRightFactor K next))
  | .measure n label next => .measure n label (fun o => observedQueryRightFactor K (next o))
  | .project M onFalse onTrue =>
      .project M (observedQueryRightFactor K onFalse) (observedQueryRightFactor K onTrue)

/-- Adds the query count to the gate count of a branch trace, retaining its state and other
metadata. -/
def addQueryGates (t : BranchTrace I) : BranchTrace I :=
  { t with gates := t.gates + t.queries }

/-- Executing the transformed circuit with oracle `O` gives the traces for oracle `O * K`, with
one additional gate counted per query. -/
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

/-- Inserting a right factor before every query preserves the structural query budget. -/
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

/-- Inserting a unitary right factor before every query preserves well-formedness. -/
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

/-- The expected query count of the transformed circuit with oracle `O` equals that of the
original circuit with oracle `O * K`. -/
theorem observedQueryRightFactor_expected [Fintype I] [DecidableEq I]
    (O K : Matrix I I ℂ) (P : ObservedCircuit I) (psi : QState I) :
    expectedObservedQueries O (observedQueryRightFactor K P) psi =
      expectedObservedQueries (O * K) P psi := by
  simp only [expectedObservedQueries_eq_sum, observedQueryRightFactor_traces,
    List.map_map, Function.comp_def, addQueryGates]

/-- Events determined by acceptance and outcome history have the same mass for the transformed
circuit with oracle `O` and the original circuit with oracle `O * K`. -/
theorem observedQueryRightFactor_event [Fintype I] [DecidableEq I]
    (O K : Matrix I I ℂ) (P : ObservedCircuit I) (psi : QState I)
    (event : Bool → List (ℕ × ℕ) → Bool) :
    observedEventMass O (observedQueryRightFactor K P) psi
        (fun t => event t.accepted t.outcomes) =
      observedEventMass (O * K) P psi (fun t => event t.accepted t.outcomes) := by
  simp only [observedEventMass, observedQueryRightFactor_traces, List.map_map,
    Function.comp_def, addQueryGates]

end Qatlib.Concepts.AdversaryBounds.AdvDuality
