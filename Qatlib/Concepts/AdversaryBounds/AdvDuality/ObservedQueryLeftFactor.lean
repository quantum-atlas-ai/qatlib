/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedQueryRightFactor

/-!
# Left factors of observed oracle queries

`observedQueryLeftFactor` inserts a fixed gate after each oracle query, implementing the product
oracle `L * O`. The resulting traces have one extra gate per query, while the structural query
budget, expected query count, and events depending on acceptance and outcomes agree with the
product-oracle execution. This uses the circuit composition convention of [NielsenChuang2010].

## Main statements

* `observedQueryLeftFactor_traces`: Traces agree with the product-oracle traces after adjusting
  gate counts.
* `observedQueryLeftFactor_wellFormed`: A unitary left factor preserves well-formedness.

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

/-- Inserts the gate `L` after every oracle query of an observed circuit, implementing left
multiplication of the oracle by `L`. -/
noncomputable def observedQueryLeftFactor (L : Matrix I I ℂ) :
    ObservedCircuit I → ObservedCircuit I
  | .halt accepted => .halt accepted
  | .step (.gate U) next => .step (.gate U) (observedQueryLeftFactor L next)
  | .step .query next => .step .query (.step (.gate L) (observedQueryLeftFactor L next))
  | .measure n label next => .measure n label (fun o => observedQueryLeftFactor L (next o))
  | .project M onFalse onTrue =>
      .project M (observedQueryLeftFactor L onFalse) (observedQueryLeftFactor L onTrue)

/-- Executing the transformed circuit with oracle `O` gives the traces for oracle `L * O`, with
one additional gate counted per query. -/
theorem observedQueryLeftFactor_traces [Fintype I] [DecidableEq I]
    (O L : Matrix I I ℂ) (P : ObservedCircuit I) (psi : QState I) :
    observedTraces O (observedQueryLeftFactor L P) psi =
      (observedTraces (L * O) P psi).map addQueryGates := by
  induction P generalizing psi with
  | halt accepted => simp [observedQueryLeftFactor, observedTraces, addQueryGates]
  | step s next ih =>
    cases s with
    | gate U =>
      simp only [observedQueryLeftFactor, observedTraces, ih, List.map_map,
        Function.comp_def, addQueryGates, Nat.add_right_comm]
    | query =>
      simp only [observedQueryLeftFactor, observedTraces, ← applyGate_mul, ih,
        List.map_map, Function.comp_def, addQueryGates, Nat.add_assoc]
  | measure n label next ih =>
    simp only [observedQueryLeftFactor, observedTraces, ih, List.map_flatten,
      List.map_ofFn, List.map_map, Function.comp_def, addQueryGates]
  | project M onFalse onTrue ihFalse ihTrue =>
    simp only [observedQueryLeftFactor, observedTraces, ihFalse, ihTrue,
      List.map_append, List.map_map, Function.comp_def, addQueryGates]

/-- Inserting a left factor after every query preserves the structural query budget. -/
theorem observedQueryLeftFactor_budget [Fintype I] [DecidableEq I]
    (L : Matrix I I ℂ) (P : ObservedCircuit I) :
    observedQueryBudget (observedQueryLeftFactor L P) = observedQueryBudget P := by
  induction P with
  | halt accepted => rfl
  | step s next ih =>
    cases s <;> simp only [observedQueryLeftFactor, observedQueryBudget, ih]
  | measure n label next ih =>
    simp only [observedQueryLeftFactor, observedQueryBudget, ih]
  | project M onFalse onTrue ihFalse ihTrue =>
    simp only [observedQueryLeftFactor, observedQueryBudget, ihFalse, ihTrue]

/-- Inserting a unitary left factor after every query preserves well-formedness. -/
theorem observedQueryLeftFactor_wellFormed [Fintype I] [DecidableEq I]
    (L : Matrix I I ℂ) (hL : L ∈ Matrix.unitaryGroup I ℂ)
    (P : ObservedCircuit I) (hP : observedWellFormed P) :
    observedWellFormed (observedQueryLeftFactor L P) := by
  induction P with
  | halt accepted => trivial
  | step s next ih =>
    cases s with
    | gate U => exact ⟨hP.1, ih hP.2⟩
    | query => exact ⟨hL, ih hP⟩
  | measure n label next ih => exact fun o => ih o (hP o)
  | project M onFalse onTrue ihFalse ihTrue =>
    exact ⟨hP.1, ihFalse hP.2.1, ihTrue hP.2.2⟩

/-- The expected query count of the transformed circuit with oracle `O` equals that of the
original circuit with oracle `L * O`. -/
theorem observedQueryLeftFactor_expected [Fintype I] [DecidableEq I]
    (O L : Matrix I I ℂ) (P : ObservedCircuit I) (psi : QState I) :
    expectedObservedQueries O (observedQueryLeftFactor L P) psi =
      expectedObservedQueries (L * O) P psi := by
  simp only [expectedObservedQueries_eq_sum, observedQueryLeftFactor_traces,
    List.map_map, Function.comp_def, addQueryGates]

/-- Events determined by acceptance and outcome history have the same mass for the transformed
circuit with oracle `O` and the original circuit with oracle `L * O`. -/
theorem observedQueryLeftFactor_event [Fintype I] [DecidableEq I]
    (O L : Matrix I I ℂ) (P : ObservedCircuit I) (psi : QState I)
    (event : Bool → List (ℕ × ℕ) → Bool) :
    observedEventMass O (observedQueryLeftFactor L P) psi
        (fun t => event t.accepted t.outcomes) =
      observedEventMass (L * O) P psi (fun t => event t.accepted t.outcomes) := by
  simp only [observedEventMass, observedQueryLeftFactor_traces, List.map_map,
    Function.comp_def, addQueryGates]

end Qatlib.Concepts.AdversaryBounds.AdvDuality
