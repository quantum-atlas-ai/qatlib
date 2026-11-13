/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedQueryBudget
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Query visits and expected query counts

`observedQueryVisits` lists the states immediately before each oracle call together with the
number of earlier calls on their branch. The module gives recursive formulas for
`expectedObservedQueries` and proves that it equals the sum of the masses of these visit states.
This accounting supports query analyses in the model of [NielsenChuang2010].

## Main statements

* `observedQueryVisits_lt_budget`: Every visit index is strictly below the structural query
  budget.
* `observedQueryVisits_mass`: The sum of query visit masses equals the expected query count.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.AdaptiveQuery.RawProcess
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Lists each pre-query branch state together with its zero-based query index along that
branch, traversing all measurement outcomes. -/
noncomputable def observedQueryVisits (O : Matrix I I ℂ) :
    ObservedCircuit I → QState I → List (ℕ × QState I)
  | .halt _, _ => []
  | .step (.gate G) next, psi => observedQueryVisits O next (ApplyGate G psi)
  | .step .query next, psi =>
      (0, psi) :: (observedQueryVisits O next (ApplyGate O psi)).map
        (fun v => (v.1 + 1, v.2))
  | .measure n label next, psi =>
      (List.ofFn (fun o : Fin n => observedQueryVisits O (next o)
        (Collapse psi (Finset.univ.filter (fun i => label i = o))))).flatten
  | .project M onFalse onTrue, psi =>
      observedQueryVisits O onFalse (ProjectiveBranch M false psi) ++
        observedQueryVisits O onTrue (ProjectiveBranch M true psi)

/-- The index of every recorded query visit is strictly smaller than the structural query
budget. -/
theorem observedQueryVisits_lt_budget (O : Matrix I I ℂ) (P : ObservedCircuit I)
    (psi : QState I) (v : ℕ × QState I) (hv : v ∈ observedQueryVisits O P psi) :
    v.1 < observedQueryBudget P := by
  induction P generalizing psi v with
  | halt accepted => simp [observedQueryVisits] at hv
  | step s next ih =>
    cases s with
    | gate G => exact ih (ApplyGate G psi) v hv
    | query =>
      rcases List.mem_cons.mp hv with rfl | hv
      · exact Nat.zero_lt_succ _
      · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
        exact Nat.add_lt_add_right (ih (ApplyGate O psi) u hu) 1
  | measure n label next ih =>
    obtain ⟨xs, hxs, hv⟩ := List.mem_flatten.mp hv
    obtain ⟨o, rfl⟩ := List.mem_ofFn.mp hxs
    exact lt_of_lt_of_le (ih o _ v hv)
      (Finset.le_sup (f := fun j : Fin n => observedQueryBudget (next j))
        (Finset.mem_univ o))
  | project M onFalse onTrue ihFalse ihTrue =>
    rcases List.mem_append.mp hv with hv | hv
    · exact lt_of_lt_of_le (ihFalse _ v hv) (le_max_left _ _)
    · exact lt_of_lt_of_le (ihTrue _ v hv) (le_max_right _ _)

/-- A halted observed circuit has zero expected query count. -/
theorem expectedObservedQueries_halt (O : Matrix I I ℂ) (b : Bool) (psi : QState I) :
    expectedObservedQueries O (.halt b) psi = 0 := by
  simp [expectedObservedQueries_eq_sum, observedTraces]

/-- An initial fixed gate contributes no queries and passes its transformed state to the
continuation. -/
theorem expectedObservedQueries_gate (O G : Matrix I I ℂ) (P : ObservedCircuit I)
    (psi : QState I) : expectedObservedQueries O (.step (.gate G) P) psi =
      expectedObservedQueries O P (ApplyGate G psi) := by
  simp only [expectedObservedQueries_eq_sum, observedTraces, List.map_map,
    Function.comp_def]

/-- For a unitary oracle and well-formed continuation, an initial query adds the input branch
mass to the continuation's expected query count. -/
theorem expectedObservedQueries_query (O : Matrix I I ℂ)
    (hO : O ∈ Matrix.unitaryGroup I ℂ) (P : ObservedCircuit I)
    (hP : observedWellFormed P) (psi : QState I) :
    expectedObservedQueries O (.step .query P) psi =
      branchMass psi + expectedObservedQueries O P (ApplyGate O psi) := by
  simp only [expectedObservedQueries_eq_sum, observedTraces, List.map_map,
    Function.comp_def, Nat.cast_add, Nat.cast_one, mul_add, mul_one, List.sum_map_add]
  rw [observedTraces_mass O hO P hP (ApplyGate O psi)]
  have hm : branchMass (ApplyGate O psi) = branchMass psi :=
    measureProb_applyGate_univ hO psi
  rw [hm, add_comm]

/-- The expected query count after a labeled measurement is the sum of the continuation counts
for the collapsed outcome states. -/
theorem expectedObservedQueries_measure (O : Matrix I I ℂ) (n : ℕ)
    (label : I → Fin n) (next : Fin n → ObservedCircuit I) (psi : QState I) :
    expectedObservedQueries O (.measure n label next) psi =
      ∑ o : Fin n, expectedObservedQueries O (next o)
        (Collapse psi (Finset.univ.filter (fun i => label i = o))) := by
  simp only [expectedObservedQueries_eq_sum, observedTraces, List.map_flatten,
    List.sum_flatten, List.map_map, Function.comp_def, List.map_ofFn, List.sum_ofFn]

/-- The expected query count after a binary projective branch is the sum of the counts in its
two continuations. -/
theorem expectedObservedQueries_project (O M : Matrix I I ℂ)
    (onFalse onTrue : ObservedCircuit I) (psi : QState I) :
    expectedObservedQueries O (.project M onFalse onTrue) psi =
      expectedObservedQueries O onFalse (ProjectiveBranch M false psi) +
        expectedObservedQueries O onTrue (ProjectiveBranch M true psi) := by
  simp only [expectedObservedQueries_eq_sum, observedTraces, List.map_append,
    List.sum_append, List.map_map, Function.comp_def]

/-- For a unitary oracle and well-formed circuit, the sum of the masses of all pre-query visit
states equals the expected query count. -/
theorem observedQueryVisits_mass (O : Matrix I I ℂ)
    (hO : O ∈ Matrix.unitaryGroup I ℂ) (P : ObservedCircuit I)
    (hP : observedWellFormed P) (psi : QState I) :
    ((observedQueryVisits O P psi).map (fun v => branchMass v.2)).sum =
      expectedObservedQueries O P psi := by
  induction P generalizing psi with
  | halt accepted => simp [observedQueryVisits, expectedObservedQueries_halt]
  | step s next ih =>
    cases s with
    | gate G =>
      simpa only [observedQueryVisits, expectedObservedQueries_gate] using
        ih hP.2 (ApplyGate G psi)
    | query =>
      simp only [observedQueryVisits, List.map_cons, List.sum_cons, List.map_map,
        Function.comp_def]
      rw [ih hP (ApplyGate O psi)]
      exact (expectedObservedQueries_query O hO next hP psi).symm
  | measure n label next ih =>
    rw [expectedObservedQueries_measure]
    simp only [observedQueryVisits, List.map_flatten, List.sum_flatten,
      List.map_map, Function.comp_def, List.map_ofFn, List.sum_ofFn]
    have hnext (o : Fin n) := ih o (hP o)
    simp only [hnext]
  | project M onFalse onTrue ihFalse ihTrue =>
    rw [expectedObservedQueries_project]
    simp only [observedQueryVisits, List.map_append, List.sum_append,
      ihFalse hP.2.1, ihTrue hP.2.2]

end Qatlib.Concepts.AdversaryBounds.AdvDuality
