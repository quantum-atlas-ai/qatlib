/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.ExpectedQueryCounterexample
import Qatlib.Concepts.SearchStopping.QueryLowerBound.Theorem7CorrectedTigh
import Qatlib.Concepts.SearchStopping.QueryLowerBound.Theorem8CorrectedTigh
import Qatlib.Papers.QSearchBoyer96.MainResults.Sec2KnownCountIterations
import Mathlib.Tactic

/-!
# Grover circuit success and query counts

This module connects the exact Grover success formula to execution of `GroverCircuit` from
`Uniform`. It proves unitarity and exact query counts, then combines the floor iteration choice
with the marked-density failure bound and the (π/4)√(N/t) query budget.

The source paper is [BoyerEtAl1998].

## Main statements

* `actual_grover_queries_and_success`: On a nonempty finite search space, the j-step Grover
  circuit is unitary, uses exactly j queries, and succeeds with probability sin²((2j + 1)θ)
  under the stated angle and nonzero sine and cosine hypotheses.
* `actual_floor_success_and_cost`: For a nonempty marked set and the stated angle conditions,
  the floor-iteration Grover circuit has failure probability at most the marked density and uses
  exactly `groverIterations θ` queries, bounded by (π/4)√(N/t).

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option warningAsError false

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Concepts.AmplitudeSearch.InterruptMin

namespace Qatlib.Papers.QSearchBoyer96.MainResults

/-- On a nonempty finite search space, the j-step Grover circuit is unitary, uses exactly j
queries, and succeeds with probability sin²((2j + 1)θ) under the stated angle and nonzero
sine and cosine hypotheses [BoyerEtAl1998]. -/
theorem actual_grover_queries_and_success {I : Type} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (θ : ℝ)
    (hθ : (Real.sin θ)^2 = (A.card : ℝ)/(Fintype.card I : ℝ))
    (hs : Real.sin θ ≠ 0) (hc : Real.cos θ ≠ 0) (j : ℕ) :
    QueryCount (GroverCircuit I j) = j ∧ IsUnitaryCircuit (GroverCircuit I j) ∧
    MeasureProb (Run (SetOracle A) (GroverCircuit I j) (Uniform I)) A =
      (Real.sin ((2*(j:ℝ)+1)*θ))^2 := by
  exact ⟨queryCount_groverCircuit j, isUnitaryCircuit_groverCircuit hN j,
    measureProb_groverState hN A θ hθ hs hc j⟩

/-- For a nonempty marked set and the stated angle conditions, the floor-iteration Grover
circuit has failure probability at most the marked density and uses exactly
`groverIterations θ` queries, bounded by (π/4)√(N/t) [BoyerEtAl1998]. -/
theorem actual_floor_success_and_cost {I : Type} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (θ : ℝ)
    (hA : 0 < A.card)
    (hθ : (Real.sin θ)^2 = (A.card : ℝ)/(Fintype.card I : ℝ))
    (hs : 0 < Real.sin θ) (hc : Real.cos θ ≠ 0)
    (hθpos : 0 < θ) (hθhalf : θ ≤ Real.pi/2) :
    1 - MeasureProb (Run (SetOracle A) (GroverCircuit I (groverIterations θ))
      (Uniform I)) A ≤ (A.card : ℝ)/(Fintype.card I : ℝ) ∧
    QueryCount (GroverCircuit I (groverIterations θ)) = groverIterations θ ∧
    (QueryCount (GroverCircuit I (groverIterations θ)) : ℝ) ≤
      Real.pi/4 * Real.sqrt ((Fintype.card I : ℝ)/(A.card : ℝ)) := by
  have h := almost_certain_success_within_budget hN A θ hA hθ hs hc hθpos hθhalf
  exact ⟨h.1, queryCount_groverCircuit _, by rw [queryCount_groverCircuit]; exact h.2⟩

end Qatlib.Papers.QSearchBoyer96.MainResults
