/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.ExpectedQueryCounterexample
import Qatlib.Concepts.SearchStopping.QueryLowerBound.Theorem7CorrectedTigh
import Qatlib.Concepts.SearchStopping.QueryLowerBound.Theorem8CorrectedTigh

/-!
# Fixed-query bounds and an expected-query example

This module collects the corrected fixed-query formulations of the search lower bounds in
`source_fixed_query_bounds`. The finite example `source_expected_query_counterexample64`
provides normalized states, unitary branches, and a probability law with success at least one
half and expected query count 8/3, below the stated fixed-query threshold.

The source paper is [BoyerEtAl1998].

## Main statements

* `source_fixed_query_bounds`: The corrected fixed-query formulations `Theorem7Corrected` and
  `Theorem8Corrected` both hold.
* `source_expected_query_counterexample64`: The 64-item construction has normalized initial
  states, unitary branch circuits and oracles, and a nonnegative normalized output law for each
  marked item. Its success probability is at least 1/2 and its expected query count is 8/3,
  strictly below ⌊sin(π/8)√64⌋.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option autoImplicit false
open scoped Classical
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AmplitudeSearch.InterruptMin
open Qatlib.Concepts.SearchStopping.QueryLowerBound
namespace Qatlib.Papers.QSearchBoyer96.MainResults
universe u v

/-- The corrected fixed-query formulations `Theorem7Corrected` and `Theorem8Corrected` both hold
[BoyerEtAl1998]. -/
theorem source_fixed_query_bounds : Theorem7Corrected.{u,v} ∧ Theorem8Corrected.{u,v} :=
  ⟨theorem7Corrected, theorem8Corrected⟩

/-- The 64-item construction has normalized initial states, unitary branch circuits and oracles,
and a nonnegative normalized output law for each marked item. Its success probability is at
least 1/2 and its expected query count is 8/3, strictly below ⌊sin(π/8)√64⌋ [BoyerEtAl1998]. -/
theorem source_expected_query_counterexample64 :
    Normalized BudgetCoin64 ∧ Normalized BudgetStart64 ∧
    (∀ b, IsUnitaryCircuit (BudgetBranch64 b)) ∧
    (∀ y : Fin 64, BudgetOracle64 y ∈ Matrix.unitaryGroup (Fin 64 × Bool) ℂ ∧
      (∀ o, 0 ≤ BudgetMass64 y o) ∧
      (∑ o : Bool × Fin 64, BudgetMass64 y o) = 1 ∧
      (1 / 2 : ℝ) ≤ ∑ b : Bool, BudgetMass64 y (b, y) ∧
      (∑ o : Bool × Fin 64, BudgetMass64 y o * (BudgetQueries64 o : ℝ)) = 8 / 3 ∧
      (∑ o : Bool × Fin 64, BudgetMass64 y o * (BudgetQueries64 o : ℝ)) <
        (⌊Real.sin (Real.pi / 8) * Real.sqrt 64⌋ : ℤ)) :=
  expected_query_counterexample64

end Qatlib.Papers.QSearchBoyer96.MainResults
