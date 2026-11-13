/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSearchBoyer96.MainResults.QueryScope

/-!
# Fixed and expected search query budgets

This module collects the corrected fixed query lower bounds associated with Theorems 7 and 8 of
[BoyerEtAl1998]. The explicit 64 address construction `source_expected_query_counterexample64`
illustrates why an expected query budget requires a separate formulation.

## Main statements

* `source_fixed_query_bounds`: Packages the corrected fixed budget statements.
* `source_expected_query_counterexample64`: Certifies a normalized search construction with
  expected query count 8/3.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option autoImplicit false
open scoped Classical
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AmplitudeSearch.InterruptMin
open Qatlib.Concepts.SearchStopping.QueryLowerBound
namespace Qatlib.Papers.QSearchBoyer98.QueryModels
universe u v

/-- Collects the corrected fixed query formulations of Theorems 7 and 8. See [BoyerEtAl1998]. -/
theorem source_fixed_query_bounds : Theorem7Corrected.{u,v} ∧ Theorem8Corrected.{u,v} :=
  Qatlib.Papers.QSearchBoyer96.MainResults.source_fixed_query_bounds

/-- Certifies a normalized unitary search construction on 64 addresses with success at least one
half and expected query count 8/3, strictly below ⌊sin(π/8)√64⌋. See [BoyerEtAl1998]. -/
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
  Qatlib.Papers.QSearchBoyer96.MainResults.source_expected_query_counterexample64

end Qatlib.Papers.QSearchBoyer98.QueryModels
