/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.ExpectedQueryCounterexample
import Qatlib.Concepts.SearchStopping.QueryLowerBound.Theorem7CorrectedTigh
import Qatlib.Concepts.SearchStopping.QueryLowerBound.Theorem8CorrectedTigh
set_option warningAsError false

set_option autoImplicit false
open scoped Classical
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AmplitudeSearch.InterruptMin
open Qatlib.Concepts.SearchStopping.QueryLowerBound
namespace Qatlib.Papers.QSearchBoyer96.MainResults
universe u v

theorem source_fixed_query_bounds : Theorem7Corrected.{u,v} ∧ Theorem8Corrected.{u,v} :=
  ⟨theorem7Corrected, theorem8Corrected⟩

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
