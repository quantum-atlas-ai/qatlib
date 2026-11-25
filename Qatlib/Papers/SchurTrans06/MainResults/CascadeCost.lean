/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SchurTrans06.MainResults.CostDefs

@[expose] public section

/-!
# The modeled Clebsch–Gordan cascade cost

The Schur cost model sums the Clebsch–Gordan costs of successive cascade
stages. Expanding the dimension recursion identifies each charged Wigner
transform and keeps the existing model's precision allocation.
-/

set_option autoImplicit false

namespace Qatlib.Papers.SchurTrans06.MainResults

open Qatlib.Papers.SchurTrans06.MainResults
open scoped BigOperators

/-- The cascade budget is the double sum of modeled reduced Wigner transform costs. -/
theorem schurCost_sum (n d : ℕ) (ε : ℝ) :
    sourceSchurCost n d ε =
      ∑ k ∈ Finset.range (n - 1), ∑ i ∈ Finset.range (d - 1),
        tHatCost (k + 1) (i + 2) (ε / ((n : ℝ) + 1)) := by
  simp only [sourceSchurCost, sourceCGCost_eq_sum]

end Qatlib.Papers.SchurTrans06.MainResults
