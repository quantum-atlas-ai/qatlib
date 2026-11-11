/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Section3QueryBoundSubgoalAfas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Grover search query upper bound

This module records the unique marked item query upper bound presented as Theorem 2.1 in
[Ambainis2005]. For at least two addresses, `theorem21_grover_search` supplies a fixed space
search algorithm with error at most one half and query budget at most (π/4)√N.

## Main statements

* `theorem21_grover_search`: Exhibits the fixed space Grover query upper bound.

## References

* [Ambainis, 2005][Ambainis2005]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Concepts.QueryComplexity.DegreeMethod

namespace Qatlib.Papers.QSearchSurvey05.MainResults

/-- For a finite address space of size at least two, unique marked item search has a fixed space
query upper bound with error one half and at most (π/4)√N queries. See [Ambainis2005]. -/
theorem theorem21_grover_search (I : Type*) [Fintype I] [DecidableEq I]
    (hN : 2 ≤ Fintype.card I) :
    ∃ k : ℕ,
      FixedSpaceQueryUpperBound (MarkOracle (I := I)) (fun w => {w}) (1 / 2) k ∧
        (k : ℝ) ≤ (Real.pi / 4) * Real.sqrt (Fintype.card I) := by
  obtain ⟨k, hupper, hbudget⟩ := singleTarget_searchClaim (I := I) hN
  refine ⟨k, hupper, ?_⟩
  have hcard : (0 : ℝ) < (Fintype.card I : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hN)
  have hsqrt : Real.sqrt (1 / (Fintype.card I : ℝ)) = 1 / Real.sqrt (Fintype.card I) := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
  calc (k : ℝ) ≤ Real.pi / (4 * Real.sqrt (1 / (Fintype.card I : ℝ))) := hbudget
    _ = (Real.pi / 4) * Real.sqrt (Fintype.card I) := by
        rw [hsqrt]
        field_simp

end Qatlib.Papers.QSearchSurvey05.MainResults
