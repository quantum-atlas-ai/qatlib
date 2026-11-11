/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Section3QueryBoundSubgoalAfas

/-!
# A square root query upper bound for singleton search

`section1_sqrtQueryBound` gives a fixed space query upper bound for singleton marked oracles on
any finite search space with at least two elements. Some integer query budget achieves success
at least one half and is bounded by `(π/4) * sqrt (Fintype.card I)`. See [Grover1997].

## Main statements

* `section1_sqrtQueryBound`: For any finite search space with at least two elements, some
  integer query budget at most `(π/4) * sqrt (Fintype.card I)` achieves a fixed space singleton
  search success bound of `1/2`.

## References

* [Grover, 1997][Grover1997]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.SearchStopping.KnownCount

namespace Qatlib.Papers.GroverSearch97.MainResults.SearchQueryBound

/-- For any finite search space with at least two elements, some integer query budget at most
`(π/4) * sqrt (Fintype.card I)` achieves a fixed space singleton search success bound of
`1/2`. -/
theorem section1_sqrtQueryBound (I : Type*) [Fintype I] [DecidableEq I]
    (hN : 2 ≤ Fintype.card I) :
    ∃ k : ℕ,
      FixedSpaceQueryUpperBound (MarkOracle (I := I)) (fun w => ({w} : Finset I))
        (1 / 2) k ∧
      (k : ℝ) ≤ Real.pi / 4 * Real.sqrt (Fintype.card I) := by
  have hpos : 0 < Fintype.card I := lt_of_lt_of_le (by norm_num) hN
  have hNpos : (0 : ℝ) < (Fintype.card I : ℝ) := by exact_mod_cast hpos
  have hsqrt : Real.sqrt (1 / (Fintype.card I : ℝ)) =
      1 / Real.sqrt (Fintype.card I : ℝ) := by
    rw [Real.sqrt_div' (1 : ℝ) (le_of_lt hNpos), Real.sqrt_one]
  have hbudget : Real.pi / (4 * Real.sqrt (1 / (Fintype.card I : ℝ))) =
      Real.pi / 4 * Real.sqrt (Fintype.card I : ℝ) := by
    rw [hsqrt]
    have hs : Real.sqrt (Fintype.card I : ℝ) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr hNpos)
    field_simp
  obtain ⟨k, hclaim, hk⟩ := singleTarget_searchClaim (I := I) hN
  exact ⟨k, hclaim, by rw [← hbudget]; exact hk⟩

end Qatlib.Papers.GroverSearch97.MainResults.SearchQueryBound
