/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSearchSurvey05.MainResults.Defs
import Qatlib.Concepts.QueryComplexity.DegreeMethod.Complexity
import Qatlib.Concepts.SearchStopping.KnownCount.Section3QueryBoundSubgoalAfas
import Qatlib.Concepts.SearchStopping.UnknownCount.SearchTimeout
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Search bounds on finite grids

This module records the grid cardinality and search estimates associated with the spatial search
discussion of [Ambainis2005]. The statements `theorem41_unique_2d` and `theorem41_general_query`
give a unique item bound on two dimensional grids and retry reach and iteration bounds for
nonempty marked sets on higher dimensional grids.

## Main statements

* `theorem41_unique_2d`: Gives a √(n²) log(n²) fixed space query bound.
* `theorem41_general_query`: Gives explicit retry reach and prefix iteration estimates.

## References

* [Ambainis, 2005][Ambainis2005]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped Classical
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Concepts.SearchStopping.UnknownCount

namespace Qatlib.Papers.QSearchSurvey05.MainResults

/-- A d dimensional grid with n cells per coordinate has cardinality n^d. See [Ambainis2005]. -/
theorem gridCard (d n : ℕ) : Fintype.card (GridCell d n) = n ^ d := by
  simp [GridCell]

/-- There is a positive universal constant C such that unique item search on an n by n grid, for
n ≥ 2, has error at most one half within C√(n²) log(n²) queries. See [Ambainis2005]. -/
theorem theorem41_unique_2d :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∃ k : ℕ,
      FixedSpaceQueryUpperBound (MarkOracle (I := GridCell 2 n)) (fun w => {w}) (1 / 2) k ∧
        (k : ℝ) ≤ C * Real.sqrt ((n : ℝ) ^ 2) * Real.log ((n : ℝ) ^ 2) := by
  refine ⟨Real.pi / 4, by positivity, ?_⟩
  intro n hn
  have hcard : Fintype.card (GridCell 2 n) = n ^ 2 := gridCard 2 n
  have h2 : 2 ≤ Fintype.card (GridCell 2 n) := by
    rw [hcard]; nlinarith [Nat.cast_nonneg (α := ℝ) n]
  obtain ⟨k, hupper, hbudget⟩ := singleTarget_searchClaim (I := GridCell 2 n) h2
  refine ⟨k, hupper, ?_⟩
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hbud : (k : ℝ) ≤ (Real.pi / 4) * Real.sqrt ((n : ℝ) ^ 2) := by
    have h := hbudget
    rw [hcard] at h
    have hcast : ((n ^ 2 : ℕ) : ℝ) = (n : ℝ) ^ 2 := by push_cast; ring
    rw [hcast] at h
    have hden : Real.sqrt (1 / (n : ℝ) ^ 2) = 1 / (n : ℝ) := by
      rw [show (1 : ℝ) / (n : ℝ) ^ 2 = (1 / (n : ℝ)) ^ 2 by field_simp]
      rw [Real.sqrt_sq (by positivity)]
    rw [hden] at h
    have hrhs : Real.pi / (4 * (1 / (n : ℝ))) = (Real.pi / 4) * (n : ℝ) := by
      field_simp
    rw [hrhs] at h
    have hsqrtn : Real.sqrt ((n : ℝ) ^ 2) = (n : ℝ) := Real.sqrt_sq (le_of_lt hnpos)
    rw [hsqrtn]
    exact h
  have hlog : (1 : ℝ) ≤ Real.log ((n : ℝ) ^ 2) := by
    have h4 : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by
      have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith
    have hexp : (1 : ℝ) ≤ Real.log 4 := by
      have h := Real.log_le_log (Real.exp_pos 1)
        (le_of_lt (lt_trans Real.exp_one_lt_three (by norm_num : (3 : ℝ) < 4)))
      rwa [Real.log_exp] at h
    exact le_trans hexp (Real.log_le_log (by norm_num) h4)
  have hsqrtpos : (0 : ℝ) ≤ Real.sqrt ((n : ℝ) ^ 2) := Real.sqrt_nonneg _
  calc (k : ℝ) ≤ (Real.pi / 4) * Real.sqrt ((n : ℝ) ^ 2) := hbud
    _ = (Real.pi / 4) * Real.sqrt ((n : ℝ) ^ 2) * 1 := by ring
    _ ≤ (Real.pi / 4) * Real.sqrt ((n : ℝ) ^ 2) * Real.log ((n : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left hlog
        positivity

/-- For d ≥ 1 and n ≥ 2, gives a common retry index K ≤ 6√(n^d) for every nonempty marked set,
with retry reach at most 3/4 and worst prefix iteration count at most 7√(n^d). See
[Ambainis2005]. -/
theorem theorem41_general_query (d n : ℕ) (_hd : 1 ≤ d) (hn : 2 ≤ n) :
    ∃ K : ℕ, (K : ℝ) ≤ 6 * Real.sqrt ((n : ℝ) ^ d) ∧
      ∀ A : Finset (GridCell d n), 0 < A.card →
        Qatlib.Concepts.AmplitudeSearch.InterruptMin.RetryReach
          A (ExponentialSizes (Fintype.card (GridCell d n))) (K + 1) ≤ (3 / 4 : ℝ) ∧
        (WorstPrefixIterations (ExponentialSizes (Fintype.card (GridCell d n))) (K + 1) : ℝ) ≤
          7 * Real.sqrt ((n : ℝ) ^ d) := by
  have hcard : Fintype.card (GridCell d n) = n ^ d := gridCard d n
  have hN : 0 < Fintype.card (GridCell d n) := by
    rw [hcard]; positivity
  obtain ⟨K, hK, hall⟩ := search_uniform_timeout (I := GridCell d n) hN
  refine ⟨K, ?_, ?_⟩
  · have h := hK
    rw [hcard] at h
    simpa [Nat.cast_pow] using h
  · intro A hA
    obtain ⟨hiter, hreach⟩ := hall 1
    refine ⟨?_, ?_⟩
    · simpa using hreach A hA
    · have h := hiter
      have h7 : (6 + ((1 : ℕ) : ℝ)) = (7 : ℝ) := by norm_num
      rw [h7] at h
      rw [hcard] at h
      simpa [Nat.cast_pow] using h

end Qatlib.Papers.QSearchSurvey05.MainResults
