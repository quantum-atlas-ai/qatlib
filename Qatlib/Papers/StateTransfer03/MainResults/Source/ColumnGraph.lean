/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Column sizes and effective chain couplings

`columnSize` assigns binomial column sizes to the graph construction. The file proves their
total size and the balance of edge counts between adjacent columns, then evaluates the
corresponding normalized coupling as `sqrt (n * (N - n))`. See [ChristandlEtAl2004].

## Main statements

* `columnSize_sum`: the column sizes total `2 ^ (N - 1)`.
* `column_edge_count`: adjacent columns give the same edge count.
* `column_coupling`: the normalized edge count has a square root form.

## References

* [Christandl et al., 2004][ChristandlEtAl2004]
-/

namespace Qatlib.Papers.StateTransfer03.MainResults.Source

open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

/-- The size of column `n`, defined as the binomial coefficient `choose (N - 1) (n - 1)`. -/
def columnSize (N n : ℕ) : ℕ := Nat.choose (N - 1) (n - 1)

/-- For positive `N`, the sizes of columns one through `N` sum to `2 ^ (N - 1)`. See
[ChristandlEtAl2004]. -/
theorem columnSize_sum (N : ℕ) (hN : 0 < N) :
    ∑ n ∈ Finset.range N, columnSize N (n + 1) = 2 ^ (N - 1) := by
  unfold columnSize
  simp only [Nat.add_sub_cancel]
  simpa [Nat.sub_add_cancel hN] using Nat.sum_range_choose (N - 1)

/-- For `1 ≤ n < N`, counting adjacent-column edges from either side gives `columnSize N n * (N
- n) = columnSize N (n + 1) * n` over the reals. See [ChristandlEtAl2004]. -/
theorem column_edge_count (N n : ℕ) (hn : 1 ≤ n) (hnN : n < N) :
    (columnSize N n : ℝ) * ((N : ℝ) - n) =
      (columnSize N (n + 1) : ℝ) * (n : ℝ) := by
  unfold columnSize
  simp only [Nat.add_sub_cancel]
  have h := Nat.choose_succ_right_eq (N - 1) (n - 1)
  rw [Nat.sub_add_cancel hn, show N - 1 - (n - 1) = N - n by omega] at h
  have h' : ((Nat.choose (N - 1) n : ℝ) * (n : ℝ)) =
      ((Nat.choose (N - 1) (n - 1) : ℝ) * ((N : ℝ) - (n : ℝ))) := by
    have h1 : ((((N - 1).choose n * n : ℕ) : ℝ)) =
        (((((N - 1).choose (n - 1) * (N - n) : ℕ) : ℝ))) := by
      exact_mod_cast h
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : n ≤ N)] at h1
    exact h1
  linarith

/-- For `1 ≤ n < N`, the edge count divided by the square root of the product of adjacent column
sizes equals `sqrt (n * (N - n))`. See [ChristandlEtAl2004]. -/
theorem column_coupling (N n : ℕ) (hn : 1 ≤ n) (hnN : n < N) :
    ((columnSize N n : ℝ) * ((N : ℝ) - n)) /
        Real.sqrt ((columnSize N n : ℝ) * (columnSize N (n + 1) : ℝ)) =
      Real.sqrt ((n : ℝ) * ((N : ℝ) - n)) := by
  have hchoose := column_edge_count N n hn hnN
  have hApos : 0 < (columnSize N n : ℝ) := by
    unfold columnSize
    exact_mod_cast Nat.choose_pos (by omega : n - 1 ≤ N - 1)
  have hBpos : 0 < (columnSize N (n + 1) : ℝ) := by
    unfold columnSize
    exact_mod_cast Nat.choose_pos (by omega : n ≤ N - 1)
  have hABpos : 0 < (columnSize N n : ℝ) * (columnSize N (n + 1) : ℝ) :=
    mul_pos hApos hBpos
  have hNn : (0 : ℝ) < (N : ℝ) - (n : ℝ) := by
    have : (n : ℝ) < (N : ℝ) := by exact_mod_cast hnN
    linarith
  have hAnonneg : 0 ≤ (columnSize N n : ℝ) * ((N : ℝ) - (n : ℝ)) := by positivity
  rw [← Real.sqrt_sq hAnonneg]
  rw [← Real.sqrt_div (show (0 : ℝ) ≤ ((columnSize N n : ℝ) * ((N : ℝ) - n)) ^ 2 by positivity)
    ((columnSize N n : ℝ) * (columnSize N (n + 1) : ℝ))]
  have hnn_nonneg : 0 ≤ (n : ℝ) * ((N : ℝ) - (n : ℝ)) :=
    mul_nonneg (by positivity) (le_of_lt hNn)
  rw [Real.sqrt_inj (div_nonneg (sq_nonneg _) (le_of_lt hABpos)) hnn_nonneg]
  field_simp
  simpa [mul_comm] using hchoose

end

end Qatlib.Papers.StateTransfer03.MainResults.Source
