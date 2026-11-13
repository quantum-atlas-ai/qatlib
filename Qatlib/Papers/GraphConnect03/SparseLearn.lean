/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GraphConnect03.MainResults.Defs
import Mathlib.Tactic
import Mathlib.Data.Real.Sqrt

/-!
# Known-sparsity matrix search costs

This module defines `sparseSearchCost` as the sum of Grover-search charges for recovering a
known number of nonzero entries in an `N`-by-`N` matrix. A telescoping square-root estimate
yields the bound `2 * N * √m`, its fixed-outdegree specialization, and a fixed-`N` comparison
with `√m`. See [DurrMhallaLei2003].

## Main statements

* `sum_inv_sqrt_succ_le`: The sum of `1/√(t + 1)` over `t < m` is at most `2√m`.
* `sparseSearchCost_le`: The known-sparsity search cost is at most `2 * N * √m`.
* `sparseSearchCost_outdeg`: With `N*k` nonzero entries, the search cost is at most `2 * N * √N
  * √k`.

## References

* [Durr et al., 2003][DurrMhallaLei2003]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.GraphConnect03.SparseLearn

open Qatlib.Papers.GraphConnect03.MainResults.Defs

/-- The sum of `√(N² / (t + 1))` for natural indices `t < m`. -/
def sparseSearchCost (N m : ℕ) : ℝ :=
  ∑ t ∈ Finset.range m, Real.sqrt ((N : ℝ) ^ 2 / ((t : ℝ) + 1))

/-- The reciprocal `1/√(t + 1)` is bounded by twice the square-root increment `√(t + 1) - √t`. -/
theorem inv_sqrt_succ_le (t : ℕ) :
    (1 : ℝ) / Real.sqrt ((t : ℝ) + 1) ≤
      2 * (Real.sqrt ((t : ℝ) + 1) - Real.sqrt (t : ℝ)) := by
  have hA : 0 < Real.sqrt ((t : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hAsq : Real.sqrt ((t : ℝ) + 1) * Real.sqrt ((t : ℝ) + 1) = (t : ℝ) + 1 :=
    Real.mul_self_sqrt (by positivity)
  have hBsq : Real.sqrt (t : ℝ) * Real.sqrt (t : ℝ) = (t : ℝ) :=
    Real.mul_self_sqrt (by positivity)
  rw [div_le_iff₀ hA]
  nlinarith [sq_nonneg (Real.sqrt ((t : ℝ) + 1) - Real.sqrt (t : ℝ))]

/-- The sum of `1/√(t + 1)` over `t < m` is at most `2√m` [DurrMhallaLei2003]. -/
theorem sum_inv_sqrt_succ_le (m : ℕ) :
    (∑ t ∈ Finset.range m, (1 : ℝ) / Real.sqrt ((t : ℝ) + 1)) ≤
      2 * Real.sqrt (m : ℝ) := by
  have hstep : ∀ t ∈ Finset.range m,
      (1 : ℝ) / Real.sqrt ((t : ℝ) + 1) ≤
        2 * (Real.sqrt ((t : ℝ) + 1) - Real.sqrt (t : ℝ)) :=
    fun t _ => inv_sqrt_succ_le t
  have hsum := Finset.sum_le_sum hstep
  have htelescope :
      (∑ t ∈ Finset.range m, 2 * (Real.sqrt ((t : ℝ) + 1) - Real.sqrt (t : ℝ))) =
        2 * Real.sqrt (m : ℝ) := by
    rw [← Finset.mul_sum]
    have h := Finset.sum_range_sub (fun t : ℕ => Real.sqrt (t : ℝ)) m
    simp only [Nat.cast_zero, Real.sqrt_zero, sub_zero] at h
    push_cast at h
    linarith
  have hsum' :
      (∑ t ∈ Finset.range m, 2 * (Real.sqrt ((t : ℝ) + 1) - Real.sqrt (t : ℝ))) ≤
        2 * Real.sqrt (m : ℝ) := by
    rw [htelescope]
  exact le_trans hsum hsum'

/-- For natural `N` and `t`, the square root of `N²/(t + 1)` equals `N/√(t + 1)`. -/
theorem sqrt_sq_div (N t : ℕ) :
    Real.sqrt ((N : ℝ) ^ 2 / ((t : ℝ) + 1)) =
      (N : ℝ) / Real.sqrt ((t : ℝ) + 1) := by
  rw [Real.sqrt_div (show (0 : ℝ) ≤ (N : ℝ) ^ 2 by positivity)]
  rw [Real.sqrt_sq (show (0 : ℝ) ≤ (N : ℝ) by positivity)]

/-- The known-sparsity search cost is at most `2 * N * √m` [DurrMhallaLei2003]. -/
theorem sparseSearchCost_le (N m : ℕ) :
    sparseSearchCost N m ≤ 2 * (N : ℝ) * Real.sqrt (m : ℝ) := by
  unfold sparseSearchCost
  calc
    (∑ t ∈ Finset.range m, Real.sqrt ((N : ℝ) ^ 2 / ((t : ℝ) + 1)))
        = ∑ t ∈ Finset.range m, (N : ℝ) / Real.sqrt ((t : ℝ) + 1) :=
          Finset.sum_congr rfl (fun t _ => sqrt_sq_div N t)
    _ = (N : ℝ) * ∑ t ∈ Finset.range m, (1 : ℝ) / Real.sqrt ((t : ℝ) + 1) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun t _ => by ring)
    _ ≤ (N : ℝ) * (2 * Real.sqrt (m : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_inv_sqrt_succ_le m) (by positivity)
    _ = 2 * (N : ℝ) * Real.sqrt (m : ℝ) := by ring

/-- The square root of a product of natural numbers cast to reals is the product of their square
roots. -/
theorem sqrt_nat_mul (a b : ℕ) :
    Real.sqrt ((a * b : ℕ) : ℝ) = Real.sqrt (a : ℝ) * Real.sqrt (b : ℝ) := by
  rw [Nat.cast_mul, Real.sqrt_mul (show (0 : ℝ) ≤ (a : ℝ) by positivity)]

/-- With `N*k` nonzero entries, the search cost is at most `2 * N * √N * √k`
[DurrMhallaLei2003]. -/
theorem sparseSearchCost_outdeg (N k : ℕ) :
    sparseSearchCost N (N * k) ≤
      2 * (N : ℝ) * (Real.sqrt (N : ℝ) * Real.sqrt (k : ℝ)) := by
  have h := sparseSearchCost_le N (N * k)
  rwa [sqrt_nat_mul] at h

/-- For fixed `N ≥ 1`, the known-sparsity search cost is bounded by a positive constant times
`√m` for every natural `m` [DurrMhallaLei2003]. -/
theorem sparseSearchCost_bigO (N : ℕ) (hN : 1 ≤ N) :
    IsBigOFrom (fun m : ℕ => sparseSearchCost N m) (fun m : ℕ => Real.sqrt (m : ℝ)) 0 := by
  refine ⟨2 * (N : ℝ), ?_, ?_⟩
  · have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    positivity
  · intro m _
    simpa [mul_assoc] using sparseSearchCost_le N m

end Qatlib.Papers.GraphConnect03.SparseLearn
