/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Field

/-!
# Scalar search costs for graph resource estimates

This module defines the real-valued search-cost expressions used in the matching and
network-flow analysis of [AmbainisSpalek2006]. The logarithmic factor `logFactor n = log (n +
3)` is positive and at least one for every natural `n`.

The finite-sum inequality `sum_sqrt_mul_le` controls sums of paired square roots and supports
later aggregation of the vertex costs.

## Main statements

* `one_le_logFactor`: the logarithmic factor is at least one.
* `sum_sqrt_mul_le`: a square-root form of the finite Cauchy-Schwarz inequality.
* `listVertexCost`: the list-model per-vertex budget expression.

## References

* [Ambainis and Špalek, 2006][AmbainisSpalek2006]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QMatchingFlow05.SearchTools

/-- The square-root search-cost expression `c * √N`. -/
def searchCost (c N : ℝ) : ℝ := c * Real.sqrt N

/-- The logarithmic factor `log (n + 3)`. -/
def logFactor (n : ℕ) : ℝ := Real.log ((n : ℝ) + 3)

/-- The factor `logFactor n` is strictly positive for every natural `n`. -/
theorem logFactor_pos (n : ℕ) : 0 < logFactor n := by
  unfold logFactor
  apply Real.log_pos
  have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- The factor `logFactor n` is at least one for every natural `n`. -/
theorem one_le_logFactor (n : ℕ) : 1 ≤ logFactor n := by
  unfold logFactor
  rw [Real.le_log_iff_exp_le (by positivity)]
  have h3 : Real.exp 1 < 3 := Real.exp_one_lt_three
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- For nonnegative functions on a finite type, the sum of `√(f i * g i)` is at most `√(∑ i, f
i) * √(∑ i, g i)`. -/
theorem sum_sqrt_mul_le {ι : Type*} [Fintype ι] (f g : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    ∑ i, Real.sqrt (f i * g i) ≤
      Real.sqrt (∑ i, f i) * Real.sqrt (∑ i, g i) := by
  calc ∑ i, Real.sqrt (f i * g i)
      = ∑ i, Real.sqrt (f i) * Real.sqrt (g i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Real.sqrt_mul (hf i)]
    _ ≤ Real.sqrt (∑ i, f i) * Real.sqrt (∑ i, g i) :=
        Real.sum_sqrt_mul_sqrt_le Finset.univ hf hg

/-- The adjacency-model vertex-cost expression `2 * searchCost c n * logFactor n`. -/
def adjacencyVertexCost (c : ℝ) (n : ℕ) : ℝ := 2 * searchCost c (n : ℝ) * logFactor n

/-- The list-model vertex-cost expression `c * (√(nV * dV) + √(dV + 1))`. -/
def listVertexCost (c nV dV : ℝ) : ℝ :=
  c * (Real.sqrt (nV * dV) + Real.sqrt (dV + 1))

end Qatlib.Papers.QMatchingFlow05.SearchTools

end
