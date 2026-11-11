/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPrimality95.MainResults.CostDefs
import Qatlib.Foundations.CostRecurrences.FiniteWeights

/-!
# Finite-sum and recursion bounds for primality-test costs

This module proves algebraic estimates used to combine the running-time terms in [ChauLo1995].
`equation5_core` controls a sum of products using a bound on the sum of the cubic factors and
uniform bounds on the remaining factors.

The result `single_recursion_step_bound` combines two cost components with assumed recursive
subproblem bounds into a single multiple of `basicCost`.

## Main statements

* `equation5_core`: For nonnegative finite families with total `a` bounded by `L`, `b` bounded
  by `B`, and `c` bounded by `Cc`, the sum of `a³ * b² * c` is at most `L³ * B² * Cc`. This is a
  finite-sum estimate for the cost analysis of [ChauLo1995].
* `single_recursion_step_bound`: If the two components of `P N` satisfy the stated subproblem
  and local-cost bounds, and summed subproblem basic costs are at most `basicCost N`, then `P N
  ≤ (3 * C) * basicCost N`.

## References

* [Chau and Lo, 1995][ChauLo1995]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QPrimality95.MainResults

open scoped BigOperators

/-- For nonnegative finite families with total `a` bounded by `L`, `b` bounded by `B`, and `c`
bounded by `Cc`, the sum of `a³ * b² * c` is at most `L³ * B² * Cc`. This is a finite-sum
estimate for the cost analysis of [ChauLo1995]. -/
theorem equation5_core {ι : Type*} (s : Finset ι) (a b c : ι → ℝ)
    (L B Cc : ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb0 : ∀ i ∈ s, 0 ≤ b i) (hbB : ∀ i ∈ s, b i ≤ B)
    (hc0 : ∀ i ∈ s, 0 ≤ c i) (hcC : ∀ i ∈ s, c i ≤ Cc)
    (hB0 : 0 ≤ B) (hCc0 : 0 ≤ Cc)
    (hL : (∑ i ∈ s, a i) ≤ L) :
    (∑ i ∈ s, a i ^ 3 * b i ^ 2 * c i) ≤ L ^ 3 * B ^ 2 * Cc :=
  Qatlib.Foundations.CostRecurrences.FiniteWeights.weighted_cube_bound s a b c L B Cc ha hb0 hbB hc0 hcC hB0 hCc0 hL

/-- If the two components of `P N` satisfy the stated subproblem and local-cost bounds, and
summed subproblem basic costs are at most `basicCost N`, then `P N ≤ (3 * C) * basicCost N`. -/
theorem single_recursion_step_bound
    (P P1 P2 : ℕ → ℝ) (C : ℝ) (hC : 0 < C)
    (N : ℕ) (S : Finset ℕ)
    (hP : P N = P1 N + P2 N)
    (hP1 : P1 N ≤ (∑ p ∈ S, P p) + C * basicCost N)
    (hP2 : P2 N ≤ C * basicCost N)
    (hrec : ∀ p ∈ S, P p ≤ C * basicCost p)
    (hEq5 : (∑ p ∈ S, basicCost p) ≤ basicCost N) :
    P N ≤ (3 * C) * basicCost N := by
  classical
  have hsum : (∑ p ∈ S, P p) ≤ C * (∑ p ∈ S, basicCost p) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hrec
  have hmul : C * (∑ p ∈ S, basicCost p) ≤ C * basicCost N :=
    mul_le_mul_of_nonneg_left hEq5 (le_of_lt hC)
  calc
    P N = P1 N + P2 N := hP
    _ ≤ ((∑ p ∈ S, P p) + C * basicCost N) + C * basicCost N :=
      add_le_add hP1 hP2
    _ = (∑ p ∈ S, P p) + 2 * C * basicCost N := by ring
    _ ≤ C * (∑ p ∈ S, basicCost p) + 2 * C * basicCost N := by linarith
    _ ≤ C * basicCost N + 2 * C * basicCost N := by linarith
    _ = (3 * C) * basicCost N := by ring

end Qatlib.Papers.QPrimality95.MainResults
