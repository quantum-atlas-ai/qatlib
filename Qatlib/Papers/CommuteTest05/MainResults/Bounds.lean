/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Crossover identities for query-cost scales

This module verifies exact power identities at the crossover parameter values for the query-cost
expressions compared in [Itakura2005]. The identities concern positive real `n` and use real
powers.

## Main statements

* `crossover_small`: Equality of the direct and two-level scales at `k = n ^ (2 / 3)`.
* `crossover_mid`: Equality of the direct and collision scales at `k = n`.
* `crossover_large`: Equality of the collision and two-level scales at `k = n ^ (3 / 2)`.

## References

* [Itakura, 2005][Itakura2005]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommuteTest05.MainResults

/-- For positive `n`, the direct and two-level power expressions agree at `k = n ^ (2 / 3)`,
giving a crossover identity for the cost comparison in [Itakura2005]. -/
theorem crossover_small (n : ℝ) (hn : 0 < n) :
    n ^ (2 / 3 : ℝ) * n ^ (5 / 3 : ℝ) =
      (n ^ (2 / 3 : ℝ)) ^ (4 / 5 : ℝ) * n ^ (9 / 5 : ℝ) := by
  rw [← Real.rpow_add hn (2 / 3) (5 / 3)]
  rw [← Real.rpow_mul hn.le (2 / 3) (4 / 5)]
  rw [← Real.rpow_add hn ((2 / 3) * (4 / 5)) (9 / 5)]
  norm_num

/-- For positive `n`, `n * n ^ (5 / 3) = n ^ (2 / 3) * n ^ 2`, giving the
direct-versus-collision crossover at `k = n` in [Itakura2005]. -/
theorem crossover_mid (n : ℝ) (hn : 0 < n) :
    n * n ^ (5 / 3 : ℝ) = n ^ (2 / 3 : ℝ) * n ^ 2 := by
  nth_rewrite 1 [← Real.rpow_one n]
  rw [← Real.rpow_add hn 1 (5 / 3)]
  rw [← Real.rpow_natCast n 2]
  rw [← Real.rpow_add hn (2 / 3) ((2 : ℕ) : ℝ)]
  norm_num

/-- For positive `n`, the collision and two-level power expressions agree at `k = n ^ (3 / 2)`,
giving a crossover identity for [Itakura2005]. -/
theorem crossover_large (n : ℝ) (hn : 0 < n) :
    (n ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) * n ^ 2 =
      (n ^ (3 / 2 : ℝ)) ^ (4 / 5 : ℝ) * n ^ (9 / 5 : ℝ) := by
  conv_lhs =>
    rw [← Real.rpow_mul hn.le (3 / 2) (2 / 3), ← Real.rpow_natCast n 2,
      ← Real.rpow_add hn ((3 / 2) * (2 / 3)) ((2 : ℕ) : ℝ)]
  conv_rhs =>
    rw [← Real.rpow_mul hn.le (3 / 2) (4 / 5),
      ← Real.rpow_add hn ((3 / 2) * (4 / 5)) (9 / 5)]
  norm_num

end Qatlib.Papers.CommuteTest05.MainResults
