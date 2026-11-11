/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Runtime lower bound from distance estimates

Establishes the scalar inequalities used to deduce the runtime bound in Theorem 1 of
[FarhiGoldstoneGutmannNagaj2008]. The theorem `theorem1_time_lower_bound` assumes the endpoint
distance estimate and its integrated derivative bound, then eliminates the intermediate quantity
`S0`.

## Main statements

* `two_mul_one_sub_sqrt_one_sub_le`: Bounds `b` by an expression involving `sqrt (1 - b)`.
* `theorem1_time_lower_bound`: Derives the explicit lower bound on `T` from the supplied
  distance estimates.

## References

* [Farhi et al., 2008][FarhiGoldstoneGutmannNagaj2008]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AdiabaticFail05.MainResults

/-- For `b ≤ 1`, the quantity `2 * (1 - Real.sqrt (1 - b))` is at least `b`. See
[FarhiGoldstoneGutmannNagaj2008]. -/
theorem two_mul_one_sub_sqrt_one_sub_le (b : ℝ) (hb1 : b ≤ 1) :
    b ≤ 2 * (1 - Real.sqrt (1 - b)) := by
  have h1b : 0 ≤ 1 - b := by linarith
  have hs2 : Real.sqrt (1 - b) ^ 2 = 1 - b := Real.sq_sqrt h1b
  have hsnn : 0 ≤ Real.sqrt (1 - b) := Real.sqrt_nonneg _
  nlinarith [sq_nonneg (1 - Real.sqrt (1 - b)), hs2]

/-- Combines the assumed lower and upper bounds on `S0` to prove `b / E * Real.sqrt (N / k) - 2
* Real.sqrt b / E ≤ T`, the scalar runtime estimate of Theorem 1 in
[FarhiGoldstoneGutmannNagaj2008]. -/
theorem theorem1_time_lower_bound
    (N k E T b S0 : ℝ) (hN : 0 < N) (hk : 0 < k) (hE : 0 < E)
    (hb0 : 0 < b) (hb1 : b ≤ 1) (_hT : 0 ≤ T)
    (heq10 : 2 * N * (1 - Real.sqrt (1 - b)) - 2 * Real.sqrt b * Real.sqrt (N * k) ≤ S0)
    (hderiv : S0 ≤ E * T * Real.sqrt (N * k)) :
    b / E * Real.sqrt (N / k) - 2 * Real.sqrt b / E ≤ T := by

  have hble : b ≤ 2 * (1 - Real.sqrt (1 - b)) :=
    two_mul_one_sub_sqrt_one_sub_le b hb1

  have hbN : b * N ≤ 2 * N * (1 - Real.sqrt (1 - b)) := by
    have := mul_le_mul_of_nonneg_right hble (le_of_lt hN)
    nlinarith [this]

  have hkey : b * N - 2 * Real.sqrt b * Real.sqrt (N * k) ≤ E * T * Real.sqrt (N * k) := by
    nlinarith [heq10, hderiv, hbN]

  have hNk_nn : 0 ≤ N * k := le_of_lt (mul_pos hN hk)
  have hNk_div : N * k * (N / k) = N ^ 2 := by
    field_simp [ne_of_gt hk]
  have hsqr : Real.sqrt (N * k) * Real.sqrt (N / k) = N := by
    have h := Real.sqrt_mul hNk_nn (N / k)
    rw [hNk_div, Real.sqrt_sq (le_of_lt hN)] at h
    exact h.symm

  have hNk_pos : Real.sqrt (N * k) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (mul_pos hN hk))
  have hE_ne : E ≠ 0 := ne_of_gt hE
  have hRHS : b / E * Real.sqrt (N / k) - 2 * Real.sqrt b / E
      = (b * N - 2 * Real.sqrt b * Real.sqrt (N * k)) / (E * Real.sqrt (N * k)) := by
    field_simp
    nlinarith [hsqr]
  rw [hRHS]
  rw [div_le_iff₀ (mul_pos hE (Real.sqrt_pos.2 (mul_pos hN hk)))]
  nlinarith [hkey, hb0]

end Qatlib.Papers.AdiabaticFail05.MainResults
