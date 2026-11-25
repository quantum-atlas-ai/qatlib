/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LowWeightPath03.MainResults.PeriodicDijkstra
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The integer update period for periodic Dijkstra

Figure 3 of [Heiligman][Heiligman2003] balances quantum search and update
work at the real period `√n`. Rounding up to a natural period can only
decrease the update term and grows the search term by at most `√2`.
-/

set_option autoImplicit false

open Filter
open Qatlib.Papers.LowWeightPath03.MainResults.PeriodicDijkstra

namespace Qatlib.Papers.LowWeightPath03.MainResults

/-- For a positive graph size, rounding the real optimum up preserves the
work bound within a factor of `√2`. -/
theorem ceil_period_work_le (n : ℕ) (hn : 1 ≤ n) :
    quantumDijkstraWork (n : ℝ) (Nat.ceil (Real.sqrt (n : ℝ))) ≤
      Real.sqrt 2 * (n : ℝ) ^ (7 / 4 : ℝ) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  let s := Real.sqrt (n : ℝ)
  let k : ℝ := (Nat.ceil s : ℝ)
  have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr hn1
  have hs0 : 0 < s := zero_lt_one.trans_le hs1
  have hsk : s ≤ k := Nat.le_ceil s
  have hk : k ≤ 2 * s := by
    have hceil : k < s + 1 := Nat.ceil_lt_add_one hs0.le
    linarith
  change quantumDijkstraWork n k ≤ _
  unfold quantumDijkstraWork
  apply max_le
  · calc
      quantumSearchWork n k ≤ quantumSearchWork n (2 * s) :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (hs0.le.trans hsk) hk (by norm_num)) (by positivity)
      _ = Real.sqrt 2 * quantumSearchWork n s := by
        unfold quantumSearchWork
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hs0.le, Real.sqrt_eq_rpow]
        ring
      _ = _ := by rw [show s = Real.sqrt (n : ℝ) from rfl, search_at_sqrt _ hn0]
  · calc
      quantumUpdateWork n k ≤ quantumUpdateWork n s :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_nonpos hs0 hsk (by norm_num)) (by positivity)
      _ = (n : ℝ) ^ (7 / 4 : ℝ) := update_at_sqrt _ hn0
      _ ≤ _ := le_mul_of_one_le_left (by positivity) (Real.one_le_sqrt.mpr (by norm_num))

/-- The natural update period `ceil(√n)` preserves the Figure 3
`O(n^(7/4))` work model. -/
theorem quantum_dijkstra_ceil_work_isBigO :
    Asymptotics.IsBigO atTop
      (fun n : ℕ => quantumDijkstraWork (n : ℝ) (Nat.ceil (Real.sqrt (n : ℝ))))
      (fun n : ℕ => (n : ℝ) ^ (7 / 4 : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound (Real.sqrt 2) ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hp : 0 ≤ quantumDijkstraWork (n : ℝ) (Nat.ceil (Real.sqrt (n : ℝ))) := by
    apply le_trans _ (le_max_left _ _)
    unfold quantumSearchWork
    positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg hp,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)] using ceil_period_work_le n hn

end Qatlib.Papers.LowWeightPath03.MainResults
