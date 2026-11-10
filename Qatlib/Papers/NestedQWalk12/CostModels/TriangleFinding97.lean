/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
noncomputable section

open scoped Real BigOperators

namespace Qatlib.Papers.NestedQWalk12.CostModels.TriangleFinding97

def triangleCost97 (n r1 r2 : ℝ) : ℝ :=
  r1 * r2 + Real.sqrt n * r2 + n * Real.sqrt r1
    + n ^ (3 / 2 : ℝ) / (r1 ^ (1 / 6 : ℝ) * r2 ^ (1 / 6 : ℝ))

theorem term97_setup {n : ℝ} (hn : 0 < n) :
    n ^ (4 / 7 : ℝ) * n ^ (5 / 7 : ℝ) = n ^ (9 / 7 : ℝ) := by
  rw [← Real.rpow_add hn]
  norm_num

theorem term97_outer_update {n : ℝ} (hn : 0 < n) :
    Real.sqrt n * n ^ (5 / 7 : ℝ) = n ^ (17 / 14 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn]
  norm_num

theorem term97_inner_update {n : ℝ} (hn : 0 < n) :
    n * Real.sqrt (n ^ (4 / 7 : ℝ)) = n ^ (9 / 7 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn.le]
  norm_num
  rw [show (9 / 7 : ℝ) = 1 + 2 / 7 by norm_num,
    Real.rpow_add hn, Real.rpow_one]

theorem term97_checking {n : ℝ} (hn : 0 < n) :
    n ^ (3 / 2 : ℝ) /
        ((n ^ (4 / 7 : ℝ)) ^ (1 / 6 : ℝ) * (n ^ (5 / 7 : ℝ)) ^ (1 / 6 : ℝ)) =
      n ^ (9 / 7 : ℝ) := by
  rw [← Real.rpow_mul hn.le, ← Real.rpow_mul hn.le]
  norm_num
  rw [← Real.rpow_add hn]
  norm_num
  rw [← Real.rpow_sub hn]
  norm_num

theorem theorem35_cost_eval {n : ℝ} (hn : 0 < n) :
    triangleCost97 n (n ^ (4 / 7 : ℝ)) (n ^ (5 / 7 : ℝ)) =
      3 * n ^ (9 / 7 : ℝ) + n ^ (17 / 14 : ℝ) := by
  unfold triangleCost97
  rw [term97_setup hn, term97_outer_update hn, term97_inner_update hn,
    term97_checking hn]
  ring

theorem theorem35_cost_bound {n : ℝ} (hn : 1 ≤ n) :
    triangleCost97 n (n ^ (4 / 7 : ℝ)) (n ^ (5 / 7 : ℝ)) ≤
      4 * n ^ (9 / 7 : ℝ) := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  rw [theorem35_cost_eval hn0]
  have hle : n ^ (17 / 14 : ℝ) ≤ n ^ (9 / 7 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn (by norm_num)

  nlinarith [hle]

theorem theorem35_bigO :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℝ, 1 ≤ n →
      triangleCost97 n (n ^ (4 / 7 : ℝ)) (n ^ (5 / 7 : ℝ)) ≤
        c * n ^ (9 / 7 : ℝ) :=
  ⟨4, by norm_num, fun n hn => theorem35_cost_bound hn⟩

end Qatlib.Papers.NestedQWalk12.CostModels.TriangleFinding97
