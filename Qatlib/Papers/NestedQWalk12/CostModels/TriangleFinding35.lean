/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
noncomputable section

open scoped Real

namespace Qatlib.Papers.NestedQWalk12.CostModels.TriangleFinding35

def triangleCost35 (n r s : ℝ) : ℝ :=
  s * r ^ 2 + n * s * Real.sqrt r + n + n ^ (3 / 2 : ℝ) / (Real.sqrt s * r ^ (1 / 3 : ℝ))

theorem term_setup {n : ℝ} (hn : 0 < n) :
    n ^ (-(1 / 27) : ℝ) * (n ^ (2 / 3 : ℝ)) ^ 2 = n ^ (35 / 27 : ℝ) := by
  rw [pow_two, ← Real.rpow_add hn]
  norm_num
  rw [show (35 / 27 : ℝ) = -(1 / 27) + 4 / 3 by norm_num, Real.rpow_add hn]

theorem term_outer_update {n : ℝ} (hn : 0 < n) :
    n * n ^ (-(1 / 27) : ℝ) * Real.sqrt (n ^ (2 / 3 : ℝ)) = n ^ (35 / 27 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn.le]
  norm_num
  rw [show (35 / 27 : ℝ) = 1 + (-(1 / 27) + 1 / 3) by norm_num,
    Real.rpow_add hn, Real.rpow_one, Real.rpow_add hn]
  ring

theorem term_checking {n : ℝ} (hn : 0 < n) :
    n ^ (3 / 2 : ℝ) /
        (Real.sqrt (n ^ (-(1 / 27) : ℝ)) * (n ^ (2 / 3 : ℝ)) ^ (1 / 3 : ℝ)) =
      n ^ (35 / 27 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn.le, ← Real.rpow_mul hn.le]
  norm_num
  rw [← Real.rpow_add hn]
  norm_num
  rw [← Real.rpow_sub hn]
  norm_num

theorem theorem34_cost_eval {n : ℝ} (hn : 0 < n) :
    triangleCost35 n (n ^ (2 / 3 : ℝ)) (n ^ (-(1 / 27) : ℝ)) =
      3 * n ^ (35 / 27 : ℝ) + n := by
  unfold triangleCost35
  rw [term_setup hn, term_outer_update hn, term_checking hn]
  ring

theorem theorem34_cost_bound {n : ℝ} (hn : 1 ≤ n) :
    triangleCost35 n (n ^ (2 / 3 : ℝ)) (n ^ (-(1 / 27) : ℝ)) ≤
      4 * n ^ (35 / 27 : ℝ) := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  rw [theorem34_cost_eval hn0]
  have hnle : n ≤ n ^ (35 / 27 : ℝ) := by
    rw [show (35 / 27 : ℝ) = 1 + 8 / 27 by norm_num,
      Real.rpow_add hn0, Real.rpow_one]
    exact le_mul_of_one_le_right hn0.le
      (Real.one_le_rpow hn (by norm_num : (0 : ℝ) ≤ 8 / 27))
  nlinarith [hnle]

theorem theorem34_bigO :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℝ, 1 ≤ n →
      triangleCost35 n (n ^ (2 / 3 : ℝ)) (n ^ (-(1 / 27) : ℝ)) ≤
        c * n ^ (35 / 27 : ℝ) :=
  ⟨4, by norm_num, fun n hn => theorem34_cost_bound hn⟩

end Qatlib.Papers.NestedQWalk12.CostModels.TriangleFinding35
