/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
noncomputable section

open scoped Real

namespace Qatlib.Papers.NestedQWalk12.CostModels.GraphCollision

def graphCollisionCost (r1 r2 m : ℝ) : ℝ :=
  m + Real.sqrt (r1 * r2) / Real.sqrt m

theorem graphCollision_m_le_r1 {r1 r2 : ℝ} (h1 : 0 < r1) (h12 : r1 ≤ r2)
    (h2r : r2 ≤ r1 ^ 2) :
    (r1 * r2) ^ (1 / 3 : ℝ) ≤ r1 := by
  have h2pos : 0 < r2 := lt_of_lt_of_le h1 h12
  have hP : 0 ≤ r1 * r2 := mul_nonneg h1.le h2pos.le
  have hle : r1 * r2 ≤ r1 ^ 3 := by nlinarith [h2r, h1]
  calc (r1 * r2) ^ (1 / 3 : ℝ) ≤ (r1 ^ 3) ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow hP hle (by norm_num)
    _ = r1 := by
        rw [← Real.rpow_natCast r1 3, ← Real.rpow_mul h1.le]
        rw [show ((3 : ℕ) : ℝ) * (1 / 3 : ℝ) = 1 by norm_num, Real.rpow_one]

theorem lemmaA1_cost_eq {r1 r2 : ℝ} (h1 : 0 < r1) (h2 : 0 < r2) :
    graphCollisionCost r1 r2 ((r1 * r2) ^ (1 / 3 : ℝ)) =
      2 * (r1 * r2) ^ (1 / 3 : ℝ) := by
  have hP : 0 < r1 * r2 := mul_pos h1 h2
  rw [graphCollisionCost, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hP.le]
  rw [← Real.rpow_sub hP]
  norm_num
  ring

theorem lemmaA1_cost_le {r1 r2 : ℝ} (h1 : 0 < r1) (h12 : r1 ≤ r2)
    (_h2r : r2 ≤ r1 ^ 2) :
    graphCollisionCost r1 r2 ((r1 * r2) ^ (1 / 3 : ℝ)) ≤
      2 * (r1 * r2) ^ (1 / 3 : ℝ) := by
  have h2pos : 0 < r2 := lt_of_lt_of_le h1 h12
  rw [lemmaA1_cost_eq h1 h2pos]

theorem lemmaA1_bigO :
    ∃ c : ℝ, 0 < c ∧ ∀ r1 r2 : ℝ, 0 < r1 → r1 ≤ r2 → r2 ≤ r1 ^ 2 →
      graphCollisionCost r1 r2 ((r1 * r2) ^ (1 / 3 : ℝ)) ≤
        c * (r1 * r2) ^ (1 / 3 : ℝ) :=
  ⟨2, by norm_num, fun r1 r2 h1 h12 h2r => lemmaA1_cost_le h1 h12 h2r⟩

end Qatlib.Papers.NestedQWalk12.CostModels.GraphCollision
