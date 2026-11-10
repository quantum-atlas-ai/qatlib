/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommuteTest05.MainResults

theorem crossover_small (n : ℝ) (hn : 0 < n) :
    n ^ (2 / 3 : ℝ) * n ^ (5 / 3 : ℝ) =
      (n ^ (2 / 3 : ℝ)) ^ (4 / 5 : ℝ) * n ^ (9 / 5 : ℝ) := by
  rw [← Real.rpow_add hn (2 / 3) (5 / 3)]
  rw [← Real.rpow_mul hn.le (2 / 3) (4 / 5)]
  rw [← Real.rpow_add hn ((2 / 3) * (4 / 5)) (9 / 5)]
  norm_num

theorem crossover_mid (n : ℝ) (hn : 0 < n) :
    n * n ^ (5 / 3 : ℝ) = n ^ (2 / 3 : ℝ) * n ^ 2 := by
  nth_rewrite 1 [← Real.rpow_one n]
  rw [← Real.rpow_add hn 1 (5 / 3)]
  rw [← Real.rpow_natCast n 2]
  rw [← Real.rpow_add hn (2 / 3) ((2 : ℕ) : ℝ)]
  norm_num

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
