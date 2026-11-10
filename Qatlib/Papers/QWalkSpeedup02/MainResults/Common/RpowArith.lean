/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QWalkSpeedup02.MainResults.Common.RpowArith

lemma two_rpow_add (a b : ℝ) : (2 : ℝ) ^ a * (2 : ℝ) ^ b = (2 : ℝ) ^ (a + b) :=
  (Real.rpow_add (by norm_num) a b).symm

lemma four_eq_two_rpow_two : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by
  rw [Real.rpow_two]
  norm_num

lemma sq_two_rpow_sixth (x : ℝ) : ((2 : ℝ) ^ (x / 6)) ^ 2 = (2 : ℝ) ^ (x / 3) := by
  rw [show ((2 : ℝ) ^ (x / 6)) ^ 2 = ((2 : ℝ) ^ (x / 6)) ^ (2 : ℝ) from
    (Real.rpow_natCast ((2 : ℝ) ^ (x / 6)) 2).symm]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) (x / 6) 2]
  rw [show x / 6 * 2 = x / 3 by ring]

lemma two_pow_eq_two_rpow (n : ℕ) : (2 : ℝ) ^ n = (2 : ℝ) ^ ((n : ℝ)) :=
  (Real.rpow_natCast 2 n).symm

end Qatlib.Papers.QWalkSpeedup02.MainResults.Common.RpowArith
