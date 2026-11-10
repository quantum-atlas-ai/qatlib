/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.RealSqrt
import Qatlib.Concepts.SearchStopping.KnownCount.Corollary22RealRestrictedStat

namespace Qatlib.Concepts.SearchStopping.KnownCount

theorem corollary2_1Counterexample :
    ∃ (N : ℕ) (k l : ℝ), N = 2 ^ 2 ∧ k < 0 ∧ 0 < l ∧
      twoAmplitudeMass N k l = 1 ∧ |k / l| < Real.sqrt N ∧ ordinaryAfter N k l < 0 := by
  have hs : 0 < Real.sqrt 21 := Real.sqrt_pos_of_pos (by norm_num)
  have hsne : Real.sqrt 21 ≠ 0 := ne_of_gt hs
  have hsq : (Real.sqrt 21) ^ 2 = 21 := Real.sq_sqrt (by norm_num)
  refine ⟨4, -3 / Real.sqrt 21, 2 / Real.sqrt 21, by norm_num,
    div_neg_of_neg_of_pos (by norm_num) hs, div_pos (by norm_num) hs, ?_, ?_, ?_⟩
  · unfold twoAmplitudeMass
    norm_num
    field_simp
    nlinarith
  · have hratio : (-3 / Real.sqrt 21) / (2 / Real.sqrt 21) = (-3 / 2 : ℝ) := by
      field_simp
    rw [hratio]
    norm_num
  · unfold ordinaryAfter
    norm_num
    have h : 0 < 1 / Real.sqrt 21 := one_div_pos.mpr hs
    field_simp
    norm_num

end Qatlib.Concepts.SearchStopping.KnownCount
