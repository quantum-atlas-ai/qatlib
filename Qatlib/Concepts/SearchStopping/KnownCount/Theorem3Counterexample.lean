/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Corollary22RealRestrictedStat

namespace Qatlib.Concepts.SearchStopping.KnownCount

theorem theorem3Counterexample :
    (let k : ℝ := 3 / 5
     let l : ℝ := 4 / 5
     0 < k ∧ k < 1 / Real.sqrt 2 ∧ 0 < l ∧
       twoAmplitudeMass 2 k l = 1 ∧
       distinguishedAfter 2 (-k) l - k = 1 / 5 ∧
       distinguishedAfter 2 (-k) l - k ≤ 1 / (2 * Real.sqrt 2) ∧
       ordinaryAfter 2 (-k) l = -3 / 5 ∧ ordinaryAfter 2 (-k) l < 0) ∧
    (let k : ℝ := 1 / 16
     let l : ℝ := 1 / 16
     9 ≤ (16 : ℕ) ∧ 0 < k ∧ k < 1 / Real.sqrt 2 ∧ 0 < l ∧
       twoAmplitudeMass 16 k l = 1 / 16 ∧ twoAmplitudeMass 16 k l ≠ 1 ∧
       distinguishedAfter 16 (-k) l - k = 7 / 64 ∧
       distinguishedAfter 16 (-k) l - k < 1 / (2 * Real.sqrt 16)) ∧
    (let k : ℝ := 1 / 2
     let l : ℝ := 1 / 2
     0 < k ∧ k < 1 / Real.sqrt 2 ∧ 0 < l ∧
       twoAmplitudeMass 4 k l = 1 ∧ distinguishedAfter 4 (-k) l = 1 ∧
       ordinaryAfter 4 (-k) l = 0) := by
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsq : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hk : (3 : ℝ) / 5 < 1 / Real.sqrt 2 := by
    apply (lt_div_iff₀ hs).2
    nlinarith
  have hb : (1 : ℝ) / 5 ≤ 1 / (2 * Real.sqrt 2) := by
    apply (le_div_iff₀ (show (0 : ℝ) < 2 * Real.sqrt 2 by positivity)).2
    nlinarith
  have hs16 : Real.sqrt (16 : ℝ) = 4 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  constructor
  · refine ⟨by norm_num, hk, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
    · norm_num [twoAmplitudeMass]
    · norm_num [distinguishedAfter]
    · calc
        distinguishedAfter 2 (-(3 / 5 : ℝ)) (4 / 5) - 3 / 5 = 1 / 5 := by
          norm_num [distinguishedAfter]
        _ ≤ 1 / (2 * Real.sqrt 2) := hb
    · norm_num [ordinaryAfter]
    · norm_num [ordinaryAfter]
  · constructor
    · refine ⟨by norm_num, by norm_num, ?_, by norm_num, ?_, ?_, ?_, ?_⟩
      · exact lt_trans (by norm_num : (1 : ℝ) / 16 < 3 / 5) hk
      · norm_num [twoAmplitudeMass]
      · norm_num [twoAmplitudeMass]
      · norm_num [distinguishedAfter]
      · norm_num [distinguishedAfter, hs16]
    · refine ⟨by norm_num, ?_, by norm_num, ?_, ?_, ?_⟩
      · exact lt_trans (by norm_num : (1 : ℝ) / 2 < 3 / 5) hk
      · norm_num [twoAmplitudeMass]
      · norm_num [distinguishedAfter]
      · norm_num [ordinaryAfter]

end Qatlib.Concepts.SearchStopping.KnownCount
