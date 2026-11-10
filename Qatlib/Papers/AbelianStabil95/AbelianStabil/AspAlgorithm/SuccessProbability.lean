/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Qatlib.Papers.AbelianStabil95.AbelianStabil.AspAlgorithm.SamplingParameters

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.AspAlgorithm

open scoped BigOperators

def aspFailureBound (k n : ℕ) : ℝ :=
  (k : ℝ) * (aspSampleCount n : ℝ) * aspEpsilon k n
    + (2 : ℝ) ^ ((n : ℤ) - (aspSampleCount n : ℤ))
        * (1 + 2 * (k : ℝ) * aspEpsilon k n) ^ (aspSampleCount n)

theorem aspSampleCount_pos (n : ℕ) : 0 < aspSampleCount n := by
  unfold aspSampleCount
  omega

theorem aspSampleCount_cast_pos (n : ℕ) : (0 : ℝ) < (aspSampleCount n : ℝ) := by
  exact_mod_cast aspSampleCount_pos n

theorem asp_first_term_eq {k n : ℕ} (hk : 0 < k) :
    (k : ℝ) * (aspSampleCount n : ℝ) * aspEpsilon k n = 1 / 6 := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hlR : (0 : ℝ) < (aspSampleCount n : ℝ) := aspSampleCount_cast_pos n
  unfold aspEpsilon
  field_simp

theorem asp_twice_term_eq {k n : ℕ} (hk : 0 < k) :
    2 * (k : ℝ) * aspEpsilon k n = 1 / (3 * (aspSampleCount n : ℝ)) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hlR : (0 : ℝ) < (aspSampleCount n : ℝ) := aspSampleCount_cast_pos n
  unfold aspEpsilon
  field_simp
  norm_num

theorem asp_pow_two_eq (n : ℕ) :
    (2 : ℝ) ^ ((n : ℤ) - (aspSampleCount n : ℤ)) = 1 / 16 := by
  have hexp : (n : ℤ) - (aspSampleCount n : ℤ) = -4 := by
    unfold aspSampleCount
    push_cast
    ring
  rw [hexp, zpow_neg]
  norm_num

theorem one_add_inv_three_pow_le {l : ℕ} (hl : 0 < l) :
    (1 + 1 / (3 * (l : ℝ))) ^ l ≤ 3 / 2 := by
  have hlR : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl
  have hden : (0 : ℝ) < 3 * (l : ℝ) := by positivity

  have hbase : (1 + 1 / (3 * (l : ℝ))) ≤ Real.exp (1 / (3 * (l : ℝ))) := by
    have := Real.add_one_le_exp (1 / (3 * (l : ℝ)))
    simpa [add_comm] using this
  have hpow : (1 + 1 / (3 * (l : ℝ))) ^ l ≤ (Real.exp (1 / (3 * (l : ℝ)))) ^ l :=
    pow_le_pow_left₀ (by positivity) hbase l

  have hexp : (Real.exp (1 / (3 * (l : ℝ)))) ^ l = Real.exp (1 / 3) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  rw [hexp] at hpow

  have hexp3 : (Real.exp (1 / 3)) ^ 3 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hlt : Real.exp (1 / 3) < 3 / 2 := by
    have hcube : (Real.exp (1 / 3)) ^ 3 < (3 / 2 : ℝ) ^ 3 := by
      rw [hexp3]
      have h3 : Real.exp 1 < 3 := Real.exp_one_lt_three
      norm_num
      linarith
    exact (pow_lt_pow_iff_left₀ (by positivity) (by norm_num) (by norm_num)).mp hcube
  linarith

theorem aspFailureBound_le_third {k n : ℕ} (hk : 0 < k) :
    aspFailureBound k n ≤ 1 / 3 := by
  unfold aspFailureBound
  rw [asp_first_term_eq hk, asp_pow_two_eq n, asp_twice_term_eq hk]
  have hfac := one_add_inv_three_pow_le (aspSampleCount_pos n)
  have h16 : (0 : ℝ) <= 1 / 16 := by norm_num
  have hprod : (1 / 16 : ℝ) * (1 + 1 / (3 * (aspSampleCount n : ℝ))) ^ (aspSampleCount n)
      ≤ (1 / 16 : ℝ) * (3 / 2) := by
    exact mul_le_mul_of_nonneg_left hfac h16
  have htight : (1 / 6 : ℝ) + (1 / 16 : ℝ) * (3 / 2) = 25 / 96 := by norm_num
  have hfinal : (25 / 96 : ℝ) ≤ 1 / 3 := by norm_num
  nlinarith [hprod]

theorem asp_generation_success_ge_two_thirds {k n : ℕ} (hk : 0 < k) :
    aspFailureBound k n ≤ 1 / 3 ∧ (2 / 3 : ℝ) = 1 - 1 / 3 := by
  exact ⟨aspFailureBound_le_third hk, by norm_num⟩

end Qatlib.Papers.AbelianStabil95.AbelianStabil.AspAlgorithm
