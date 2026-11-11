/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Qatlib.Papers.AbelianStabil95.AbelianStabil.AspAlgorithm.SamplingParameters

/-!
# Failure bound for Abelian stabilizer sampling

`aspFailureBound` combines the coordinate-estimation error and the residual generation term for
the Abelian stabilizer sampling parameters. The arithmetic lemmas evaluate these terms and bound
their sum by one third; the final statement also records the complementary value two thirds. The
development follows [Kitaev1995].

## Main statements

* `aspFailureBound_le_third`: bounds the failure expression by one third for positive `k`.
* `asp_generation_success_ge_two_thirds`: pairs the failure bound with the complementary
  arithmetic identity.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.AspAlgorithm

open scoped BigOperators

/-- The sum of the coordinate-error term and the residual generation term for Abelian stabilizer
sampling. -/
def aspFailureBound (k n : ℕ) : ℝ :=
  (k : ℝ) * (aspSampleCount n : ℝ) * aspEpsilon k n
    + (2 : ℝ) ^ ((n : ℤ) - (aspSampleCount n : ℤ))
        * (1 + 2 * (k : ℝ) * aspEpsilon k n) ^ (aspSampleCount n)

/-- The Abelian stabilizer sample count is positive for every `n`. -/
theorem aspSampleCount_pos (n : ℕ) : 0 < aspSampleCount n := by
  unfold aspSampleCount
  omega

/-- The real-valued cast of the Abelian stabilizer sample count is positive. -/
theorem aspSampleCount_cast_pos (n : ℕ) : (0 : ℝ) < (aspSampleCount n : ℝ) := by
  exact_mod_cast aspSampleCount_pos n

/-- For positive `k`, the coordinate-error term `k * aspSampleCount n * aspEpsilon k n` equals
one sixth. -/
theorem asp_first_term_eq {k n : ℕ} (hk : 0 < k) :
    (k : ℝ) * (aspSampleCount n : ℝ) * aspEpsilon k n = 1 / 6 := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hlR : (0 : ℝ) < (aspSampleCount n : ℝ) := aspSampleCount_cast_pos n
  unfold aspEpsilon
  field_simp

/-- For positive `k`, twice `k * aspEpsilon k n` equals the reciprocal of three times the sample
count. -/
theorem asp_twice_term_eq {k n : ℕ} (hk : 0 < k) :
    2 * (k : ℝ) * aspEpsilon k n = 1 / (3 * (aspSampleCount n : ℝ)) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hlR : (0 : ℝ) < (aspSampleCount n : ℝ) := aspSampleCount_cast_pos n
  unfold aspEpsilon
  field_simp
  norm_num

/-- The factor `2 ^ (n - aspSampleCount n)`, with integer exponent, equals one sixteenth. -/
theorem asp_pow_two_eq (n : ℕ) :
    (2 : ℝ) ^ ((n : ℤ) - (aspSampleCount n : ℤ)) = 1 / 16 := by
  have hexp : (n : ℤ) - (aspSampleCount n : ℤ) = -4 := by
    unfold aspSampleCount
    push_cast
    ring
  rw [hexp, zpow_neg]
  norm_num

/-- For positive `l`, the expression `(1 + 1 / (3 * l)) ^ l` is at most three halves. -/
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

/-- For positive `k`, the Abelian stabilizer failure expression is at most one third, as
required by the sampling analysis in [Kitaev, 1995, Section 4][Kitaev1995]. -/
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

/-- For positive `k`, the failure expression is at most one third, and two thirds equals the
complement of one third. -/
theorem asp_generation_success_ge_two_thirds {k n : ℕ} (hk : 0 < k) :
    aspFailureBound k n ≤ 1 / 3 ∧ (2 / 3 : ℝ) = 1 - 1 / 3 := by
  exact ⟨aspFailureBound_le_third hk, by norm_num⟩

end Qatlib.Papers.AbelianStabil95.AbelianStabil.AspAlgorithm
