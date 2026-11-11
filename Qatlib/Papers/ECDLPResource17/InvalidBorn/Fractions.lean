/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Invalid fraction identities

This module records exact scalar identities for the invalid fraction expressions used in the
elliptic curve resource analysis. It combines two equal exceptional contributions and expands
both the squared validity factor and its complementary failure fraction for a pair of words.

The mathematical setting follows [RoettelerEtAl2017].

## Main statements

* `overall_invalid_fraction`: simplification of the sum of two case fractions.
* `pair_validity_square` and `pair_failure_fraction`: exact paired fraction expansions.

## References

* [Roetteler et al., 2017][RoettelerEtAl2017]
-/

set_option autoImplicit false

namespace Qatlib.Papers.ECDLPResource17.InvalidBorn

open Real

/-- The sum of two copies of `n / 2^(n + 1)` equals `2 * n / 2^(n + 1)`. -/
theorem two_case_fraction_sum (n : ℕ) :
    (n : ℝ) / (2 : ℝ) ^ (n + 1) + (n : ℝ) / (2 : ℝ) ^ (n + 1) =
      (2 * (n : ℝ)) / (2 : ℝ) ^ (n + 1) := by
  ring

/-- The expression `2 * n / 2^(n + 1)` equals `n / 2^n`. -/
theorem overall_invalid_fraction (n : ℕ) :
    (2 * (n : ℝ)) / (2 : ℝ) ^ (n + 1) = (n : ℝ) / (2 : ℝ) ^ n := by
  have hpow : (2 : ℝ) ^ (n + 1) = (2 : ℝ) ^ n * 2 := by
    rw [pow_succ]
  rw [hpow]
  field_simp

/-- For `n ≥ 1`, the squared validity factor expands as `1 - n / 2^(n - 1) + n² / 2^(2 * n)`. -/
theorem pair_validity_square (n : ℕ) (hn : 1 ≤ n) :
    (1 - (n : ℝ) / (2 : ℝ) ^ n) ^ 2 =
      1 - (n : ℝ) / (2 : ℝ) ^ (n - 1) + (n : ℝ) ^ 2 / (2 : ℝ) ^ (2 * n) := by
  have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hm : (2 : ℝ) ^ (n - 1) = (2 : ℝ) ^ n / 2 := by
    rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)]
    conv_rhs => rw [← hn']
    rw [pow_succ]
  have h2n : (2 : ℝ) ^ (2 * n) = ((2 : ℝ) ^ n) ^ 2 := by
    rw [show 2 * n = n * 2 by ring, pow_mul]
  rw [hm, h2n, div_div_eq_mul_div, ← div_pow]
  ring

/-- For `n ≥ 1`, the complement of the squared validity factor equals `n / 2^(n - 1) - n² / 2^(2
* n)`. -/
theorem pair_failure_fraction (n : ℕ) (hn : 1 ≤ n) :
    1 - (1 - (n : ℝ) / (2 : ℝ) ^ n) ^ 2 =
      (n : ℝ) / (2 : ℝ) ^ (n - 1) - (n : ℝ) ^ 2 / (2 : ℝ) ^ (2 * n) := by
  have hexp := pair_validity_square n hn
  rw [hexp]
  ring

end Qatlib.Papers.ECDLPResource17.InvalidBorn
