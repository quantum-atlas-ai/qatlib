/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Exponential cost identities for quantum cryptanalysis

`pow2` records real powers of two used in cryptanalytic cost expressions. Its algebraic and
square-root identities support Grover exponents, while `subset_cost_eq` rewrites the
subset-search cost scale. The mathematical context is [KaplanEtAl2015].

## Main statements

* `sqrt_pow2`: The square root of `pow2 x` is `pow2 (x/2)`.
* `subset_cost_eq`: For positive `n` and `k`, the two-thirds power of `n/√k` equals `n^(2/3) *
  k^(-1/3)`.

## References

* [Kaplan et al., 2015][KaplanEtAl2015]
-/

set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace Qatlib.Papers.QCryptanal15.MainResults.Complexity

/-- The real exponential `2^x` used in the cryptanalytic cost formulas. -/
noncomputable def pow2 (x : ℝ) : ℝ := (2 : ℝ) ^ x

/-- Every value of `pow2` is strictly positive. -/
theorem pow2_pos (x : ℝ) : 0 < pow2 x := by
  unfold pow2
  exact Real.rpow_pos_of_pos (by norm_num) x

/-- Every value of `pow2` is nonnegative. -/
theorem pow2_nonneg (x : ℝ) : 0 ≤ pow2 x := (pow2_pos x).le

/-- No value of `pow2` is zero. -/
theorem pow2_ne_zero (x : ℝ) : pow2 x ≠ 0 := (pow2_pos x).ne'

/-- The function `pow2` is monotone. -/
theorem pow2_le_pow2 {x y : ℝ} (h : x ≤ y) : pow2 x ≤ pow2 y := by
  unfold pow2
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h

/-- The power of two at a sum is the product of the corresponding powers. -/
theorem pow2_add (x y : ℝ) : pow2 (x + y) = pow2 x * pow2 y := by
  unfold pow2
  exact Real.rpow_add (by norm_num) x y

/-- Negating the exponent of `pow2` takes the multiplicative inverse. -/
theorem pow2_neg (x : ℝ) : pow2 (-x) = (pow2 x)⁻¹ := by
  unfold pow2
  exact Real.rpow_neg (by norm_num) x

/-- Subtracting exponents of `pow2` gives the quotient of the corresponding powers. -/
theorem pow2_sub (x y : ℝ) : pow2 (x - y) = pow2 x / pow2 y := by
  rw [sub_eq_add_neg, pow2_add, pow2_neg, div_eq_mul_inv]

/-- The value `pow2 (x*y)` equals the real power `(pow2 x)^y`. -/
theorem pow2_mul (x y : ℝ) : pow2 (x * y) = (pow2 x) ^ y := by
  unfold pow2
  exact Real.rpow_mul (by norm_num) x y

/-- The value of `pow2` at zero is one. -/
@[simp] theorem pow2_zero : pow2 0 = 1 := by
  unfold pow2
  simp

/-- The value of `pow2` at one is two. -/
theorem pow2_one : pow2 1 = 2 := by
  unfold pow2
  norm_num

/-- Squaring `pow2 (x/2)` gives `pow2 x`. -/
theorem pow2_half_sq (x : ℝ) : pow2 (x / 2) ^ 2 = pow2 x := by
  have h : pow2 x = (pow2 (x / 2)) ^ (2 : ℝ) := by
    rw [← pow2_mul]
    ring_nf
  rw [h, Real.rpow_two]

/-- The square root of `pow2 x` is `pow2 (x/2)`. -/
theorem sqrt_pow2 (x : ℝ) : Real.sqrt (pow2 x) = pow2 (x / 2) := by
  rw [Real.sqrt_eq_rpow]
  have h : (pow2 x) ^ (1 / 2 : ℝ) = pow2 (x * (1 / 2)) := by
    rw [← pow2_mul]
  rw [h]
  ring_nf

/-- The reciprocal square root of `pow2 (-h)` is `pow2 (h/2)`. -/
theorem inv_sqrt_pow2_neg (h : ℝ) : (Real.sqrt (pow2 (-h)))⁻¹ = pow2 (h / 2) := by
  rw [sqrt_pow2]
  have h' : -h / 2 = -(h / 2) := by ring
  rw [h', pow2_neg, inv_inv]

/-- For positive `n` and `k`, the two-thirds power of `n/√k` equals `n^(2/3) * k^(-1/3)`. -/
theorem subset_cost_eq (n k : ℝ) (hn : 0 < n) (hk : 0 < k) :
    (n / Real.sqrt k) ^ (2 / 3 : ℝ) = n ^ (2 / 3 : ℝ) * k ^ (-(1 / 3) : ℝ) := by
  have hk' : Real.sqrt k = k ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow k
  have hkpos : 0 < k ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hk _
  rw [hk', Real.div_rpow (le_of_lt hn) hkpos.le (2 / 3 : ℝ)]
  have hk13 : (k ^ (1 / 2 : ℝ)) ^ (2 / 3 : ℝ) = k ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_mul (le_of_lt hk)]
    congr 1
    norm_num
  rw [hk13, div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hk) (1 / 3)]

end Qatlib.Papers.QCryptanal15.MainResults.Complexity
