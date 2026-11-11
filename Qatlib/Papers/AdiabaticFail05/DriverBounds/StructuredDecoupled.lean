/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Success bounds for independent bit transitions

This module records the product success probability for independent bits with common failure
probability and derives its Bernoulli lower bound. The theorem `quadratic_gap_constant_success`
shows that a bound of the form `C / T ^ 2` per bit gives success at least `1 - c` once the
specified square-root runtime threshold is reached. The mathematical context is
[FarhiGoldstoneGutmannNagaj2008].

## Main statements

* `one_sub_pow_ge`: For `0 ≤ q ≤ 1`, the joint success expression `(1 - q) ^ n` is at least `1 -
  n * q`.
* `quadratic_gap_constant_success`: For positive `C`, `c`, and `T` with `c ≤ 1` and `C / T ^ 2 ≤
  1`, a runtime `T ≥ Real.sqrt (n * C / c)` gives `(1 - C / T ^ 2) ^ n ≥ 1 - c`.

## References

* [Farhi et al., 2008][FarhiGoldstoneGutmannNagaj2008]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AdiabaticFail05.DriverBounds

open Finset

/-- The product of `n` identical success factors `1 - q` equals `(1 - q) ^ n`
[FarhiGoldstoneGutmannNagaj2008]. -/
theorem decoupled_success_product (n : ℕ) (q : ℝ) :
    (∏ _i : Fin n, (1 - q)) = (1 - q) ^ n := by
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- For `0 ≤ q ≤ 1`, the joint success expression `(1 - q) ^ n` is at least `1 - n * q`
[FarhiGoldstoneGutmannNagaj2008]. -/
theorem one_sub_pow_ge (n : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    1 - (n : ℝ) * q ≤ (1 - q) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 0 ≤ 1 - q := by linarith
    have hstep : (1 - (n : ℝ) * q) * (1 - q) ≤ (1 - q) ^ (n + 1) := by
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_right ih h1
    have hexp : 1 - ((n : ℝ) + 1) * q ≤ (1 - (n : ℝ) * q) * (1 - q) := by
      nlinarith [mul_nonneg (Nat.cast_nonneg n) (sq_nonneg q)]
    calc 1 - ((n + 1 : ℕ) : ℝ) * q
        = 1 - (((n : ℝ) + 1) * q) := by push_cast; ring_nf
      _ ≤ (1 - (n : ℝ) * q) * (1 - q) := hexp
      _ ≤ (1 - q) ^ (n + 1) := hstep

/-- If `0 ≤ q ≤ 1`, `n * q ≤ c`, and `c ≤ 1`, then `(1 - q) ^ n ≥ 1 - c`
[FarhiGoldstoneGutmannNagaj2008]. -/
theorem constant_success (n : ℕ) (q c : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hc_nq : (n : ℝ) * q ≤ c) (hc1 : c ≤ 1) :
    1 - c ≤ (1 - q) ^ n := by
  have hb := one_sub_pow_ge n q hq0 hq1
  linarith

/-- For positive `C`, `c`, and `T` with `c ≤ 1` and `C / T ^ 2 ≤ 1`, a runtime `T ≥ Real.sqrt (n
* C / c)` gives `(1 - C / T ^ 2) ^ n ≥ 1 - c` [FarhiGoldstoneGutmannNagaj2008]. -/
theorem quadratic_gap_constant_success
    (n : ℕ) (C c T : ℝ)
    (hC : 0 < C) (hc : 0 < c) (hc1 : c ≤ 1) (hT : 0 < T)
    (hq1 : C / T ^ 2 ≤ 1)
    (hTbig : Real.sqrt ((n : ℝ) * C / c) ≤ T) :
    1 - c ≤ (1 - C / T ^ 2) ^ n := by

  have hq0 : 0 ≤ C / T ^ 2 := by positivity

  have hTsq : (n : ℝ) * C / c ≤ T ^ 2 := by
    have h := hTbig
    have hnn : 0 ≤ (n : ℝ) * C / c := by positivity
    have := (Real.sqrt_le_iff).mp h
    exact this.2

  have hnc : (n : ℝ) * C ≤ c * T ^ 2 := by
    have := (div_le_iff₀ hc).mp hTsq
    linarith [this]

  have hnq : (n : ℝ) * (C / T ^ 2) ≤ c := by
    have hT2 : (0 : ℝ) < T ^ 2 := by positivity
    have h1 : (n : ℝ) * (C / T ^ 2) = ((n : ℝ) * C) / T ^ 2 := by ring
    rw [h1]
    exact (div_le_iff₀ hT2).mpr hnc
  exact constant_success n (C / T ^ 2) c hq0 hq1 hnq hc1

end Qatlib.Papers.AdiabaticFail05.DriverBounds
