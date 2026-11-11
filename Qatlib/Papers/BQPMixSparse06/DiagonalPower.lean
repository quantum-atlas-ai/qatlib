/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPMixSparse06.WalkCounts.MomentSupport

/-!
# Error bounds for normalized matrix powers

The estimates `pow_lipschitz_unit` and `functional_error_budget` control powers of real numbers
in the unit interval. The rescaling identity `diagonal_power_rescale` relates normalized and
unnormalized power errors for the diagonal-entry estimation arguments of [JanzingWocjan2006].

## Main statements

* `pow_lipschitz_unit`: the power function has Lipschitz bound `m` on `[-1, 1]`.
* `functional_error_budget`: an input error at most `eps / (m + 1)` gives power error at most
  `eps`.
* `diagonal_power_rescale`: equivalence of the scaled and normalized error inequalities.

## References

* [Janzing and Wocjan, 2006][JanzingWocjan2006]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BQPMixSparse06.DiagonalPower

/-- Every natural power of a real number with absolute value at most one also has absolute value
at most one. -/
theorem pow_sup_unit {x : ℝ} (hx : |x| ≤ 1) (m : ℕ) : |x ^ m| ≤ 1 := by
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg x) hx

/-- On `[-1, 1]`, the difference of `m`th powers is at most `m` times the difference of the
inputs in absolute value [JanzingWocjan2006]. -/
theorem pow_lipschitz_unit {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (m : ℕ) :
    |x ^ m - y ^ m| ≤ (m : ℝ) * |x - y| := by
  have h := Qatlib.Papers.BQPMixSparse06.WalkCounts.pow_abs_sub_pow_le
    (x := x) (y := y) (c := 1) zero_le_one hx hy m
  simpa using h

/-- For inputs in `[-1, 1]`, an error at most `eps / (m + 1)` gives an error at most `eps`
between their `m`th powers [JanzingWocjan2006]. -/
theorem functional_error_budget {x y eps : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (heps : 0 ≤ eps) (m : ℕ) (h : |x - y| ≤ eps / (m + 1)) :
    |x ^ m - y ^ m| ≤ eps := by
  have hcast : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
  have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  calc |x ^ m - y ^ m| ≤ (m : ℝ) * |x - y| := pow_lipschitz_unit hx hy m
    _ ≤ (m : ℝ) * (eps / ((m : ℝ) + 1)) := by
        exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg m)
    _ = ((m : ℝ) / ((m : ℝ) + 1)) * eps := by ring
    _ ≤ 1 * eps := by
        have hm : (m : ℝ) / ((m : ℝ) + 1) ≤ 1 := by
          rw [div_le_one hpos]
          linarith
        exact mul_le_mul_of_nonneg_right hm heps
    _ = eps := by ring

/-- For positive `b`, dividing the power-estimation error inequality by `b ^ m` gives the
equivalent normalized inequality [JanzingWocjan2006]. -/
theorem diagonal_power_rescale {lam b g eps : ℝ} (hb : 0 < b) (m : ℕ) :
    |b ^ m * (lam / b) ^ m - g| ≤ eps * b ^ m ↔
      |(lam / b) ^ m - g / b ^ m| ≤ eps := by
  have hbpow : 0 < b ^ m := pow_pos hb m
  have hfac : b ^ m * (lam / b) ^ m - g = b ^ m * ((lam / b) ^ m - g / b ^ m) := by
    field_simp
  rw [hfac, abs_mul, abs_of_pos hbpow, mul_comm eps (b ^ m)]
  exact mul_le_mul_iff_of_pos_left hbpow

/-- If `|lam| ≤ b` and `b` is positive, every natural power of `lam / b` has absolute value at
most one [JanzingWocjan2006]. -/
theorem normalized_pow_le_one {lam b : ℝ} (hb : 0 < b) (hlam : |lam| ≤ b) (m : ℕ) :
    |(lam / b) ^ m| ≤ 1 := by
  apply pow_sup_unit
  rw [abs_div, abs_of_pos hb, div_le_one hb]
  exact hlam

end Qatlib.Papers.BQPMixSparse06.DiagonalPower
