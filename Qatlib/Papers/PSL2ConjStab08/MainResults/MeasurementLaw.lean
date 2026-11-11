/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Measurement probabilities and repetition

The rational probability expressions arising in [DenneyMooreRussell2008] simplify to `(q − 1) /
(2q)` and its complement. A uniform lower bound on success gives arbitrarily small repeated-miss
powers and the corresponding repeated-success estimate.

## Main statements

* `prob_eq_shift_ge_quarter`: the simplified success expression is at least one quarter for `q ≥
  2`.
* `repeated_success`: the complementary geometric expression can exceed any prescribed
  confidence below one.

## References

* [Denney et al., 2008][DenneyMooreRussell2008]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PSL2ConjStab08.MainResults.MeasurementLaw

/-- For `q ≥ 2`, the ratio `(q − 1)^2 / (2 * q * (q − 1))` simplifies to `(q − 1) / (2 * q)`.
See [DenneyMooreRussell2008]. -/
theorem prob_eq_shift (q : ℕ) (hq : 2 ≤ q) :
    (((q : ℝ) - 1) ^ 2) / (2 * q * ((q : ℝ) - 1)) = ((q : ℝ) - 1) / (2 * q) := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hq1 : (q : ℝ) - 1 ≠ 0 := by linarith
  field_simp

/-- For `q ≥ 2`, `(q − 1) / (2 * q)` equals `1 / 2 − 1 / (2 * q)`. See [DenneyMooreRussell2008]. -/
theorem prob_eq_shift_eq_half_sub (q : ℕ) (hq : 2 ≤ q) :
    ((q : ℝ) - 1) / (2 * q) = 1 / 2 - 1 / (2 * q) := by
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  field_simp

/-- For `q ≥ 2`, the expression `(q − 1) / (2 * q)` is at least `1 / 4`. See
[DenneyMooreRussell2008]. -/
theorem prob_eq_shift_ge_quarter (q : ℕ) (hq : 2 ≤ q) :
    1 / 4 ≤ ((q : ℝ) - 1) / (2 * q) := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- For `q ≥ 1`, the complement of `(q − 1) / (2 * q)` equals `(q + 1) / (2 * q)`. See
[DenneyMooreRussell2008]. -/
theorem prob_neq_shift (q : ℕ) (hq : 1 ≤ q) :
    1 - ((q : ℝ) - 1) / (2 * q) = ((q : ℝ) + 1) / (2 * q) := by
  have hq0 : (q : ℝ) ≠ 0 := by
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
    positivity
  field_simp
  ring

/-- For `q ≥ 2` and positive `δ`, some power of the miss expression `(q + 1) / (2 * q)` is less
than `δ`. See [DenneyMooreRussell2008]. -/
theorem repeated_miss_tends_to_zero (q : ℕ) (hq : 2 ≤ q) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, (((q : ℝ) + 1) / (2 * q)) ^ n < δ := by
  have hqpos : (0 : ℝ) < q := by
    have : (0 : ℝ) < 2 := by norm_num
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hpos : 0 < ((q : ℝ) + 1) / (2 * q) := by positivity
  have hlt : ((q : ℝ) + 1) / (2 * q) < 1 := by
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
    rw [div_lt_one (by positivity)]
    linarith
  exact exists_pow_lt_of_lt_one hδ hlt

/-- For `q ≥ 2` and positive `δ`, some repetition count makes `1 − ((q + 1) / (2 * q))^n`
greater than `1 − δ`. See [DenneyMooreRussell2008]. -/
theorem repeated_success (q : ℕ) (hq : 2 ≤ q) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, 1 - δ < 1 - (((q : ℝ) + 1) / (2 * q)) ^ n := by
  obtain ⟨n, hn⟩ := repeated_miss_tends_to_zero q hq hδ
  exact ⟨n, by linarith⟩

end Qatlib.Papers.PSL2ConjStab08.MainResults.MeasurementLaw
