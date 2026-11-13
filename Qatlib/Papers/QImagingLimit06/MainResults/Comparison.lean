/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QImagingLimit06.MainResults.FisherCore

/-!
# Comparison of intensity and field resolution scales

This module compares positive resolution parameters defined by inverse squared derivative sums.
A pointwise bound for the derivative of a complex field magnitude yields `a_ge_b_of_field`, the
inequality `b ≤ a`. See [DelaubertEtAl2008] for the paper context.

## Main statements

* `a_ge_b_of_pointwise`: Pointwise domination of squared derivative terms implies `b ≤ a` when
  their sums equal the inverse squares of positive scales `a` and `b`.
* `abs_deriv_sq_le`: The squared radial derivative expression `(a*c + b*d) / sqrt(a² + b²)` is
  at most `c² + d²` when the denominator is nonzero.
* `a_ge_b_of_field`: For a field with nonzero pixel magnitudes, the positive scale defined by
  magnitude derivatives is at least the scale defined by both field derivatives.

## References

* [Delaubert et al., 2008][DelaubertEtAl2008]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QImagingLimit06.MainResults

/-- Pointwise domination of squared derivative terms implies `b ≤ a` when their sums equal the
inverse squares of positive scales `a` and `b`. -/
theorem a_ge_b_of_pointwise {ι : Type} [Fintype ι] {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) (dAbsU dU : ι → ℝ)
    (hpoint : ∀ k, (dAbsU k) ^ 2 ≤ (dU k) ^ 2)
    (ha_def : 1 / a ^ 2 = ∑ k, (dAbsU k) ^ 2)
    (hb_def : 1 / b ^ 2 = ∑ k, (dU k) ^ 2) :
    b ≤ a := by
  have hsum : ∑ k, (dAbsU k) ^ 2 ≤ ∑ k, (dU k) ^ 2 :=
    Finset.sum_le_sum fun k _ => hpoint k
  have hineq : 1 / a ^ 2 ≤ 1 / b ^ 2 := by
    rw [ha_def, hb_def]
    exact hsum
  have ha2 : (0 : ℝ) < a ^ 2 := by positivity
  have hb2 : (0 : ℝ) < b ^ 2 := by positivity
  have ha' : a ≠ 0 := ha.ne'
  have hb' : b ≠ 0 := hb.ne'
  have hsq : b ^ 2 ≤ a ^ 2 := by
    have hmul : 1 / a ^ 2 * (a ^ 2 * b ^ 2) ≤ 1 / b ^ 2 * (a ^ 2 * b ^ 2) :=
      mul_le_mul_of_nonneg_right hineq (le_of_lt (mul_pos ha2 hb2))
    have h1 : 1 / a ^ 2 * (a ^ 2 * b ^ 2) = b ^ 2 := by
      field_simp
    have h2 : 1 / b ^ 2 * (a ^ 2 * b ^ 2) = a ^ 2 := by
      field_simp
    rwa [h1, h2] at hmul
  have hroot := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq hb.le, Real.sqrt_sq ha.le] at hroot

/-- The squared radial derivative expression `(a*c + b*d) / sqrt(a² + b²)` is at most `c² + d²`
when the denominator is nonzero. See [DelaubertEtAl2008]. -/
theorem abs_deriv_sq_le {a b c d : ℝ} (hn : a ^ 2 + b ^ 2 ≠ 0) :
    ((a * c + b * d) / Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 ≤ c ^ 2 + d ^ 2 := by
  have hnonneg : (0 : ℝ) ≤ a ^ 2 + b ^ 2 := by positivity
  have hpos : 0 < a ^ 2 + b ^ 2 := lt_of_le_of_ne hnonneg (Ne.symm hn)
  have hkey : (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
    nlinarith [sq_nonneg (a * d - b * c)]
  have hsq : Real.sqrt (a ^ 2 + b ^ 2) ^ 2 = a ^ 2 + b ^ 2 :=
    Real.sq_sqrt (le_of_lt hpos)
  rw [div_pow, hsq, div_le_iff₀ hpos]
  calc (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := hkey
    _ = (c ^ 2 + d ^ 2) * (a ^ 2 + b ^ 2) := by ring

/-- For a field with nonzero pixel magnitudes, the positive scale defined by magnitude
derivatives is at least the scale defined by both field derivatives. See
[DelaubertEtAl2008]. -/
theorem a_ge_b_of_field {ι : Type} [Fintype ι] {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) (uRe uIm duRe duIm : ι → ℝ)
    (hn : ∀ k, uRe k ^ 2 + uIm k ^ 2 ≠ 0)
    (ha_def : 1 / a ^ 2 = ∑ k,
      ((uRe k * duRe k + uIm k * duIm k) / Real.sqrt (uRe k ^ 2 + uIm k ^ 2)) ^ 2)
    (hb_def : 1 / b ^ 2 = ∑ k, (duRe k ^ 2 + duIm k ^ 2)) :
    b ≤ a := by
  refine a_ge_b_of_pointwise ha hb
    (fun k => (uRe k * duRe k + uIm k * duIm k) /
      Real.sqrt (uRe k ^ 2 + uIm k ^ 2))
    (fun k => Real.sqrt (duRe k ^ 2 + duIm k ^ 2)) ?_ ha_def ?_
  · intro k
    show ((uRe k * duRe k + uIm k * duIm k) /
          Real.sqrt (uRe k ^ 2 + uIm k ^ 2)) ^ 2 ≤
        (Real.sqrt (duRe k ^ 2 + duIm k ^ 2)) ^ 2
    rw [Real.sq_sqrt (show (0 : ℝ) ≤ duRe k ^ 2 + duIm k ^ 2 by positivity)]
    exact abs_deriv_sq_le (a := uRe k) (b := uIm k) (c := duRe k)
      (d := duIm k) (hn k)
  · rw [hb_def]
    exact Finset.sum_congr rfl fun k _ => by
      show duRe k ^ 2 + duIm k ^ 2 = (Real.sqrt (duRe k ^ 2 + duIm k ^ 2)) ^ 2
      rw [Real.sq_sqrt (show (0 : ℝ) ≤ duRe k ^ 2 + duIm k ^ 2 by positivity)]

end Qatlib.Papers.QImagingLimit06.MainResults
