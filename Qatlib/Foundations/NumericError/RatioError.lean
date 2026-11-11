/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic

/-!
# Error budgets for complex quotients

Proves `quotient_error_of_third_budgets`, a stability bound for approximating a complex
numerator divided by a real normalization factor. When `0 ≤ θ ≤ 1` and `‖a‖ ≤ Z`, allocating `(θ
/ 3) * Z` to each of the numerator and denominator errors bounds the quotient error by `θ`; the
statement also covers `Z = 0` with Lean's division convention. See [Watrous2018] for related
background.

## Main statements

* `quotient_error_of_third_budgets`: If `0 ≤ θ ≤ 1`, `‖a‖ ≤ Z`, and the numerator and
  denominator approximations each have error at most `(θ / 3) * Z`, then `‖a_tilde / Z_tilde - a
  / (Z : ℂ)‖ ≤ θ`.

## References

* [Watrous, 2018][Watrous2018]
-/

namespace Qatlib.Foundations.NumericError.RatioError

/-- If `0 ≤ θ ≤ 1`, `‖a‖ ≤ Z`, and the numerator and denominator approximations each have error
at most `(θ / 3) * Z`, then `‖a_tilde / Z_tilde - a / (Z : ℂ)‖ ≤ θ`. -/
theorem quotient_error_of_third_budgets :
    ∀ (θ : ℝ) (a a_tilde : ℂ) (Z : ℝ) (Z_tilde : ℂ),
    0 ≤ θ →
    θ ≤ 1 →
    ‖a‖ ≤ Z →
    ‖a - a_tilde‖ ≤ (θ / 3) * Z →
    ‖(Z : ℂ) - Z_tilde‖ ≤ (θ / 3) * Z →
    ‖a_tilde / Z_tilde - a / (Z : ℂ)‖ ≤ θ := by
  intro θ a a_tilde Z Z_tilde hθ0 hθ1 ha haa hZZ
  have hZ0 : 0 ≤ Z := le_trans (norm_nonneg a) ha
  by_cases hZ : Z = 0
  · subst hZ
    have ha0 : a = 0 := norm_le_zero_iff.mp ha
    have hat0 : a_tilde = 0 := by
      have h : ‖a - a_tilde‖ ≤ 0 := by simpa using haa
      have h' := sub_eq_zero.mp (norm_le_zero_iff.mp h)
      rw [ha0] at h'
      exact h'.symm
    have hZt0 : Z_tilde = 0 := by
      have h : ‖((0 : ℝ) : ℂ) - Z_tilde‖ ≤ 0 := by simpa using hZZ
      have h' := norm_le_zero_iff.mp h
      simpa using h'
    subst ha0
    subst hat0
    subst hZt0
    simp [hθ0]
  · have hZpos : 0 < Z := lt_of_le_of_ne hZ0 (Ne.symm hZ)
    have hnormZ : ‖(Z : ℂ)‖ = Z := by
      have h : ‖(Z : ℂ)‖ = |Z| := RCLike.norm_ofReal Z
      rwa [abs_of_nonneg hZ0] at h
    have hZt_lb : (2 / 3 : ℝ) * Z ≤ ‖Z_tilde‖ := by
      have h1 : Z - ‖Z_tilde‖ ≤ ‖(Z : ℂ) - Z_tilde‖ := by
        have h := norm_sub_norm_le (Z : ℂ) Z_tilde
        rwa [hnormZ] at h
      have h2 : (0 : ℝ) ≤ (1 - θ) * Z := mul_nonneg (sub_nonneg.mpr hθ1) hZ0
      linarith
    have hZt_pos : 0 < ‖Z_tilde‖ := lt_of_lt_of_le (by linarith) hZt_lb
    have hZt_ne : Z_tilde ≠ 0 := norm_pos_iff.mp hZt_pos
    have hZc_ne : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hZpos)
    have haa' : ‖a_tilde - a‖ ≤ (θ / 3) * Z := by
      rw [← norm_sub_rev]
      exact haa

    have hid : a_tilde / Z_tilde - a / (Z : ℂ)
        = ((a_tilde - a) * (Z : ℂ) + a * ((Z : ℂ) - Z_tilde)) / ((Z : ℂ) * Z_tilde) := by
      rw [div_sub_div _ _ hZt_ne hZc_ne]
      congr 1
      · ring
      · exact mul_comm _ _
    rw [hid, norm_div, norm_mul ((Z : ℂ)) Z_tilde, hnormZ,
      div_le_iff₀ (mul_pos hZpos hZt_pos)]
    have hnum : ‖(a_tilde - a) * (Z : ℂ) + a * ((Z : ℂ) - Z_tilde)‖
        ≤ ‖a_tilde - a‖ * Z + ‖a‖ * ‖(Z : ℂ) - Z_tilde‖ := by
      calc ‖(a_tilde - a) * (Z : ℂ) + a * ((Z : ℂ) - Z_tilde)‖
          ≤ ‖(a_tilde - a) * (Z : ℂ)‖ + ‖a * ((Z : ℂ) - Z_tilde)‖ := norm_add_le _ _
        _ = ‖a_tilde - a‖ * Z + ‖a‖ * ‖(Z : ℂ) - Z_tilde‖ := by
            rw [norm_mul, norm_mul, hnormZ]
    have hsum : ‖a_tilde - a‖ * Z + ‖a‖ * ‖(Z : ℂ) - Z_tilde‖
        ≤ (θ / 3) * Z * Z + Z * ((θ / 3) * Z) :=
      add_le_add (mul_le_mul_of_nonneg_right haa' hZ0)
        (mul_le_mul ha hZZ (norm_nonneg _) hZ0)
    have h4 : θ * (Z * ((2 / 3 : ℝ) * Z)) ≤ θ * (Z * ‖Z_tilde‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hZt_lb hZ0) hθ0

    have key : ‖a_tilde - a‖ * Z + ‖a‖ * ‖(Z : ℂ) - Z_tilde‖
        ≤ θ * (Z * ‖Z_tilde‖) := by
      nlinarith [hsum, h4]
    exact le_trans hnum key

end Qatlib.Foundations.NumericError.RatioError
