/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Error bounds for centered finite differences

This module expands low-order Taylor polynomials and bounds the error of a centered difference
with perturbed endpoint values. It separates third-derivative truncation error from value
precision, supporting the classical comparison in [Jordan2005Gradient].

## Main statements

* `centered_truncation`: a global third-derivative bound gives error at most `D3*l^2/24`.
* `centered_total_error`: endpoint error at most `E` adds at most `2*E/l`.

## References

* [Jordan, 2005][Jordan2005Gradient]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Set

namespace Qatlib.Concepts.GradientOracle.StepSizes

/-- The first-order Taylor evaluation within a set equals the function value plus the first
within-derivative times the displacement. -/
lemma taylor_one_eval (f : ℝ → ℝ) (s : Set ℝ) (x y : ℝ) :
    taylorWithinEval f 1 s x y = f x + iteratedDerivWithin 1 f s x * (y - x) := by
  rw [taylorWithinEval_succ, taylor_within_zero_eval]
  simp
  ring

/-- The second-order Taylor evaluation within a set equals the value, linear term, and one-half
the second within-derivative times the squared displacement. -/
lemma taylor_two_eval (f : ℝ → ℝ) (s : Set ℝ) (x y : ℝ) :
    taylorWithinEval f 2 s x y
      = f x + iteratedDerivWithin 1 f s x * (y - x)
        + (1 / 2) * iteratedDerivWithin 2 f s x * (y - x) ^ 2 := by
  rw [taylorWithinEval_succ, taylor_one_eval]
  simp only [Nat.factorial_one, Nat.cast_one, mul_one, smul_eq_mul]
  norm_num
  ring

/-- For distinct interval endpoints and a function `n` times continuously differentiable at `x`,
its `n`th derivative within the unoriented closed interval at `x` equals the unrestricted
derivative. -/
lemma within_deriv_eq (f : ℝ → ℝ) (n : ℕ) (x y : ℝ) (hxy : x ≠ y)
    (hf : ContDiffAt ℝ n f x) :
    iteratedDerivWithin n f (uIcc x y) x = iteratedDeriv n f x := by
  apply iteratedDerivWithin_eq_iteratedDeriv
  · rw [uIcc]
    apply uniqueDiffOn_Icc
    rcases lt_or_gt_of_ne hxy with h | h
    · rwa [inf_eq_left.mpr h.le, sup_eq_right.mpr h.le]
    · rwa [inf_eq_right.mpr h.le, sup_eq_left.mpr h.le]
  · exact hf
  · exact left_mem_uIcc

/-- For a globally `C³` function with third derivative bounded by `D3`, the centered difference
at separation `l > 0` has derivative error at most `D3*l^2/24`. See [Jordan2005Gradient]. -/
theorem centered_truncation (f : ℝ → ℝ) (x l D3 : ℝ) (hl : 0 < l)
    (hC : ContDiff ℝ 3 f) (hD3 : ∀ t, |iteratedDeriv 3 f t| ≤ D3) :
    |(f (x + l / 2) - f (x - l / 2)) / l - iteratedDeriv 1 f x| ≤ D3 * l ^ 2 / 24 := by
  have hxp : x ≠ x + l / 2 := by intro he; linarith
  have hxm : x ≠ x - l / 2 := by intro he; linarith
  obtain ⟨ξ1, _, h1⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (f := f) (x := x + l / 2) (x₀ := x)
      (n := 2) hxp hC.contDiffOn
  obtain ⟨ξ2, _, h2⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (f := f) (x := x - l / 2) (x₀ := x)
      (n := 2) hxm hC.contDiffOn
  rw [taylor_two_eval] at h1 h2
  rw [within_deriv_eq f 1 x (x + l / 2) hxp ((hC.of_le (by decide)).contDiffAt),
      within_deriv_eq f 2 x (x + l / 2) hxp ((hC.of_le (by decide)).contDiffAt)] at h1
  rw [within_deriv_eq f 1 x (x - l / 2) hxm ((hC.of_le (by decide)).contDiffAt),
      within_deriv_eq f 2 x (x - l / 2) hxm ((hC.of_le (by decide)).contDiffAt)] at h2
  have hp : x + l / 2 - x = l / 2 := by ring
  have hm : x - l / 2 - x = -(l / 2) := by ring
  rw [hp] at h1
  rw [hm] at h2
  norm_num at h1 h2
  have hdiff : f (x + l / 2) - f (x - l / 2) - l * iteratedDeriv 1 f x
      = (iteratedDeriv 3 f ξ1 + iteratedDeriv 3 f ξ2) * (l / 2) ^ 3 / 6 := by
    rw [iteratedDeriv_one]
    linear_combination h1 - h2
  have hbound :
      |(iteratedDeriv 3 f ξ1 + iteratedDeriv 3 f ξ2) * (l / 2) ^ 3 / 6|
        ≤ D3 * l ^ 3 / 24 := by
    have hp3 : (0 : ℝ) ≤ (l / 2) ^ 3 := by positivity
    have htri : |iteratedDeriv 3 f ξ1 + iteratedDeriv 3 f ξ2|
        ≤ |iteratedDeriv 3 f ξ1| + |iteratedDeriv 3 f ξ2| := abs_add_le _ _
    have h1 := hD3 ξ1
    have h2 := hD3 ξ2
    have hnonneg : (0 : ℝ) ≤ (l / 2) ^ 3 / 6 := by positivity
    have hstep : |iteratedDeriv 3 f ξ1 + iteratedDeriv 3 f ξ2| * ((l / 2) ^ 3 / 6)
        ≤ (D3 + D3) * ((l / 2) ^ 3 / 6) := by
      have ht1 := mul_le_mul_of_nonneg_right htri hnonneg
      have ht2 :=
          mul_le_mul_of_nonneg_right
          (by linarith : |iteratedDeriv 3 f ξ1| + |iteratedDeriv 3 f ξ2| ≤ D3 + D3) hnonneg
      exact le_trans ht1 ht2
    calc |(iteratedDeriv 3 f ξ1 + iteratedDeriv 3 f ξ2) * (l / 2) ^ 3 / 6|
        = |iteratedDeriv 3 f ξ1 + iteratedDeriv 3 f ξ2| * ((l / 2) ^ 3 / 6) := by
          rw [abs_div, abs_mul, abs_of_nonneg hp3,
            abs_of_pos (by norm_num : (0 : ℝ) < 6)]
          ring
      _ ≤ (D3 + D3) * ((l / 2) ^ 3 / 6) := hstep
      _ = D3 * l ^ 3 / 24 := by ring
  have hdiv : (f (x + l / 2) - f (x - l / 2)) / l - iteratedDeriv 1 f x
      = (f (x + l / 2) - f (x - l / 2) - l * iteratedDeriv 1 f x) / l := by
    field_simp
  rw [hdiv, hdiff]
  calc |((iteratedDeriv 3 f ξ1 + iteratedDeriv 3 f ξ2) * (l / 2) ^ 3 / 6) / l|
      = |(iteratedDeriv 3 f ξ1 + iteratedDeriv 3 f ξ2) * (l / 2) ^ 3 / 6| / l := by
        rw [abs_div, abs_of_pos hl]
    _ ≤ (D3 * l ^ 3 / 24) / l := by
        rw [div_le_div_iff₀ hl hl]
        exact mul_le_mul_of_nonneg_right hbound hl.le
    _ = D3 * l ^ 2 / 24 := by
        field_simp

/-- If both endpoint values are approximated within `E` and `l > 0`, the resulting
centered-difference value changes by at most `2*E/l`. See [Jordan2005Gradient]. -/
theorem centered_value_error (f : ℝ → ℝ) (x l E gp gm : ℝ) (hl : 0 < l)
    (hp : |f (x + l / 2) - gp| ≤ E) (hm : |f (x - l / 2) - gm| ≤ E) :
    |(gp - gm) / l - (f (x + l / 2) - f (x - l / 2)) / l| ≤ 2 * E / l := by
  have h1 : |gp - f (x + l / 2)| ≤ E := by rw [abs_sub_comm]; exact hp
  have h2 : |gm - f (x - l / 2)| ≤ E := by rw [abs_sub_comm]; exact hm
  have hkey : (gp - gm) / l - (f (x + l / 2) - f (x - l / 2)) / l
      = ((gp - f (x + l / 2)) - (gm - f (x - l / 2))) / l := by
    field_simp
    ring
  have htri : |(gp - f (x + l / 2)) - (gm - f (x - l / 2))|
      ≤ |gp - f (x + l / 2)| + |gm - f (x - l / 2)| := by
    have h := abs_add_le (gp - f (x + l / 2)) (-(gm - f (x - l / 2)))
    have h' : |gp - f (x + l / 2) + (f (x - l / 2) - gm)|
        ≤ |gp - f (x + l / 2)| + |f (x - l / 2) - gm| := by
      simpa [abs_neg] using h
    rw [show gp - f (x + l / 2) + (f (x - l / 2) - gm)
        = (gp - f (x + l / 2)) - (gm - f (x - l / 2)) by ring,
      abs_sub_comm (f (x - l / 2)) gm] at h'
    exact h'
  have hnum : |(gp - f (x + l / 2)) - (gm - f (x - l / 2))| ≤ 2 * E := by
    calc |(gp - f (x + l / 2)) - (gm - f (x - l / 2))|
        ≤ |gp - f (x + l / 2)| + |gm - f (x - l / 2)| := htri
      _ ≤ E + E := add_le_add h1 h2
      _ = 2 * E := by ring
  rw [hkey, abs_div, abs_of_pos hl]
  rw [div_le_div_iff₀ hl hl]
  exact mul_le_mul_of_nonneg_right hnum hl.le

/-- For a globally `C³` function with third derivative bounded by `D3` and endpoint errors at
most `E`, the centered-difference derivative error is at most `D3*l^2/24 + 2*E/l`. See
[Jordan2005Gradient]. -/
theorem centered_total_error (f : ℝ → ℝ) (x l D3 E gp gm : ℝ) (hl : 0 < l)
    (hC : ContDiff ℝ 3 f) (hD3 : ∀ t, |iteratedDeriv 3 f t| ≤ D3)
    (hp : |f (x + l / 2) - gp| ≤ E) (hm : |f (x - l / 2) - gm| ≤ E) :
    |(gp - gm) / l - iteratedDeriv 1 f x| ≤ D3 * l ^ 2 / 24 + 2 * E / l := by
  have ht := centered_truncation f x l D3 hl hC hD3
  have hv := centered_value_error f x l E gp gm hl hp hm
  have hsplit : (gp - gm) / l - iteratedDeriv 1 f x
      = ((gp - gm) / l - (f (x + l / 2) - f (x - l / 2)) / l)
        + ((f (x + l / 2) - f (x - l / 2)) / l - iteratedDeriv 1 f x) := by
    ring
  rw [hsplit]
  calc |((gp - gm) / l - (f (x + l / 2) - f (x - l / 2)) / l)
        + ((f (x + l / 2) - f (x - l / 2)) / l - iteratedDeriv 1 f x)|
      ≤ |(gp - gm) / l - (f (x + l / 2) - f (x - l / 2)) / l|
        + |(f (x + l / 2) - f (x - l / 2)) / l - iteratedDeriv 1 f x| := abs_add_le _ _
    _ ≤ 2 * E / l + D3 * l ^ 2 / 24 := add_le_add hv ht
    _ = D3 * l ^ 2 / 24 + 2 * E / l := by ring

end Qatlib.Concepts.GradientOracle.StepSizes
