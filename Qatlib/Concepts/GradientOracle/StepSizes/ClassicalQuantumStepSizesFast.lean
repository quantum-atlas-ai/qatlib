/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.StepSizes.ClassicalQuantumStepSizesStat
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Classical and quantum step-size identities

This module proves the centered finite-difference error estimate using a third-derivative bound
on the evaluation interval. It combines this estimate with endpoint perturbation and step-size
identities for the comparison associated with [Jordan2005Gradient].

## Main statements

* `central_difference_error`: centered truncation error is at most `D*l^2/24`.
* `classicalQuantumStepSizes`: endpoint error, truncation, and error-matching step-size
  identities.

## References

* [Jordan, 2005][Jordan2005Gradient]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace Qatlib.Concepts.GradientOracle.StepSizes
open Set

/-- For a `C³` function and distinct real endpoints, the error after the quadratic Taylor
polynomial equals the third derivative at some intermediate point times the cubed
displacement divided by six. -/
private theorem quadratic_remainder (f : ℝ → ℝ) (x y : ℝ) (hxy : x ≠ y)
    (hf : ContDiff ℝ 3 f) :
    ∃ z ∈ uIoo x y, f y - (f x + deriv f x * (y-x) +
      iteratedDeriv 2 f x * (y-x)^2 / 2) = iteratedDeriv 3 f z * (y-x)^3 / 6 := by
  obtain ⟨z, hz, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) hxy hf.contDiffOn
  have hu : UniqueDiffOn ℝ (uIcc x y) := uniqueDiffOn_Icc (by grind)
  have hp : taylorWithinEval f 2 (uIcc x y) x y =
      f x + deriv f x * (y-x) + iteratedDeriv 2 f x * (y-x)^2 / 2 := by
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hf.contDiffAt.of_le (by norm_num)) left_mem_uIcc,
      iteratedDerivWithin_eq_iteratedDeriv hu (hf.contDiffAt.of_le (by norm_num)) left_mem_uIcc,
      iteratedDerivWithin_eq_iteratedDeriv hu (hf.contDiffAt.of_le (by norm_num)) left_mem_uIcc]
    simp [iteratedDeriv_zero, iteratedDeriv_one, Nat.factorial, smul_eq_mul]
    ring
  refine ⟨z, hz, ?_⟩
  rw [hp] at he
  norm_num only [Nat.factorial] at he
  exact he

/-- For a `C³` function whose third derivative is bounded by `D` on the evaluation interval, the
centered-difference error at positive separation `l` is at most `D*l^2/24`. -/
theorem central_difference_error (f : ℝ → ℝ) (x l D : ℝ) (hl : 0 < l)
    (hf : ContDiff ℝ 3 f)
    (hD : ∀ ξ ∈ Icc (x-l/2) (x+l/2), |iteratedDeriv 3 f ξ| ≤ D) :
    |(f (x+l/2)-f (x-l/2))/l - deriv f x| ≤ D*l^2/24 := by
  obtain ⟨a, ha, hpa⟩ := quadratic_remainder f x (x+l/2) (by linarith) hf
  obtain ⟨b, hb, hpb⟩ := quadratic_remainder f x (x-l/2) (by linarith) hf
  have haa : a ∈ Icc (x-l/2) (x+l/2) := by
    rw [uIoo_of_lt (by linarith)] at ha
    constructor <;> linarith [ha.1, ha.2]
  have hbb : b ∈ Icc (x-l/2) (x+l/2) := by
    rw [uIoo_of_gt (by linarith)] at hb
    constructor <;> linarith [hb.1, hb.2]
  have hea : |iteratedDeriv 3 f a * (x+l/2-x)^3/6| ≤ D*(l/2)^3/6 := by
    rw [abs_div, abs_mul, abs_pow, abs_of_pos (by linarith : 0 < x+l/2-x)]
    norm_num
    convert! mul_le_mul_of_nonneg_right (hD a haa) (by positivity : 0 ≤ (l/2)^3/6) using 1 <;> ring
  have heb : |iteratedDeriv 3 f b * (x-l/2-x)^3/6| ≤ D*(l/2)^3/6 := by
    rw [abs_div, abs_mul, abs_pow, abs_of_neg (by linarith : x-l/2-x < 0)]
    norm_num
    convert! mul_le_mul_of_nonneg_right (hD b hbb) (by positivity : 0 ≤ (l/2)^3/6) using 1 <;> ring
  have he : f (x+l/2)-f (x-l/2)-l*deriv f x =
      iteratedDeriv 3 f a * (x+l/2-x)^3/6 -
      iteratedDeriv 3 f b * (x-l/2-x)^3/6 := by
    nlinarith [hpa, hpb]
  have hh := (abs_sub (iteratedDeriv 3 f a * (x+l/2-x)^3/6)
    (iteratedDeriv 3 f b * (x-l/2-x)^3/6)).trans (add_le_add hea heb)
  rw [← he] at hh
  have hr : (f (x+l/2)-f (x-l/2))/l - deriv f x =
      (f (x+l/2)-f (x-l/2)-l*deriv f x)/l := by
    field_simp
  rw [hr, abs_div, abs_of_pos hl]
  apply (div_le_iff₀ hl).2
  nlinarith [hh]

/-- Proves endpoint-value stability, the centered truncation bound, and the classical and
quantum step-size substitution identities for the prescribed target error. See
[Jordan2005Gradient]. -/
theorem classicalQuantumStepSizes : ClassicalQuantumStepSizes := by
  refine ⟨?_, central_difference_error, ?_⟩
  · intro F1 F0 f1 f0 l δ hl _ h1 h0
    have h := (abs_sub (F1-f1) (F0-f0)).trans (add_le_add h1 h0)
    have he : (F1-F0)/l-(f1-f0)/l = ((F1-f1)-(F0-f0))/l := by ring
    rw [he, abs_div, abs_of_pos hl]
    exact div_le_div_of_nonneg_right (by linarith) hl.le
  · intro σ D2 D3 d hσ h2 h3 hd
    constructor
    · rw [mul_pow, Real.sq_sqrt (by positivity)]
      field_simp
      ring
    · have hs : Real.sqrt (d : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hd))
      have hs3 : Real.sqrt 3 ≠ 0 := by positivity
      field_simp

end Qatlib.Concepts.GradientOracle.StepSizes
