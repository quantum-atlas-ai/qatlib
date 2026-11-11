/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Classical and quantum value-precision comparison

This module defines real logarithmic precision estimates for classical and quantum gradient
evaluation. It proves that their difference is `log₂(2*π/θ)`, independent of the derivative grid
resolution, and evaluates the four-bit choice `θ = π/8` discussed in [Jordan2005Gradient].

## Main statements

* `quantumRequiredBits_sub_classicalRequiredBits`: the exact logarithmic gap under nonzero
  parameter assumptions.
* `quantumRequiredBits_sub_classicalRequiredBits_pi_div_eight`: the gap is four.
* `cos_sq_pi_div_eight`: the associated cosine-squared value is `(2+sqrt 2)/4`.

## References

* [Jordan, 2005][Jordan2005Gradient]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.GradientOracle.ReadoutWindow

/-- The real logarithmic classical value-precision estimate `log₂(valRange / (m*l/2^n))`. -/
def classicalRequiredBits (valRange m l : ℝ) (n : ℕ) : ℝ :=
  Real.logb 2 (valRange / ((m * l) / (2 : ℝ) ^ n))

/-- The real logarithmic quantum value-precision estimate with tolerance `m*l/2^n` further
scaled by `theta/(2*π)`. -/
def quantumRequiredBits (valRange m l theta : ℝ) (n : ℕ) : ℝ :=
  Real.logb 2 (valRange / (((m * l) / (2 : ℝ) ^ n) * (theta / (2 * Real.pi))))

/-- For nonzero range, scale, step, and phase tolerance, the quantum precision estimate equals
the classical estimate plus `log₂(2*π/theta)`. See [Jordan2005Gradient]. -/
theorem quantumRequiredBits_eq_classicalRequiredBits_add
    (valRange m l theta : ℝ) (n : ℕ)
    (hR : valRange ≠ 0) (hm : m ≠ 0) (hl : l ≠ 0) (hθ : theta ≠ 0) :
    quantumRequiredBits valRange m l theta n
      = classicalRequiredBits valRange m l n + Real.logb 2 (2 * Real.pi / theta) := by
  unfold quantumRequiredBits classicalRequiredBits
  have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hA : (m * l) / (2 : ℝ) ^ n ≠ 0 := div_ne_zero (mul_ne_zero hm hl) h2
  have hx : valRange / ((m * l) / (2 : ℝ) ^ n) ≠ 0 := div_ne_zero hR hA
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hc : (2 * Real.pi / theta : ℝ) ≠ 0 := div_ne_zero hpi hθ
  have harg : valRange / (((m * l) / (2 : ℝ) ^ n) * (theta / (2 * Real.pi)))
      = (valRange / ((m * l) / (2 : ℝ) ^ n)) * (2 * Real.pi / theta) := by
    field_simp
  rw [harg, Real.logb_mul hx hc]

/-- Under the nonzero parameter assumptions, the quantum-minus-classical logarithmic precision
gap is exactly `log₂(2*π/theta)`. See [Jordan2005Gradient]. -/
theorem quantumRequiredBits_sub_classicalRequiredBits
    (valRange m l theta : ℝ) (n : ℕ)
    (hR : valRange ≠ 0) (hm : m ≠ 0) (hl : l ≠ 0) (hθ : theta ≠ 0) :
    quantumRequiredBits valRange m l theta n - classicalRequiredBits valRange m l n
      = Real.logb 2 (2 * Real.pi / theta) := by
  rw [quantumRequiredBits_eq_classicalRequiredBits_add valRange m l theta n hR hm hl hθ]
  ring

/-- For phase tolerance `π/8` and nonzero range, scale, and step, the real logarithmic quantum
precision estimate exceeds the classical estimate by exactly four. See [Jordan2005Gradient]. -/
theorem quantumRequiredBits_sub_classicalRequiredBits_pi_div_eight
    (valRange m l : ℝ) (n : ℕ)
    (hR : valRange ≠ 0) (hm : m ≠ 0) (hl : l ≠ 0) :
    quantumRequiredBits valRange m l (Real.pi / 8) n
      - classicalRequiredBits valRange m l n = 4 := by
  rw [quantumRequiredBits_eq_classicalRequiredBits_add
    valRange m l (Real.pi / 8) n hR hm hl (by positivity)]
  have h16 : (2 * Real.pi / (Real.pi / 8) : ℝ) = 16 := by
    field_simp
    norm_num
  rw [h16]
  have hpow : (16 : ℝ) = 2 ^ 4 := by norm_num
  rw [hpow, Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
  norm_num

/-- For nonzero parameters, the quantum-minus-classical logarithmic precision gap is independent
of the grid-resolution exponent `n`. See [Jordan2005Gradient]. -/
theorem quantumRequiredBits_gap_independent_of_n
    (valRange m l theta : ℝ) (n n' : ℕ)
    (hR : valRange ≠ 0) (hm : m ≠ 0) (hl : l ≠ 0) (hθ : theta ≠ 0) :
    quantumRequiredBits valRange m l theta n - classicalRequiredBits valRange m l n
      = quantumRequiredBits valRange m l theta n' - classicalRequiredBits valRange m l n' := by
  rw [quantumRequiredBits_sub_classicalRequiredBits valRange m l theta n hR hm hl hθ,
    quantumRequiredBits_sub_classicalRequiredBits valRange m l theta n' hR hm hl hθ]

/-- For nonzero parameters, the quantum logarithmic precision estimate equals `n +
log₂(2*π*valRange/(m*l*theta))`. See [Jordan2005Gradient]. -/
theorem quantumRequiredBits_eq_n_add
    (valRange m l theta : ℝ) (n : ℕ)
    (hR : valRange ≠ 0) (hm : m ≠ 0) (hl : l ≠ 0) (hθ : theta ≠ 0) :
    quantumRequiredBits valRange m l theta n
      = n + Real.logb 2 (2 * Real.pi * valRange / (m * l * theta)) := by
  unfold quantumRequiredBits
  have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hA : m * l ≠ 0 := mul_ne_zero hm hl
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hc : (2 * Real.pi * valRange / (m * l * theta) : ℝ) ≠ 0 :=
    div_ne_zero (mul_ne_zero hpi hR) (mul_ne_zero hA hθ)
  have harg : valRange / (((m * l) / (2 : ℝ) ^ n) * (theta / (2 * Real.pi)))
      = (2 : ℝ) ^ n * (2 * Real.pi * valRange / (m * l * theta)) := by
    field_simp
  rw [harg, Real.logb_mul h2 hc, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
  ring

/-- The value `cos (π/8)^2` equals `(2+sqrt 2)/4`, the overlap factor used in the precision
comparison of [Jordan2005Gradient]. -/
theorem cos_sq_pi_div_eight :
    Real.cos (Real.pi / 8) ^ 2 = (2 + Real.sqrt 2) / 4 := by
  rw [Real.cos_pi_div_eight]
  have h2 : (0 : ℝ) ≤ 2 + Real.sqrt 2 := by positivity
  rw [div_pow, Real.sq_sqrt h2]
  ring

/-- The overlap factor `cos (π/8)^2` is at least `0.85`. See [Jordan2005Gradient]. -/
theorem cos_sq_pi_div_eight_ge_85 :
    (0.85 : ℝ) ≤ Real.cos (Real.pi / 8) ^ 2 := by
  rw [cos_sq_pi_div_eight]
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnon : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith

/-- The overlap factor `cos (π/8)^2` is at most `0.86`. See [Jordan2005Gradient]. -/
theorem cos_sq_pi_div_eight_le_86 :
    Real.cos (Real.pi / 8) ^ 2 ≤ (0.86 : ℝ) := by
  rw [cos_sq_pi_div_eight]
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnon : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith

end Qatlib.Concepts.GradientOracle.ReadoutWindow
