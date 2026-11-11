/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Cauchy and Gamma integral identities

This module evaluates the scalar integrals used in the decision-tree passage estimates. It
expresses the Cauchy-type integral through inverse hyperbolic sine and a logarithm, and
evaluates a decaying Gamma integral with exponent one quarter.

These constructions accompany the results of [FarhiGutmann1998].

## Main statements

* `cauchy_integral_arsinh`: evaluates the reciprocal-square-root interval integral.
* `arsinh_div_eq_log`: rewrites the inverse hyperbolic sine in logarithmic form.
* `gamma_tail_uniform_decay`: gives the exact inverse-quarter-power dependence on the tail
  parameter.

## References

* [Farhi and Gutmann, 1998][FarhiGutmann1998]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators Real

namespace Qatlib.Papers.DecisionTrees97.MainResults

/-- For positive `t`, factors `t` out of the square root of `t ^ 2 + x ^ 2`. -/
theorem sqrt_one_add_div_sq {t x : ℝ} (ht : 0 < t) :
    Real.sqrt (1 + (x / t) ^ 2) = Real.sqrt (t ^ 2 + x ^ 2) / t := by
  have ht2 : 0 < t ^ 2 := by positivity
  have harg : 1 + (x / t) ^ 2 = (t ^ 2 + x ^ 2) / t ^ 2 := by
    field_simp
  rw [harg, Real.sqrt_div (by positivity : (0 : ℝ) ≤ t ^ 2 + x ^ 2), Real.sqrt_sq ht.le]

/-- For positive `t`, the integral from zero to `T` of the reciprocal of `sqrt (t ^ 2 + τ ^ 2)`
equals `arsinh (T / t)`. See [FarhiGutmann1998]. -/
theorem cauchy_integral_arsinh {t T : ℝ} (ht : 0 < t) :
    ∫ τ in (0 : ℝ)..T, (Real.sqrt (t ^ 2 + τ ^ 2))⁻¹ = Real.arsinh (T / t) := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (fun y : ℝ => Real.arsinh (y / t))
        ((Real.sqrt (t ^ 2 + x ^ 2))⁻¹) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => y / t) (1 / t) x := by
      simpa using (hasDerivAt_id x).div_const t
    have h2 := (Real.hasDerivAt_arsinh (x / t)).comp x h1
    have hsqrt := sqrt_one_add_div_sq (t := t) (x := x) ht
    convert! h2 using 1
    rw [hsqrt]
    have hB : 0 < Real.sqrt (t ^ 2 + x ^ 2) := Real.sqrt_pos.mpr (by positivity)
    field_simp
  have hcont : Continuous fun x : ℝ => (Real.sqrt (t ^ 2 + x ^ 2))⁻¹ := by
    refine Continuous.inv₀ ?_ ?_
    · fun_prop
    · intro x
      exact (Real.sqrt_pos.mpr (by positivity)).ne'
  have hint : IntervalIntegrable (fun x : ℝ => (Real.sqrt (t ^ 2 + x ^ 2))⁻¹)
      volume (0 : ℝ) T := hcont.intervalIntegrable 0 T
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [h]
  simp

/-- For positive `t`, rewrites `arsinh (T / t)` as the logarithm of `(T + sqrt (t ^ 2 + T ^ 2))
/ t`. See [FarhiGutmann1998]. -/
theorem arsinh_div_eq_log {t T : ℝ} (ht : 0 < t) :
    Real.arsinh (T / t) = Real.log ((T + Real.sqrt (t ^ 2 + T ^ 2)) / t) := by
  unfold Real.arsinh
  congr 1
  rw [sqrt_one_add_div_sq (t := t) (x := T) ht]
  field_simp

/-- For positive `T`, evaluates the integral of `μ ^ (-3 / 4) * exp (-(T * μ))` on the positive
half-line as `(1 / T) ^ (1 / 4) * Gamma (1 / 4)`. See [FarhiGutmann1998]. -/
theorem gamma_tail_integral {T : ℝ} (hT : 0 < T) :
    ∫ μ in Set.Ioi (0 : ℝ), μ ^ (-(3 : ℝ) / 4) * Real.exp (-(T * μ)) =
      (1 / T) ^ (1 / 4 : ℝ) * Real.Gamma (1 / 4) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1 / 4) (r := T)
    (by norm_num) hT
  have he : (-(3 : ℝ) / 4) = 1 / 4 - 1 := by norm_num
  rw [he]
  exact h

/-- The inverse-quarter-power Gamma tail expression is positive for positive `T`. -/
theorem gamma_tail_pos {T : ℝ} (hT : 0 < T) :
    0 < (1 / T) ^ (1 / 4 : ℝ) * Real.Gamma (1 / 4) := by
  have h1 : 0 < (1 / T) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have h2 : 0 < Real.Gamma (1 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  exact mul_pos h1 h2

/-- For positive `T`, expresses the Gamma tail integral as `Gamma (1 / 4) * (1 / T) ^ (1 / 4)`.
See [FarhiGutmann1998]. -/
theorem gamma_tail_uniform_decay {T : ℝ} (hT : 0 < T) :
    ∫ μ in Set.Ioi (0 : ℝ), μ ^ (-(3 : ℝ) / 4) * Real.exp (-(T * μ)) =
      Real.Gamma (1 / 4) * (1 / T) ^ (1 / 4 : ℝ) := by
  rw [gamma_tail_integral hT, mul_comm]

end Qatlib.Papers.DecisionTrees97.MainResults
