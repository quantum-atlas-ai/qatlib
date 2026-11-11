/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QChemistry14.ScalarModels.Definitions
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Gaussian bias probability and reciprocal cost

`erf` is defined by its Gaussian integral, and `biasProbability` integrates a Gaussian density
over the interval from zero to a cutoff. The module evaluates this integral in terms of error
functions and verifies the reciprocal identity for `repetitionCost`. See [McCleanEtAl2014].

## Main statements

* `erf_neg`: proves oddness of the error function.
* `bias_probability_erf`: evaluates the cutoff integral for positive standard deviation.
* `repetition_cost_mul`: cancels the reciprocal cost against a positive probability parameter.

## References

* [McClean et al., 2014][McCleanEtAl2014]
-/

set_option warningAsError false

set_option autoImplicit false

open scoped Interval
open MeasureTheory

namespace Qatlib.Papers.QChemistry14.ScalarModels.VanVleck

/-- The error function defined as `2 / Real.sqrt Real.pi` times the integral of `Real.exp (-(t ^
2))` from zero to `x`. -/
noncomputable def erf (x : ℝ) : ℝ :=
  (2 / Real.sqrt Real.pi) * ∫ t in (0 : ℝ)..x, Real.exp (-(t ^ 2))

/-- The integral from zero to `M` of the Gaussian density with center `Nbar` and scale parameter
`σ`. -/
noncomputable def biasProbability (Nbar σ M : ℝ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi * σ ^ 2)) *
    ∫ x in (0 : ℝ)..M, Real.exp (-(1 / 2) * ((x - Nbar) / σ) ^ 2)

/-- The reciprocal `1 / P`, used as the scalar repetition cost. -/
noncomputable def repetitionCost (P : ℝ) : ℝ := 1 / P

/-- The error function is odd: `erf (-x) = -erf x`. -/
theorem erf_neg (x : ℝ) : erf (-x) = -erf x := by
  unfold erf
  have h : ∫ u in (0:ℝ)..(-x), Real.exp (-(u^2))
      = - ∫ u in (0:ℝ)..x, Real.exp (-(u^2)) := by
    have h1 : ∫ u in (0:ℝ)..(-x), Real.exp (-(u^2))
        = ∫ u in (0:ℝ)..(-x), Real.exp (-((-u)^2)) := by
      congr 1 with u
      ring_nf
    rw [h1]
    rw [intervalIntegral.integral_comp_neg (f := fun t : ℝ => Real.exp (-(t^2)))
      (a := (0:ℝ)) (b := -x)]
    simp only [neg_zero, neg_neg]
    rw [intervalIntegral.integral_symm]
  rw [h]
  ring

/-- For positive `σ`, the Gaussian cutoff integral equals half the sum of the error functions at
`(M - Nbar) / Real.sqrt (2 * σ ^ 2)` and `Nbar / Real.sqrt (2 * σ ^ 2)`. This evaluates the
scalar probability in Eqs. (59)–(60) of [McCleanEtAl2014]. -/
theorem bias_probability_erf (Nbar σ M : ℝ) (hσ : 0 < σ) :
    biasProbability Nbar σ M
      = (1 / 2) * (erf ((M - Nbar) / Real.sqrt (2 * σ ^ 2))
          + erf (Nbar / Real.sqrt (2 * σ ^ 2))) := by
  unfold biasProbability
  set c : ℝ := σ * Real.sqrt 2 with hc_def
  have hcpos : 0 < c := by positivity
  have hc : c ≠ 0 := ne_of_gt hcpos
  have hsqrt2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hpoint : (fun x : ℝ => Real.exp (-(1 / 2) * ((x - Nbar) / σ) ^ 2))
      = fun x : ℝ => Real.exp (-((x / c - Nbar / c) ^ 2)) := by
    funext x
    congr 1
    rw [hc_def]
    field_simp
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    ring
  rw [hpoint]
  simp only [sub_eq_add_neg]
  rw [intervalIntegral.integral_comp_div_add (f := fun u : ℝ => Real.exp (-(u ^ 2)))
    (a := (0:ℝ)) (b := M) hc (-(Nbar / c))]
  simp only [zero_div, zero_add]
  have hupper : M / c + -(Nbar / c) = (M - Nbar) / c := by field_simp; ring
  rw [hupper]
  have hcont : Continuous fun u : ℝ => Real.exp (-(u ^ 2)) := by fun_prop
  have hb_int : IntervalIntegrable (fun u : ℝ => Real.exp (-(u ^ 2))) volume 0 ((M - Nbar) / c) :=
    hcont.intervalIntegrable _ _
  have ha_int : IntervalIntegrable (fun u : ℝ => Real.exp (-(u ^ 2))) volume 0 (-(Nbar / c)) :=
    hcont.intervalIntegrable _ _
  rw [← intervalIntegral.integral_interval_sub_left hb_int ha_int]
  have hI (x : ℝ) : ∫ u in (0:ℝ)..x, Real.exp (-(u ^ 2)) = erf x * Real.sqrt Real.pi / 2 := by
    unfold erf
    have hpi : Real.sqrt Real.pi ≠ 0 := Real.sqrt_ne_zero'.mpr Real.pi_pos
    field_simp
  rw [hI ((M - Nbar) / c), hI (-(Nbar / c)), erf_neg (Nbar / c)]
  have hc_sq : c ^ 2 = 2 * σ ^ 2 := by
    rw [hc_def, mul_pow, Real.sq_sqrt (by norm_num)]
    ring
  have hc_sqrt : Real.sqrt (2 * σ ^ 2) = c := by
    rw [← hc_sq, Real.sqrt_sq (le_of_lt hcpos)]
  rw [hc_sqrt]
  have hden : Real.sqrt (2 * Real.pi * σ ^ 2) = c * Real.sqrt Real.pi := by
    rw [show 2 * Real.pi * σ ^ 2 = c ^ 2 * Real.pi by rw [hc_sq]; ring]
    rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq (le_of_lt hcpos)]
  rw [hden]
  field_simp
  rw [show M + -Nbar = M - Nbar by ring]
  simp only [smul_eq_mul]
  ring

/-- For positive `P`, multiplying `repetitionCost P` by `P` gives one. -/
theorem repetition_cost_mul (P : ℝ) (hP : 0 < P) :
    repetitionCost P * P = 1 := by
  unfold repetitionCost
  field_simp

end Qatlib.Papers.QChemistry14.ScalarModels.VanVleck
