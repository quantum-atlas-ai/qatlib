/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkLine00.MainResults.WalkModel.SpectralFacts
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Stationary-point identities for line walks

This module evaluates the sine and cosine of `kAlpha`, establishes its stationary-point
derivative identity, and relates the second dispersion derivative expression to
`omegaSecondAtStationary`. It also verifies the defining cosine relation for the coin-angle
dispersion family used in [NayakVishwanath2000].

## Main statements

* `hasDerivAt_dispersion_at_kAlpha`: gives dispersion derivative `-α` at the stationary-point
  expression.
* `dispersion_second_at_kAlpha`: identifies the negative stationary curvature.
* `cos_dispersionTheta`: gives the cosine relation for the parameterized family.

## References

* [Nayak and Vishwanath, 2000][NayakVishwanath2000]
-/

set_option warningAsError false

namespace Qatlib.Papers.QWalkLine00.MainResults

set_option autoImplicit false

open Real

noncomputable section

/-- For `α² < 1/2`, the cosine of `kAlpha α` is `-α / √(1 - α²)`. -/
theorem cos_kAlpha {α : ℝ} (hα : α ^ 2 < 1 / 2) :
    Real.cos (kAlpha α) = -α / Real.sqrt (1 - α ^ 2) := by
  unfold kAlpha
  have h1α : 0 ≤ 1 - α ^ 2 := by nlinarith
  have hpos : (0 : ℝ) < Real.sqrt (1 - α ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hlt : |α| < Real.sqrt (1 - α ^ 2) := by
    have hsq : α ^ 2 < 1 - α ^ 2 := by nlinarith
    have := Real.sqrt_lt_sqrt (sq_nonneg α) hsq
    rwa [Real.sqrt_sq_eq_abs] at this
  have habs : |(-α) / Real.sqrt (1 - α ^ 2)| < 1 := by
    rw [abs_div, abs_neg, abs_of_pos hpos, div_lt_one hpos]
    exact hlt
  exact Real.cos_arccos (le_of_lt (abs_lt.mp habs).1) (le_of_lt (abs_lt.mp habs).2)

/-- For `α² < 1/2`, `√(1 - cos² (kAlpha α))` equals `√(1 - 2 * α²) / √(1 - α²)`. -/
theorem sqrt_one_sub_sq_kAlpha {α : ℝ} (hα : α ^ 2 < 1 / 2) :
    Real.sqrt (1 - Real.cos (kAlpha α) ^ 2) = Real.sqrt (1 - 2 * α ^ 2) / Real.sqrt (1 - α ^ 2) := by
  rw [cos_kAlpha hα]
  have hpos : (0 : ℝ) < Real.sqrt (1 - α ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hsq : (Real.sqrt (1 - α ^ 2)) ^ 2 = 1 - α ^ 2 := Real.sq_sqrt (by nlinarith)
  have key : (1 : ℝ) - (-α / Real.sqrt (1 - α ^ 2)) ^ 2
      = (1 - 2 * α ^ 2) / (1 - α ^ 2) := by
    have hne : (1 - α ^ 2) ≠ 0 := ne_of_gt (by nlinarith)
    field_simp
    nlinarith [hsq]
  rw [key, Real.sqrt_div' (1 - 2 * α ^ 2) (by nlinarith)]

/-- The cosine of `dispersionTheta θ k` is `cos (θ / 2) * cos k`. See [NayakVishwanath2000]. -/
theorem cos_dispersionTheta (θ k : ℝ) :
    Real.cos (dispersionTheta θ k) = Real.cos (θ / 2) * Real.cos k := by
  unfold dispersionTheta
  have hb : |Real.cos (θ / 2) * Real.cos k| ≤ 1 := by
    rw [abs_mul]
    have h1 := Real.abs_cos_le_one (θ / 2)
    have h2 := Real.abs_cos_le_one k
    have h1n : 0 ≤ |Real.cos (θ / 2)| := abs_nonneg _
    have h2n : 0 ≤ |Real.cos k| := abs_nonneg _
    nlinarith [abs_mul (Real.cos (θ / 2)) (Real.cos k)]
  exact Real.cos_arccos (abs_le.mp hb).1 (abs_le.mp hb).2

/-- The stationary-point expression `kAlpha α` lies in `[0, π]`. -/
lemma kAlpha_mem_Icc (α : ℝ) : kAlpha α ∈ Set.Icc 0 Real.pi :=
  ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

/-- For `α² < 1/2`, `1 + cos² (kAlpha α)` equals `1 / (1 - α²)`. -/
lemma one_add_cos_sq_kAlpha {α : ℝ} (hα : α ^ 2 < 1 / 2) :
    1 + Real.cos (kAlpha α) ^ 2 = 1 / (1 - α ^ 2) := by
  have h1 : (0 : ℝ) < 1 - α ^ 2 := by nlinarith
  have hsq : (Real.sqrt (1 - α ^ 2)) ^ 2 = 1 - α ^ 2 := Real.sq_sqrt h1.le
  rw [cos_kAlpha hα, div_pow, hsq]
  field_simp
  ring

/-- For `α² < 1/2`, the sine of `kAlpha α` is `√(1 - 2 * α²) / √(1 - α²)`. -/
theorem sin_kAlpha {α : ℝ} (hα : α ^ 2 < 1 / 2) :
    Real.sin (kAlpha α) = Real.sqrt (1 - 2 * α ^ 2) / Real.sqrt (1 - α ^ 2) := by
  obtain ⟨h0, hπ⟩ := kAlpha_mem_Icc α
  rw [Real.sin_eq_sqrt_one_sub_cos_sq h0 hπ, cos_kAlpha hα]
  have h1 : (0 : ℝ) < 1 - α ^ 2 := by nlinarith
  have hne : (1 : ℝ) - α ^ 2 ≠ 0 := ne_of_gt h1
  have hkey : 1 - (-α / Real.sqrt (1 - α ^ 2)) ^ 2 = (1 - 2 * α ^ 2) / (1 - α ^ 2) := by
    have hsq : (Real.sqrt (1 - α ^ 2)) ^ 2 = 1 - α ^ 2 := Real.sq_sqrt (le_of_lt h1)
    field_simp
    nlinarith [hsq]
  rw [hkey, Real.sqrt_div' (1 - 2 * α ^ 2) (le_of_lt h1)]

/-- For `α² < 1/2`, the dispersion derivative expression at `kAlpha α` equals `-α`. -/
theorem dispersion_deriv_at_kAlpha {α : ℝ} (hα : α ^ 2 < 1 / 2) :
    Real.cos (kAlpha α) / Real.sqrt (1 + Real.cos (kAlpha α) ^ 2) = -α := by
  rw [one_add_cos_sq_kAlpha hα, cos_kAlpha hα]
  have h1 : (0 : ℝ) < 1 - α ^ 2 := by nlinarith
  rw [Real.sqrt_div' 1 (le_of_lt h1), Real.sqrt_one]
  have hne : (1 : ℝ) - α ^ 2 ≠ 0 := ne_of_gt h1
  field_simp

/-- For `α² < 1/2`, the dispersion has derivative `-α` at `kAlpha α`. -/
theorem hasDerivAt_dispersion_at_kAlpha {α : ℝ} (hα : α ^ 2 < 1 / 2) :
    HasDerivAt dispersion (-α) (kAlpha α) := by
  have h := hasDerivAt_dispersion (kAlpha α)
  rwa [dispersion_deriv_at_kAlpha hα] at h

/-- For `α² < 1/2`, the second dispersion derivative expression at `kAlpha α` equals
`-omegaSecondAtStationary α`. See [NayakVishwanath2000]. -/
theorem dispersion_second_at_kAlpha {α : ℝ} (hα : α ^ 2 < 1 / 2) :
    -Real.sin (kAlpha α) / (Real.sqrt (1 + Real.cos (kAlpha α) ^ 2)) ^ 3
      = -omegaSecondAtStationary α := by
  rw [sin_kAlpha hα, cos_kAlpha hα]
  have h1 : (0 : ℝ) < 1 - α ^ 2 := by nlinarith
  have h2 : (0 : ℝ) < 1 - 2 * α ^ 2 := by nlinarith
  have hsq : (Real.sqrt (1 - α ^ 2)) ^ 2 = 1 - α ^ 2 := Real.sq_sqrt (le_of_lt h1)
  have hspos : (0 : ℝ) < Real.sqrt (1 - α ^ 2) := Real.sqrt_pos.2 h1
  rw [show 1 + (-α / Real.sqrt (1 - α ^ 2)) ^ 2 = 1 / (1 - α ^ 2) by
    rw [div_pow, hsq]
    have hne : (1 : ℝ) - α ^ 2 ≠ 0 := ne_of_gt h1
    field_simp
    ring]
  rw [Real.sqrt_div' 1 (le_of_lt h1), Real.sqrt_one]
  unfold omegaSecondAtStationary
  field_simp
  rw [hsq]

end

end Qatlib.Papers.QWalkLine00.MainResults
