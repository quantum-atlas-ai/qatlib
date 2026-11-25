/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HydroSpinLatt21.GKModel.BesselCoefficientBridge

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# First-order expansion of the azimuthal projection

[Saenz2021HydroSpinLattices], Methods equations (18)–(22),
[DOI](https://doi.org/10.1038/s41586-021-03682-1).
The order-`r / L` longitudinal term in the numerator of the unit
separation projection cancels the corresponding reciprocal-distance
term. Keeping those terms together gives a quadratic error.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.HydroSpinLatt21.BesselModel

open Qatlib.Papers.HydroSpinLatt21.GKModel
open Real

/-- Left azimuthal projection of the pair separation divided by its length. -/
noncomputable def azimuthProjection (r L φ ψ : ℝ) : ℝ :=
  (L * sin φ + r * sin (φ - ψ)) / pairDist r L φ ψ

/-- A gap between profile values in the interval `[-1, 1]` has magnitude at most two. -/
private theorem gap_abs_le_two {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    |x - y| ≤ 2 := by
  rw [sub_eq_add_neg]
  have h := abs_add_le x (-y)
  rw [abs_neg] at h
  linarith only [h, hx, hy]

/-- The exact normalization of the separation vector has a bounded
projection, a linear deviation from the zeroth-order sine, and a quadratic
remainder after correction by the first-order transverse phase gap. -/
theorem azimuth_projection_bounds (r L φ ψ : ℝ)
    (hL : 0 < L) (hr : 0 < r) (hrL : r ≤ L / 4) :
    |azimuthProjection r L φ ψ| ≤ 3 ∧
      |azimuthProjection r L φ ψ - sin φ| ≤ 8 * r / L ∧
      |azimuthProjection r L φ ψ - (sin φ + (r / L) * (cos φ * (sin φ - sin ψ)))|
        ≤ 20 * r ^ 2 / L ^ 2 := by
  let d := pairDist r L φ ψ
  let S := sin φ
  let V := sin (φ - ψ)
  let U := cos φ * (sin φ - sin ψ)
  let δ := cos ψ - cos φ
  have hdge : L / 2 ≤ d := pairDist_ge_half r L φ ψ hL hr hrL
  have hd : 0 < d := (half_pos hL).trans_le hdge
  have hn : |d - L| ≤ 3 * r := pairDist_sub_L_le r L φ ψ hL hr hrL
  have hn' : |L - d| ≤ 3 * r := by rwa [abs_sub_comm]
  have he : |L + r * δ - d| ≤ 4 * r ^ 2 / L := by
    rw [abs_sub_comm]
    exact pairDist_sub_longitudinal_le r L φ ψ hL hr hrL
  have hS : |S| ≤ 1 := Real.abs_sin_le_one φ
  have hV : |V| ≤ 1 := Real.abs_sin_le_one (φ - ψ)
  have hU : |U| ≤ 2 := by
    rw [show U = cos φ * (sin φ - sin ψ) from rfl, abs_mul]
    simpa only [one_mul] using
      mul_le_mul (Real.abs_cos_le_one φ)
        (gap_abs_le_two (Real.abs_sin_le_one φ) (Real.abs_sin_le_one ψ)) (abs_nonneg _) zero_le_one
  have hVeq : V = δ * S + U := by
    unfold V δ S U
    rw [Real.sin_sub]
    ring
  have hLr : 0 ≤ r / L := div_nonneg hr.le hL.le
  change |(L * S + r * V) / d| ≤ 3 ∧
    |(L * S + r * V) / d - S| ≤ 8 * r / L ∧
    |(L * S + r * V) / d - (S + (r / L) * U)| ≤ 20 * r ^ 2 / L ^ 2
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_div, abs_of_pos hd]
    apply (div_le_iff₀ hd).2
    calc
      _ ≤ |L * S| + |r * V| := abs_add_le _ _
      _ ≤ L + r := by
        rw [abs_mul, abs_mul, abs_of_pos hL, abs_of_pos hr]
        simpa only [mul_one] using
          add_le_add (mul_le_mul_of_nonneg_left hS hL.le) (mul_le_mul_of_nonneg_left hV hr.le)
      _ ≤ 3 * d := by linarith only [hdge, hrL, hL.le]
  · have hrewrite : (L * S + r * V) / d - S = ((L - d) * S + r * V) / d := by
      field_simp [hd.ne']
      ring
    have hnum : |(L - d) * S + r * V| ≤ 4 * r := by
      calc
        _ ≤ |(L - d) * S| + |r * V| := abs_add_le _ _
        _ ≤ 3 * r * 1 + r * 1 := by
          rw [abs_mul, abs_mul, abs_of_pos hr]
          exact add_le_add (mul_le_mul hn' hS (abs_nonneg _) (by positivity))
            (mul_le_mul_of_nonneg_left hV hr.le)
        _ = _ := by ring
    rw [hrewrite, abs_div, abs_of_pos hd]
    calc
      _ ≤ (4 * r) / d := div_le_div_of_nonneg_right hnum hd.le
      _ ≤ (4 * r) / (L / 2) := div_le_div_of_nonneg_left (by positivity) (half_pos hL) hdge
      _ = _ := by ring
  · have hrewrite : (L * S + r * V) / d - (S + (r / L) * U) =
        ((L + r * δ - d) * S + (r / L) * (L - d) * U) / d := by
      rw [hVeq]
      field_simp [hd.ne', hL.ne']
      ring
    have hnum : |(L + r * δ - d) * S + (r / L) * (L - d) * U| ≤ 10 * r ^ 2 / L := by
      calc
        _ ≤ |(L + r * δ - d) * S| + |(r / L) * (L - d) * U| := abs_add_le _ _
        _ ≤ (4 * r ^ 2 / L) * 1 + ((r / L) * (3 * r)) * 2 := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hLr]
          exact add_le_add (mul_le_mul he hS (abs_nonneg _) (by positivity))
            (mul_le_mul (mul_le_mul_of_nonneg_left hn' hLr) hU (abs_nonneg _) (by positivity))
        _ = _ := by ring
    rw [hrewrite, abs_div, abs_of_pos hd]
    calc
      _ ≤ (10 * r ^ 2 / L) / d := div_le_div_of_nonneg_right hnum hd.le
      _ ≤ (10 * r ^ 2 / L) / (L / 2) :=
        div_le_div_of_nonneg_left (by positivity) (half_pos hL) hdge
      _ = _ := by ring

end Qatlib.Papers.HydroSpinLatt21.BesselModel
