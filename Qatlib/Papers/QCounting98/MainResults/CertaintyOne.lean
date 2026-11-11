/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Angle reduction for certain amplification

`certaintyM0`, `certaintyTheta0`, and `certaintyA0` define the rounded iteration count, reduced
angle, and reduced marked probability for certainty method (i). The module proves the angle
comparison and the resulting sine-squared identity. The mathematical context is
[BrassardHoyerTapp1998Counting].

## Main statements

* `certainty_success_one`: Amplifying the reduced angle for `certaintyM0 θ` iterations gives
  squared sine exactly one.
* `source_certainty_one_success`: For `0 < θ ≤ π/2`, the reduced success parameter is no larger
  than `sin² θ` and its amplified squared sine equals one.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QCounting98.MainResults

/-- The natural ceiling of `π/(4θ) - 1/2` used for certainty method (i). -/
def certaintyM0 (θ : ℝ) : ℕ := Nat.ceil (Real.pi / (4 * θ) - 1 / 2)

/-- The reduced angle `π/(4 * certaintyM0 θ + 2)`. -/
def certaintyTheta0 (θ : ℝ) : ℝ := Real.pi / (4 * (certaintyM0 θ : ℝ) + 2)

/-- The squared sine of the reduced angle `certaintyTheta0 θ`. -/
def certaintyA0 (θ : ℝ) : ℝ := Real.sin (certaintyTheta0 θ) ^ 2

/-- The rounded count `certaintyM0 θ` is at least `π/(4θ) - 1/2`. -/
theorem certainty_m0_lower (θ : ℝ) :
    Real.pi / (4 * θ) - 1 / 2 ≤ (certaintyM0 θ : ℝ) :=
  Nat.le_ceil _

/-- For positive `θ`, the reduced angle `certaintyTheta0 θ` is positive. -/
theorem certainty_theta0_pos {θ : ℝ} (_hθ : 0 < θ) : 0 < certaintyTheta0 θ := by
  unfold certaintyTheta0
  have hden : (0 : ℝ) < 4 * (certaintyM0 θ : ℝ) + 2 := by positivity
  exact div_pos Real.pi_pos hden

/-- For positive `θ`, the reduced angle is at most `θ`. -/
theorem certainty_theta0_le {θ : ℝ} (hθ : 0 < θ) : certaintyTheta0 θ ≤ θ := by
  have hm := certainty_m0_lower θ
  have h4θ : (0 : ℝ) < 4 * θ := by positivity
  have hden : (0 : ℝ) < 4 * (certaintyM0 θ : ℝ) + 2 := by positivity
  have hmul : Real.pi ≤ (4 * (certaintyM0 θ : ℝ) + 2) * θ := by
    have h := hm
    rw [sub_le_iff_le_add] at h
    rw [div_le_iff₀ h4θ] at h
    nlinarith [h]
  unfold certaintyTheta0
  rw [div_le_iff₀ hden]
  nlinarith [hmul]

/-- For `0 < θ ≤ π/2`, the reduced squared sine is at most `sin² θ`. See
[BrassardHoyerTapp1998Counting]. -/
theorem certainty_a0_le {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ ≤ Real.pi / 2) :
    certaintyA0 θ ≤ Real.sin θ ^ 2 := by
  unfold certaintyA0
  have h0pos := certainty_theta0_pos hθ0
  have hle := certainty_theta0_le hθ0
  have hsinle : Real.sin (certaintyTheta0 θ) ≤ Real.sin θ :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos, h0pos])
      hθπ hle
  have hsinnn : 0 ≤ Real.sin (certaintyTheta0 θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (le_of_lt h0pos)
      (by linarith [hθπ, Real.pi_pos])
  exact pow_le_pow_left₀ hsinnn hsinle 2

/-- Amplifying the reduced angle for `certaintyM0 θ` iterations gives squared sine exactly one.
See [BrassardHoyerTapp1998Counting]. -/
theorem certainty_success_one (θ : ℝ) :
    Real.sin ((2 * (certaintyM0 θ : ℝ) + 1) * certaintyTheta0 θ) ^ 2 = 1 := by
  unfold certaintyTheta0
  have hden : (4 : ℝ) * (certaintyM0 θ : ℝ) + 2 ≠ 0 := by positivity
  have hangle : (2 * (certaintyM0 θ : ℝ) + 1) *
      (Real.pi / (4 * (certaintyM0 θ : ℝ) + 2)) = Real.pi / 2 := by
    field_simp
    ring
  rw [hangle, Real.sin_pi_div_two]
  norm_num

/-- For `0 < θ ≤ π/2`, the reduced success parameter is no larger than `sin² θ` and its
amplified squared sine equals one. See [BrassardHoyerTapp1998Counting]. -/
theorem source_certainty_one_success {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ ≤ Real.pi / 2) :
    certaintyA0 θ ≤ Real.sin θ ^ 2 ∧
      Real.sin ((2 * (certaintyM0 θ : ℝ) + 1) * certaintyTheta0 θ) ^ 2 = 1 :=
  ⟨certainty_a0_le hθ0 hθπ, certainty_success_one θ⟩

end Qatlib.Papers.QCounting98.MainResults
