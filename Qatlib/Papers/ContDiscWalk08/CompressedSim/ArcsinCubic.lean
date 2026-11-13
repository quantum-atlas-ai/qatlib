/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# A cubic bound for the arcsine phase error

This module bounds the difference between a real number and its arcsine on the unit interval.
The estimate `abs_arcsin_sub_self_le_two_mul_abs_cube` gives the cubic phase control used for
compressed continuous-time simulation by a discrete-time walk in [Childs2010].

## Main statements

* `arcsin_sub_self_le_two_mul_cube`: Bounds `arcsin lam - lam` by `2 * lam ^ 3` on `[0, 1]`.
* `abs_arcsin_sub_self_le_two_mul_abs_cube`: Extends the bound to `|lam| ≤ 1` using absolute
  values.

## References

* [Childs, 2010][Childs2010]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.ContDiscWalk08.CompressedSim

/-- For `0 ≤ lam ≤ 1`, the arcsine remainder satisfies `Real.arcsin lam - lam ≤ 2 * lam ^ 3`. -/
theorem arcsin_sub_self_le_two_mul_cube {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    Real.arcsin lam - lam ≤ 2 * lam ^ 3 := by
  set u := Real.arcsin lam with hu_def
  have hu0 : 0 ≤ u := Real.arcsin_nonneg.mpr h0
  have hu_pi : u ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two lam
  have hsin : Real.sin u = lam := Real.sin_arcsin (by linarith) h1
  rcases hu0.eq_or_lt with hu_eq | hu_pos
  · have hlam0 : lam = 0 := by rw [← hsin, ← hu_eq, Real.sin_zero]
    rw [hlam0]
    norm_num
    linarith [hu_eq]
  by_cases hu_le : u ≤ 1
  · have hgt : u - u ^ 3 / 4 < Real.sin u := by
      linarith [Real.sin_gt_sub_cube hu_pos, pow_nonneg hu_pos.le 3]
    have hu2 : u ^ 2 ≤ 1 := by
      have := mul_self_le_mul_self hu0 hu_le
      simpa [pow_two] using this
    have huu : u ^ 3 ≤ u := by
      have h := mul_le_mul_of_nonneg_left hu2 hu0
      nlinarith [h]
    have hhalf : u / 2 < Real.sin u := by linarith
    have hcube : u ^ 3 < 8 * Real.sin u ^ 3 := by
      have h2 : u < 2 * Real.sin u := by linarith
      have hp := pow_lt_pow_left₀ h2 hu0 (n := 3) (by norm_num)
      have he : (2 * Real.sin u) ^ 3 = 8 * Real.sin u ^ 3 := by ring
      linarith
    rw [← hsin]
    nlinarith [hgt, hcube]
  · have hu_ge : 1 ≤ u := le_of_lt (lt_of_not_ge hu_le)
    have hsin_mono : Real.sin 1 ≤ Real.sin u :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (x := 1) (y := u)
        (by linarith [Real.pi_pos]) hu_pi hu_ge
    have hsin_gt : (3 / 4 : ℝ) < Real.sin u := by
      have h1' : (3 / 4 : ℝ) < Real.sin 1 := by
        have h := Real.sin_gt_sub_cube zero_lt_one
        norm_num at h
        linarith
      linarith
    have hupper : u - Real.sin u ≤ Real.pi / 2 - 3 / 4 := by linarith
    have hlower : 2 * (3 / 4 : ℝ) ^ 3 ≤ 2 * Real.sin u ^ 3 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 4) (le_of_lt hsin_gt) 3
      nlinarith [h]
    have hpi : Real.pi / 2 - 3 / 4 < 2 * (3 / 4 : ℝ) ^ 3 := by
      have h := Real.pi_lt_d20
      norm_num at h ⊢
      linarith
    rw [← hsin]
    linarith

/-- For `0 ≤ lam ≤ 1`, `lam ≤ Real.arcsin lam`. -/
theorem le_arcsin_self {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    lam ≤ Real.arcsin lam := by
  have hsin : Real.sin lam ≤ lam := Real.sin_le h0
  have hmono : Real.arcsin (Real.sin lam) ≤ Real.arcsin lam := Real.arcsin_le_arcsin hsin
  have harc : Real.arcsin (Real.sin lam) = lam :=
    Real.arcsin_sin (by linarith [Real.pi_div_two_pos]) (by linarith [Real.pi_gt_three])
  linarith

/-- For `|lam| ≤ 1`, the phase remainder satisfies `|Real.arcsin lam - lam| ≤ 2 * |lam| ^ 3`.
This supplies cubic phase control for the compressed-simulation estimates associated with
[Childs, Theorem 2][Childs2010]. -/
theorem abs_arcsin_sub_self_le_two_mul_abs_cube {lam : ℝ} (h : |lam| ≤ 1) :
    |Real.arcsin lam - lam| ≤ 2 * |lam| ^ 3 := by
  have hpos := arcsin_sub_self_le_two_mul_cube (abs_nonneg lam) h
  have hle1 : abs lam ≤ 1 := h
  rcases le_total 0 lam with hs | hs
  · have hle : lam ≤ 1 := by rw [← abs_of_nonneg hs]; exact h
    have hnonneg : 0 ≤ Real.arcsin lam - lam := by linarith [le_arcsin_self hs hle]
    rw [abs_of_nonneg hs] at hpos ⊢
    rw [abs_of_nonneg hnonneg]
    exact hpos
  · have hneg : |lam| = -lam := abs_of_nonpos hs
    have hnonneg : 0 ≤ Real.arcsin |lam| - |lam| :=
      sub_nonneg.mpr (le_arcsin_self (abs_nonneg lam) hle1)
    have harc : Real.arcsin lam = -Real.arcsin |lam| := by
      rw [hneg, Real.arcsin_neg]
      ring
    have hstep : -Real.arcsin |lam| - lam = -(Real.arcsin |lam| - |lam|) := by
      rw [hneg]
      ring
    rw [harc, hstep, abs_neg, abs_of_nonneg hnonneg]
    exact hpos

end Qatlib.Papers.ContDiscWalk08.CompressedSim
