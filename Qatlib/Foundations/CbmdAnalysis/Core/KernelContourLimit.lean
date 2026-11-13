/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.KernelContourBounds

/-!
# Vanishing square boundary integrals

`halfGridRadius` specifies expanding squares whose vertical sides avoid the sampling lattice,
and `squareBoundaryIntegral` sums their four oriented edge integrals. A quadratic majorant
controls the vertical edges even as their lengths grow.

Together with the horizontal estimates, this proves that the square boundary integrals vanish
for functions with compatible half-plane growth, as required by the contour method in
[WangEtAl2026].

## Main statements

* `integerContour_square_vertical_tendsto_zero`: handles the growing vertical edges.
* `integerContour_square_tendsto_zero`: proves vanishing of the full boundary integral.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace CBMD
open Filter MeasureTheory
open scoped Topology

/-- The half-grid radius `(n + 1/2) / a`. -/
def halfGridRadius (a : ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1 / 2) / a

/-- For positive spacing, the half-grid radii tend to infinity. -/
theorem halfGridRadius_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (halfGridRadius a) atTop atTop :=
  (tendsto_atTop_add_const_right atTop (1 / 2 : ℝ)
    (tendsto_natCast_atTop_atTop (R := ℝ))).atTop_div_const ha

/-- If `R ≥ 2m + 2`, the vertical edge bound with length `2R` is at most `4 *
kernelNormalization m / (R - m)²`. -/
private theorem vertical_square_majorant (m : ℕ) {R : ℝ}
    (hR : 2 * m + 2 ≤ R) :
    kernelNormalization m / (R - m) ^ (2 * m + 3) * (2 * R) ≤
      4 * kernelNormalization m / (R - m) ^ 2 := by
  have hd : 1 ≤ R - m := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hd0 : 0 < R - m := by linarith
  have hp : (R - m) ^ 3 ≤ (R - m) ^ (2 * m + 3) :=
    pow_le_pow_right₀ hd (by omega)
  calc
    _ ≤ kernelNormalization m / (R - m) ^ 3 * (4 * (R - m)) :=
      mul_le_mul (div_le_div_of_nonneg_left (kernelNormalization_pos m).le (by positivity) hp)
        (by linarith) (by linarith) (div_nonneg (kernelNormalization_pos m).le (by positivity))
    _ = _ := by field_simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]

/-- Under the stated growth and spacing bounds, both vertical edge integrals of the expanding
half-grid squares tend to zero. -/
theorem integerContour_square_vertical_tendsto_zero (m : ℕ) {a ρ : ℝ} (ha : 0 < a)
    (hρ : ρ ≤ 2 * Real.pi * a) (U : ℂ → E)
    (hU : ∀ z, ‖U z‖ ≤ Real.exp (max z.im 0 * ρ)) :
    Tendsto (fun n : ℕ => ∫ y in -halfGridRadius a n..halfGridRadius a n,
      Complex.I • integerContourIntegrand m a U
        ((halfGridRadius a n : ℂ) + (y : ℂ) * Complex.I)) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => ∫ y in -halfGridRadius a n..halfGridRadius a n,
      Complex.I • integerContourIntegrand m a U
        ((-halfGridRadius a n : ℝ) + (y : ℂ) * Complex.I)) atTop (𝓝 0) := by
  have hR := halfGridRadius_tendsto ha
  have hRpos (n : ℕ) : 0 ≤ halfGridRadius a n := by dsimp [halfGridRadius]; positivity
  have hd : Tendsto (fun n => halfGridRadius a n - m) atTop atTop := by
    simpa only [sub_eq_add_neg] using! tendsto_atTop_add_const_right atTop (-(m : ℝ)) hR
  have hlim : Tendsto (fun n => 4 * kernelNormalization m / (halfGridRadius a n - m) ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hd)
  constructor
  · apply squeeze_zero_norm' _ hlim
    filter_upwards [hR.eventually_ge_atTop (2 * (m : ℝ) + 2)] with n hn
    have hAbs : |((n : ℝ) + 1 / 2) / a| = halfGridRadius a n := abs_of_nonneg (hRpos n)
    have hb := integerContour_vertical_integral_le m ha hρ U hU (n : ℤ) (-halfGridRadius a n) (halfGridRadius a n)
      (by simpa only [Int.cast_natCast, hAbs] using!
        (show (m : ℝ) < halfGridRadius a n by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]))
    have he : |halfGridRadius a n - -halfGridRadius a n| = 2 * halfGridRadius a n := by
      rw [sub_neg_eq_add, abs_of_nonneg (add_nonneg (hRpos n) (hRpos n))]; ring
    have hb' : ‖∫ y in -halfGridRadius a n..halfGridRadius a n,
        Complex.I • integerContourIntegrand m a U
          ((halfGridRadius a n : ℂ) + (y : ℂ) * Complex.I)‖ ≤
        kernelNormalization m / (halfGridRadius a n - m) ^ (2 * m + 3) * (2 * halfGridRadius a n) := by
      simpa only [Int.cast_natCast, hAbs, he] using! hb
    exact hb'.trans (vertical_square_majorant m hn)
  · apply squeeze_zero_norm' _ hlim
    filter_upwards [hR.eventually_ge_atTop (2 * (m : ℝ) + 2)] with n hn
    have he : (((-(n : ℤ) - 1 : ℤ) : ℝ) + 1 / 2) / a = -halfGridRadius a n := by
      dsimp [halfGridRadius]; push_cast; ring
    have hb := integerContour_vertical_integral_le m ha hρ U hU (-(n : ℤ) - 1) (-halfGridRadius a n) (halfGridRadius a n)
      (by rw [he, abs_neg, abs_of_nonneg (hRpos n)]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
    have he' : |halfGridRadius a n - -halfGridRadius a n| = 2 * halfGridRadius a n := by
      rw [sub_neg_eq_add, abs_of_nonneg (add_nonneg (hRpos n) (hRpos n))]; ring
    rw [he, abs_neg, abs_of_nonneg (hRpos n), he'] at hb
    exact hb.trans (vertical_square_majorant m hn)

/-- The counterclockwise boundary integral around the square with corners `±R ± iR`, expressed
as four real interval integrals. -/
def squareBoundaryIntegral (f : ℂ → E) (R : ℝ) : E :=
  (∫ x in -R..R, f ((x : ℂ) + (-R : ℂ) * Complex.I)) +
  (∫ y in -R..R, Complex.I • f ((R : ℂ) + (y : ℂ) * Complex.I)) -
  (∫ x in -R..R, f ((x : ℂ) + (R : ℂ) * Complex.I)) -
  (∫ y in -R..R, Complex.I • f ((-R : ℂ) + (y : ℂ) * Complex.I))

/-- Under the stated growth and spacing bounds, the integer contour integrand has boundary
integrals tending to zero on expanding half-grid squares. -/
theorem integerContour_square_tendsto_zero (m : ℕ) {a ρ : ℝ} (ha : 0 < a)
    (hρ : ρ ≤ 2 * Real.pi * a) (U : ℂ → E)
    (hU : ∀ z, ‖U z‖ ≤ Real.exp (max z.im 0 * ρ)) :
    Tendsto (fun n : ℕ => squareBoundaryIntegral (integerContourIntegrand m a U)
      (halfGridRadius a n)) atTop (𝓝 0) := by
  obtain ⟨hvR, hvL⟩ := integerContour_square_vertical_tendsto_zero m ha hρ U hU
  obtain ⟨hhT, hhB⟩ := integerContour_horizontal_integrals_tendsto_zero m ha hρ U hU
    (fun Y => -Y) (fun Y => Y)
  have ht := hhT.comp (halfGridRadius_tendsto ha)
  have hb := hhB.comp (halfGridRadius_tendsto ha)
  simpa only [squareBoundaryIntegral, Function.comp_def, zero_add, sub_zero, Complex.ofReal_neg] using!
    ((hb.add hvR).sub ht).sub hvL

end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
