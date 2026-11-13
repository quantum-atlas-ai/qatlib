/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Rounding.Analytic.GaussianPairTilt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Closed forms for tilted Gaussian pair moments

The polynomial `determinant` controls the Gaussian pair integrals with correlation parameter of
absolute value less than one. The module proves its positivity and simplifies the tilted mass
and cross moment to explicit inverse square-root expressions. See [CrostaSaubanereHuber2026].

## Main statements

* `pair_mass`: evaluates the tilted pair mass as `1 / √determinant`.
* `pair_cross`: evaluates the tilted pair cross moment as `t / (determinant * √determinant)`.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical NNReal
open MeasureTheory ProbabilityTheory Set Real
namespace Qatlib.Papers.RydbergMaxCut26.Rounding.TiltedClosed
open Qatlib.Papers.RydbergMaxCut26.Rounding.Laplace

/-- The polynomial `1 + 2 * a + 2 * b + 4 * (1 - t²) * a * b` governing the tilted Gaussian pair
integrals. -/
def determinant (t a b : ℝ) : ℝ := 1+2*a+2*b+4*(1-t^2)*a*b

/-- For `|t| < 1`, the square of the noise scale `√(1 - t²)` is `1 - t²`. -/
theorem noise_square (t : ℝ) (ht : |t| < 1) : (Real.sqrt (1-t^2))^2=1-t^2 := by
  have h := abs_lt.mp ht
  have hsq : t^2 < 1 := by nlinarith [sq_nonneg (t+1),sq_nonneg (t-1)]
  exact Real.sq_sqrt (by linarith)

/-- For `|t| < 1` and nonnegative tilt parameters, `determinant t a b` is positive. -/
theorem determinant_positive (t a b : ℝ) (ht : |t| < 1) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 < determinant t a b := by
  have hs : 0 ≤ 1-t^2 := by rw [← noise_square t ht];positivity
  unfold determinant
  nlinarith [mul_nonneg (mul_nonneg hs ha) hb]

/-- For `|t| < 1` and nonnegative `b`, four times the product of the noise and outer precisions
equals `determinant t a b`. -/
theorem precisions_product (t a b : ℝ) (ht : |t| < 1) (hb : 0 ≤ b) :
    4*noisePrecision b (Real.sqrt (1-t^2))*outerPrecision t (Real.sqrt (1-t^2)) a b=determinant t a b := by
  have hden : 1+2*b*(Real.sqrt (1-t^2))^2 ≠ 0 := by positivity
  unfold outerPrecision remainingRate noisePrecision determinant
  field_simp
  rw [noise_square t ht]
  ring

/-- For `|t| < 1` and nonnegative tilt parameters, the product of the Gaussian normalization and
precision factors equals `1 / √(determinant t a b)`. -/
theorem prefactor_closed (t a b : ℝ) (ht : |t| < 1) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt (2*Real.pi))⁻¹^2*Real.sqrt (Real.pi/noisePrecision b (Real.sqrt (1-t^2)))*
      Real.sqrt (Real.pi/outerPrecision t (Real.sqrt (1-t^2)) a b)=
      1/Real.sqrt (determinant t a b) := by
  let A := noisePrecision b (Real.sqrt (1-t^2))
  let B := outerPrecision t (Real.sqrt (1-t^2)) a b
  have hA : 0 < A := noisePrecision_pos hb _
  have hB : 0 < B := outerPrecision_pos t _ a b ha hb
  have hD := determinant_positive t a b ht ha hb
  have hAB : 4*A*B=determinant t a b := precisions_product t a b ht hb
  have hp : (Real.sqrt (2*Real.pi))⁻¹^2=1/(2*Real.pi) := by
    rw [inv_pow,Real.sq_sqrt (by positivity),one_div]
  rw [hp]
  change 1/(2*Real.pi)*Real.sqrt (Real.pi/A)*Real.sqrt (Real.pi/B)=1/Real.sqrt (determinant t a b)
  have hsA := Real.sq_sqrt (le_of_lt (div_pos Real.pi_pos hA))
  have hsB := Real.sq_sqrt (le_of_lt (div_pos Real.pi_pos hB))
  have hsD := Real.sq_sqrt hD.le
  have hsD0 := Real.sqrt_pos.mpr hD
  have hprod : (1/(2*Real.pi)*Real.sqrt (Real.pi/A)*Real.sqrt (Real.pi/B))^2=1/determinant t a b := by
    rw [mul_pow,mul_pow,hsA,hsB]
    rw [← hAB]
    field_simp
    ring
  have hnon : 0 ≤ 1/(2*Real.pi)*Real.sqrt (Real.pi/A)*Real.sqrt (Real.pi/B) := by positivity
  have hright : (1/Real.sqrt (determinant t a b))^2=1/determinant t a b := by
    rw [div_pow,one_pow,hsD]
  nlinarith [div_pos (by norm_num : (0:ℝ)<1) hsD0]

/-- For `|t| < 1` and nonnegative tilt parameters, the tilted pair mass equals `1 /
√(determinant t a b)`. -/
theorem pair_mass (t a b : ℝ) (ht : |t| < 1) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    pairTiltZero t (Real.sqrt (1-t^2)) a b=1/Real.sqrt (determinant t a b) := by
  rw [pairTiltZero_eval t _ a b hb,prefactor_closed t a b ht ha hb]

/-- For `|t| < 1` and nonnegative tilt parameters, the tilted pair cross moment equals `t /
(determinant t a b * √(determinant t a b))`. -/
theorem pair_cross (t a b : ℝ) (ht : |t| < 1) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    pairTiltCross t (Real.sqrt (1-t^2)) a b=t/(determinant t a b*Real.sqrt (determinant t a b)) := by
  rw [pairTiltCross_eval t _ a b ha hb,prefactor_closed t a b ht ha hb,
    precisions_product t a b ht hb]
  ring
end Qatlib.Papers.RydbergMaxCut26.Rounding.TiltedClosed
