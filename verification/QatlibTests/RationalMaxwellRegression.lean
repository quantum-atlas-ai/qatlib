/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.RationalMaxwell

/-! Regression consumers for the source-free Maxwell property of the rational
Bateman field. The witness point (1, 2, 3, 4) is nondegenerate; the second
cross-numerator partial and the third cross numerator entry are evaluated there
against independently computed values, and the Maxwell and divergence theorems
are instantiated componentwise. -/

@[expose] public section
set_option autoImplicit false

open Qatlib.Papers.KnottedLight08.HopfField
open Qatlib.Papers.KnotLight13.TorusFamily
open Qatlib.Papers.KnotLight13.TorusFamily

-- The curl equals i times the time derivative, in every component.
example (j : Fin 3) :
    fieldCurl 1 2 3 4 j = Complex.I * fieldTimeDeriv 1 2 3 4 j :=
  maxwell_rational_field 1 2 3 4 j

-- The field is divergence-free at the witness point.
example :
    deriv (fun x' => rationalField x' 2 3 4 0) 1 +
      deriv (fun y' => rationalField 1 y' 3 4 1) 2 +
      deriv (fun z' => rationalField 1 2 z' 4 2) 3 = 0 :=
  rational_field_divergence_free 1 2 3 4

-- The y partial of the third field entry has the stated exact rational value.
example :
    deriv (fun y' => rationalField 1 y' 3 4 2) 2 =
      ((0 * betaYNumerator 1 2 3 4 +
          alphaXNumerator 1 2 3 4 * (-(4 * betaReducedNumerator 1 2)) -
          (4 * alphaCommonFactor 3 4 * betaXNumerator 1 2 3 4 +
            alphaYNumerator 1 2 3 4 *
              (4 * ((2 : ℝ) : ℂ) + 4 * Complex.I * ((1 : ℝ) : ℂ)))) *
        complexDenominator 1 2 3 4 -
        4 * ((2 * 2 : ℝ) : ℂ) *
          cross3 (alphaGradientNumerators 1 2 3 4) (betaGradientNumerators 1 2 3 4) 2) /
        complexDenominator 1 2 3 4 ^ 5 :=
  (hasDerivAt_rationalField_y_two 1 2 3 4).deriv

-- The third cross numerator entry at the witness point evaluates explicitly.
example :
    cross3 (alphaGradientNumerators 1 2 3 4) (betaGradientNumerators 1 2 3 4) 2 =
      ((200 : ℂ) - Complex.I * 40) := by
  apply Complex.ext
  · simp [cross3, alphaGradientNumerators, betaGradientNumerators,
      alphaXNumerator, alphaYNumerator, alphaZNumerator, betaXNumerator,
      betaYNumerator, betaZNumerator, alphaCommonFactor, betaReducedNumerator,
      complexDenominator, radialAux, Complex.mul_re, Complex.mul_im]
    norm_num
  · simp [cross3, alphaGradientNumerators, betaGradientNumerators,
      alphaXNumerator, alphaYNumerator, alphaZNumerator, betaXNumerator,
      betaYNumerator, betaZNumerator, alphaCommonFactor, betaReducedNumerator,
      complexDenominator, radialAux, Complex.mul_re, Complex.mul_im]
    norm_num

-- Its y partial numerator evaluates against the independently computed value.
example :
    (0 * betaYNumerator 1 2 3 4 +
      alphaXNumerator 1 2 3 4 * (-(4 * betaReducedNumerator 1 2)) -
      (4 * alphaCommonFactor 3 4 * betaXNumerator 1 2 3 4 +
        alphaYNumerator 1 2 3 4 * (4 * ((2 : ℝ) : ℂ) +
          4 * Complex.I * ((1 : ℝ) : ℂ)))) = ((40 : ℂ) - Complex.I * 152) := by
  apply Complex.ext
  · simp [alphaXNumerator, alphaYNumerator, betaXNumerator, betaYNumerator,
      alphaCommonFactor, betaReducedNumerator, complexDenominator, radialAux,
      Complex.mul_re, Complex.mul_im]
    norm_num
  · simp [alphaXNumerator, alphaYNumerator, betaXNumerator, betaYNumerator,
      alphaCommonFactor, betaReducedNumerator, complexDenominator, radialAux,
      Complex.mul_re, Complex.mul_im]
    norm_num
