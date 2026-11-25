/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.RationalTransport

/-! Regression consumers for the Poynting-flow transport kernel of the
rational Bateman field. The origin is a fully division-free witness: the
field evaluates to `(-4, 4i, 0)`, so `E = (-4, 0, 0)`, `B = (0, 4, 0)`,
the energy density is `16` and the normalized Poynting flow is
`v = (0, 0, -1)`; both freezing relations are instantiated there, and the
witness point (1, 2, 3, 4) instantiates the unconditional null invariants.
The flow, the ODE-level line preservation and the topological invariance
statement of the paper remain open and are not claimed. -/

@[expose] public section
set_option autoImplicit false

open Qatlib.Papers.KnotLight13.TorusFamily (radialAux pairDenominator)
open Qatlib.Papers.KnottedLight08.HopfField (cross3 dot3 squaredLength)
open Qatlib.Papers.KnotLight13.TorusFamily

/-- The first field component at the origin evaluates to `-4`. -/
private theorem fieldOrigin_zero : rationalField 0 0 0 0 0 = ((-4 : ℂ)) := by
  have hc : cross3 (alphaGradientNumerators 0 0 0 0) (betaGradientNumerators 0 0 0 0) 0
      = ((-4 : ℂ)) := by
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
  have hw : complexDenominator 0 0 0 0 ^ 4 = 1 := by
    norm_num [complexDenominator, radialAux]
  rw [rationalField_eq_cross_div, hc, hw, div_one]

/-- The second field component at the origin evaluates to `4i`. -/
private theorem fieldOrigin_one : rationalField 0 0 0 0 1 = Complex.I * 4 := by
  have hc : cross3 (alphaGradientNumerators 0 0 0 0) (betaGradientNumerators 0 0 0 0) 1
      = Complex.I * 4 := by
    apply Complex.ext
    · simp [cross3, alphaGradientNumerators, betaGradientNumerators,
        alphaXNumerator, alphaYNumerator, alphaZNumerator, betaXNumerator,
        betaYNumerator, betaZNumerator, alphaCommonFactor, betaReducedNumerator,
        complexDenominator, radialAux, Complex.mul_re, Complex.mul_im]
    · simp [cross3, alphaGradientNumerators, betaGradientNumerators,
        alphaXNumerator, alphaYNumerator, alphaZNumerator, betaXNumerator,
        betaYNumerator, betaZNumerator, alphaCommonFactor, betaReducedNumerator,
        complexDenominator, radialAux, Complex.mul_re, Complex.mul_im]
      norm_num
  have hw : complexDenominator 0 0 0 0 ^ 4 = 1 := by
    norm_num [complexDenominator, radialAux]
  rw [rationalField_eq_cross_div, hc, hw, div_one]

set_option linter.unusedSimpArgs false in
/-- The third field component at the origin vanishes. -/
private theorem fieldOrigin_two : rationalField 0 0 0 0 2 = 0 := by
  have hc : cross3 (alphaGradientNumerators 0 0 0 0) (betaGradientNumerators 0 0 0 0) 2
      = 0 := by
    apply Complex.ext <;>
      simp [cross3, alphaGradientNumerators, betaGradientNumerators,
        alphaXNumerator, alphaYNumerator, alphaZNumerator, betaXNumerator,
        betaYNumerator, betaZNumerator, alphaCommonFactor, betaReducedNumerator,
        complexDenominator, radialAux, Complex.mul_re, Complex.mul_im]
  have hw : complexDenominator 0 0 0 0 ^ 4 = 1 := by
    norm_num [complexDenominator, radialAux]
  rw [rationalField_eq_cross_div, hc, hw, div_one]

-- The electric and magnetic parts at the origin: `E = (-4, 0, 0)`,
-- `B = (0, 4, 0)`, the energy density is `16`, and the normalized Poynting
-- flow is `v = (0, 0, -1)`.
example : cross3 (poyntingFlow 0 0 0 0) (magneticField 0 0 0 0) =
    (fun j => -(electricField 0 0 0 0 j)) ∧
    cross3 (poyntingFlow 0 0 0 0) (electricField 0 0 0 0) =
      magneticField 0 0 0 0 := by
  have hE0 : electricField 0 0 0 0 0 = -4 := by
    show (rationalField 0 0 0 0 0).re = -4
    rw [fieldOrigin_zero]
    rfl
  have hE1 : electricField 0 0 0 0 1 = 0 := by
    show (rationalField 0 0 0 0 1).re = 0
    rw [fieldOrigin_one]
    norm_num
  have hE2 : electricField 0 0 0 0 2 = 0 := by
    show (rationalField 0 0 0 0 2).re = 0
    rw [fieldOrigin_two]
    rfl
  have hB0 : magneticField 0 0 0 0 0 = 0 := by
    show (rationalField 0 0 0 0 0).im = 0
    rw [fieldOrigin_zero]
    norm_num
  have hB1 : magneticField 0 0 0 0 1 = 4 := by
    show (rationalField 0 0 0 0 1).im = 4
    rw [fieldOrigin_one]
    norm_num
  have hB2 : magneticField 0 0 0 0 2 = 0 := by
    show (rationalField 0 0 0 0 2).im = 0
    rw [fieldOrigin_two]
    rfl
  have hL : squaredLength (electricField 0 0 0 0) = 16 := by
    show electricField 0 0 0 0 0 * electricField 0 0 0 0 0 +
        electricField 0 0 0 0 1 * electricField 0 0 0 0 1 +
        electricField 0 0 0 0 2 * electricField 0 0 0 0 2 = 16
    rw [hE0, hE1, hE2]
    norm_num
  have hv : poyntingFlow 0 0 0 0 2 = -1 := by
    show (electricField 0 0 0 0 0 * magneticField 0 0 0 0 1 -
          electricField 0 0 0 0 1 * magneticField 0 0 0 0 0) /
        (electricField 0 0 0 0 0 * electricField 0 0 0 0 0 +
          electricField 0 0 0 0 1 * electricField 0 0 0 0 1 +
          electricField 0 0 0 0 2 * electricField 0 0 0 0 2) = -1
    rw [hE0, hE1, hE2, hB0, hB1]
    norm_num
  exact ⟨poyntingFlow_cross_magnetic 0 0 0 0 (by rw [hL]; norm_num),
    poyntingFlow_cross_electric 0 0 0 0 (by rw [hL]; norm_num)⟩

-- The unconditional null invariants at the nondegenerate witness point.
example : squaredLength (magneticField 1 2 3 4) = squaredLength (electricField 1 2 3 4) ∧
    dot3 (electricField 1 2 3 4) (magneticField 1 2 3 4) = 0 :=
  poyntingFlow_null_invariants 1 2 3 4
