/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.HopfField.NullAlgebra
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Ribbon twist of a rotating normal field along the unit circle

[Kedia2018SuperfluidHelicity], Section IV, [DOI](https://doi.org/10.1103/PhysRevFluids.3.104702).
The Seifert-surface (centerline-plus-framing) picture decomposes centerline helicity into
linking, writhe and twist parts. This module exhibits a fully explicit smooth ribbon over the
unit circle — the centerline `circleCurve` with the rotating unit normal
`circleRibbonNormal m` that spins `m` half-turns about the tangent per circuit — and computes
its total ribbon twist `ribbonTwist` exactly as `-m`.

The computation is a rigorous identity for this model ribbon and makes precise that the twist
contribution is a geometric quantity: it equals `-m` for every real `m`, integer or not, so
only integral `m` give topologically distinct framings. The twist correction term in the
paper's Seifert-surface formula is thus genuine geometry, not topology. The CFW/Séifert
decomposition theorem for arbitrary knotted ribbons, existence of Seifert surfaces, and the
singular-core limit relating ribbon twist to vortex-core circulation are not proved here.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.SeifertCWF

open Qatlib.Papers.KnottedLight08.HopfField

/-- The unit circle in the `xy`-plane, parametrized by arc length on `[0, 2π]`. -/
noncomputable def circleCurve (s : ℝ) : Fin 3 → ℝ :=
  ![Real.cos s, Real.sin s, 0]

/-- The ribbon normal over the circle obtained by rotating the outward radial normal
`(cos s, sin s, 0)` through angle `m * s` about the tangent direction: a unit normal field
perpendicular to `circleCurve` that spins at rate `m`. -/
noncomputable def circleRibbonNormal (m s : ℝ) : Fin 3 → ℝ :=
  ![Real.cos (m * s) * Real.cos s, Real.cos (m * s) * Real.sin s, Real.sin (m * s)]

/-- Total ribbon twist: the net rotation of the normal `N` along the closed curve `γ`,
computed as the normalized line integral of `(T × N) · N'` with `T = γ'`. -/
noncomputable def ribbonTwist (γ N : ℝ → (Fin 3 → ℝ)) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ s in (0)..(2 * Real.pi),
    dot3 (cross3 (deriv γ s) (N s)) (deriv N s)

/-- The arc-length parametrized circle has tangent `(-sin s, cos s, 0)`. -/
theorem hasDerivAt_circleCurve (s : ℝ) :
    HasDerivAt circleCurve ![-Real.sin s, Real.cos s, 0] s := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · exact Real.hasDerivAt_cos s
  · exact Real.hasDerivAt_sin s
  · show HasDerivAt (fun _ : ℝ => (0 : ℝ)) (0 : ℝ) s
    exact hasDerivAt_const (c := (0 : ℝ)) (x := s)

/-- The derivative of the unit circle parametrization is the unit tangent. -/
theorem deriv_circleCurve (s : ℝ) :
    deriv circleCurve s = ![-Real.sin s, Real.cos s, 0] :=
  (hasDerivAt_circleCurve s).deriv

/-- The rotating normal differentiates componentwise by the product and chain rules. -/
theorem hasDerivAt_circleRibbonNormal (m s : ℝ) :
    HasDerivAt (circleRibbonNormal m)
      ![-m * Real.sin (m * s) * Real.cos s - Real.cos (m * s) * Real.sin s,
        -m * Real.sin (m * s) * Real.sin s + Real.cos (m * s) * Real.cos s,
        m * Real.cos (m * s)] s := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · show HasDerivAt (fun t => Real.cos (m * t) * Real.cos t)
        (-m * Real.sin (m * s) * Real.cos s - Real.cos (m * s) * Real.sin s) s
    have h0 : HasDerivAt (fun t => Real.cos (m * t)) (-Real.sin (m * s) * m) s :=
      (hasDerivAt_const_mul m).cos
    have h1 : HasDerivAt (fun t => Real.cos t) (-Real.sin s) s := Real.hasDerivAt_cos s
    exact (h0.mul h1).congr_deriv (by ring)
  · show HasDerivAt (fun t => Real.cos (m * t) * Real.sin t)
        (-m * Real.sin (m * s) * Real.sin s + Real.cos (m * s) * Real.cos s) s
    have h0 : HasDerivAt (fun t => Real.cos (m * t)) (-Real.sin (m * s) * m) s :=
      (hasDerivAt_const_mul m).cos
    have h1 : HasDerivAt (fun t => Real.sin t) (Real.cos s) s := Real.hasDerivAt_sin s
    exact (h0.mul h1).congr_deriv (by ring)
  · show HasDerivAt (fun t => Real.sin (m * t)) (m * Real.cos (m * s)) s
    have h0 : HasDerivAt (fun t => Real.sin (m * t)) (Real.cos (m * s) * m) s :=
      (hasDerivAt_const_mul m).sin
    exact h0.congr_deriv (by ring)

/-- The derivative of the ribbon normal combines rotation of the frame and twist. -/
theorem deriv_circleRibbonNormal (m s : ℝ) :
    deriv (circleRibbonNormal m) s =
      ![-m * Real.sin (m * s) * Real.cos s - Real.cos (m * s) * Real.sin s,
        -m * Real.sin (m * s) * Real.sin s + Real.cos (m * s) * Real.cos s,
        m * Real.cos (m * s)] :=
  (hasDerivAt_circleRibbonNormal m s).deriv

/-- The circle ribbon is honest: the normal field is unit length at every point. -/
theorem circleRibbonNormal_self_eq_one (m s : ℝ) :
    dot3 (circleRibbonNormal m s) (circleRibbonNormal m s) = 1 := by
  show (Real.cos (m * s) * Real.cos s) * (Real.cos (m * s) * Real.cos s)
      + (Real.cos (m * s) * Real.sin s) * (Real.cos (m * s) * Real.sin s)
      + Real.sin (m * s) * Real.sin (m * s) = 1
  linear_combination (Real.cos (m * s) ^ 2) * Real.sin_sq_add_cos_sq s
    + Real.sin_sq_add_cos_sq (m * s)

/-- The circle ribbon is honest: the normal field is perpendicular to the tangent at every
point. -/
theorem circleRibbonNormal_orth_tangent (m s : ℝ) :
    dot3 (deriv circleCurve s) (circleRibbonNormal m s) = 0 := by
  rw [deriv_circleCurve]
  show (-Real.sin s) * (Real.cos (m * s) * Real.cos s)
      + Real.cos s * (Real.cos (m * s) * Real.sin s) + (0 : ℝ) * Real.sin (m * s) = 0
  ring

/-- Pointwise twist density of the circle ribbon: the integrand of `ribbonTwist` is the
constant `-m`, the (signed) rotation rate of the normal. -/
theorem twistDensity_circle_eq (m s : ℝ) :
    dot3 (cross3 (deriv circleCurve s) (circleRibbonNormal m s))
        (deriv (circleRibbonNormal m) s) = -m := by
  rw [deriv_circleCurve, deriv_circleRibbonNormal]
  show (Real.cos s * Real.sin (m * s) - (0 : ℝ) * (Real.cos (m * s) * Real.sin s))
        * (-m * Real.sin (m * s) * Real.cos s - Real.cos (m * s) * Real.sin s)
      + ((0 : ℝ) * (Real.cos (m * s) * Real.cos s) - (-Real.sin s) * Real.sin (m * s))
        * (-m * Real.sin (m * s) * Real.sin s + Real.cos (m * s) * Real.cos s)
      + ((-Real.sin s) * (Real.cos (m * s) * Real.sin s)
          - Real.cos s * (Real.cos (m * s) * Real.cos s)) * (m * Real.cos (m * s)) = -m
  linear_combination (-m) * Real.sin_sq_add_cos_sq s
    + (-(m * (Real.sin s ^ 2 + Real.cos s ^ 2))) * Real.sin_sq_add_cos_sq (m * s)

/-- Total ribbon twist of the circle ribbon with rotation rate `m` is exactly `-m`, for every
real `m`: the twist is a geometric quantity, and only integral `m` distinguish framings
topologically. -/
theorem ribbonTwist_circle_eq (m : ℝ) :
    ribbonTwist circleCurve (circleRibbonNormal m) = -m := by
  rw [ribbonTwist, intervalIntegral.integral_congr (fun s _ => twistDensity_circle_eq m s),
    intervalIntegral.integral_const, sub_zero, smul_eq_mul, ← mul_assoc,
    div_mul_cancel₀ _ (mul_ne_zero two_ne_zero Real.pi_ne_zero), one_mul]

end Qatlib.Papers.SuperfluidHel18.SeifertCWF
