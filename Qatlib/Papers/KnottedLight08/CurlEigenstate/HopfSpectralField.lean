/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.CurlEigenstate.HopfSincKernel
public import Qatlib.Papers.KnottedLight08.HopfField.RanadaBateman

import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The Hopf field from the time-dependent spectral kernel

The time-phased radial Laplace–sine integral in `HopfTimeKernel`
gives the spacetime kernel `((1 + it)^2 + x^2 + y^2 + z^2)⁻¹`.
Its second directional derivatives in two orthogonal complex null
directions give the three components of the Rañada field in the
library's convention.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.CurlEigenstate

open Qatlib.Papers.KnottedLight08.HopfField (ranadaField ranadaField_eq_bateman)
open Qatlib.Papers.KnotLight13.TorusFamily
  (complexDenominator complex_denominator_ne_zero alphaCommonFactor
    betaReducedNumerator spinorField rationalField_eq_spinorField)
open Qatlib.Papers.KnotLight13.TorusFamily (radialAux)
open scoped ComplexConjugate Topology

/-- The reciprocal denominator of the time-phased radial kernel pulled back
to the line in direction `a(∂ₓ + i∂ᵧ) + b(∂ₜ - ∂_z)`. -/
noncomputable def hopfKernelNullSection (x y z t : ℝ) (a b s : ℂ) : ℂ :=
  ((1 + Complex.I * ((t : ℂ) + b * s)) ^ 2 + ((x : ℂ) + a * s) ^ 2 +
    ((y : ℂ) + Complex.I * a * s) ^ 2 + ((z : ℂ) - b * s) ^ 2)⁻¹

/-- The denominator of the time-phased integral coincides with the
common Bateman denominator at the Euclidean spatial radius. -/
theorem hopf_time_denominator_eq (x y z t : ℝ) :
    (1 + Complex.I * (t : ℂ)) ^ 2 +
        (Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) : ℂ) ^ 2 =
      complexDenominator x y z t := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
  unfold complexDenominator radialAux
  push_cast
  linear_combination (t : ℂ) ^ 2 * Complex.I_mul_I

/-- The two complex null directions annul the quadratic part of the
denominator along the line. -/
theorem hopfKernelNullSection_eq_affine (x y z t : ℝ) (a b s : ℂ) :
    hopfKernelNullSection x y z t a b s =
      (complexDenominator x y z t +
        (2 * ((x : ℂ) + Complex.I * (y : ℂ)) * a +
          2 * Complex.I * (1 + Complex.I * ((t + z : ℝ) : ℂ)) * b) * s)⁻¹ := by
  unfold hopfKernelNullSection complexDenominator radialAux
  congr 1
  push_cast
  linear_combination (((a ^ 2 + b ^ 2) * s ^ 2 - 2 * (z : ℂ) * b * s) +
    (t : ℂ) ^ 2) * Complex.I_mul_I

/-- At the base point the holomorphic null section equals the radial
spectral integral, including at the spatial origin. -/
theorem hopfKernelNullSection_zero_eq_integral (x y z t : ℝ) (a b : ℂ) :
    let r := Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2)
    hopfKernelNullSection x y z t a b 0 =
      ∫ k in Set.Ioi (0 : ℝ), Complex.exp (-(1 + Complex.I * (t : ℂ)) * (k : ℂ)) *
        ((k * Real.sinc (r * k) : ℝ) : ℂ) := by
  dsimp only
  rw [integral_hopf_time_radial, hopf_time_denominator_eq, hopfKernelNullSection_eq_affine,
    mul_zero, add_zero, one_div]

/-- The second derivative of an affine reciprocal at its regular base point. -/
private theorem second_deriv_affine_inv (c m : ℂ) (hc : c ≠ 0) :
    deriv (deriv (fun s : ℂ => (c + m * s)⁻¹)) 0 = 2 * m ^ 2 / c ^ 3 := by
  have hl (s : ℂ) : HasDerivAt (fun u : ℂ => c + m * u) m s := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id s).const_mul m).const_add c
  have hne : (fun s : ℂ => c + m * s) 0 ≠ 0 := by simpa using hc
  have hnear := (hl 0).continuousAt.eventually_ne hne
  have he : (deriv (fun s : ℂ => (c + m * s)⁻¹)) =ᶠ[𝓝 (0 : ℂ)]
      (fun s : ℂ => -m / (c + m * s) ^ 2) := by
    filter_upwards [hnear] with s hs
    exact ((hl s).fun_inv hs).deriv
  have hd : HasDerivAt (fun s : ℂ => -m / (c + m * s) ^ 2) (2 * m ^ 2 / c ^ 3) 0 := by
    refine ((hasDerivAt_const (0 : ℂ) (-m)).fun_div ((hl 0).pow 2) (pow_ne_zero _ hne)).congr_deriv ?_
    simp only [Pi.pow_apply, mul_zero, add_zero, zero_mul, zero_sub]
    field_simp [hc]
    ring
  exact (hd.congr_of_eventuallyEq he).deriv

/-- The second derivative of the pulse kernel in a complex null direction
depends quadratically on that direction's affine slope. -/
theorem second_deriv_hopfKernelNullSection (x y z t : ℝ) (a b : ℂ) :
    deriv (deriv (hopfKernelNullSection x y z t a b)) 0 =
      8 * (((x : ℂ) + Complex.I * (y : ℂ)) * a +
        Complex.I * (1 + Complex.I * ((t + z : ℝ) : ℂ)) * b) ^ 2 /
        complexDenominator x y z t ^ 3 := by
  rw [show hopfKernelNullSection x y z t a b = fun s =>
    (complexDenominator x y z t + (2 * ((x : ℂ) + Complex.I * (y : ℂ)) * a +
      2 * Complex.I * (1 + Complex.I * ((t + z : ℝ) : ℂ)) * b) * s)⁻¹ from
    funext (hopfKernelNullSection_eq_affine x y z t a b)]
  rw [second_deriv_affine_inv _ _ (complex_denominator_ne_zero x y z t)]
  ring

/-- All spacetime components of the Rañada field are second derivatives
of the time-phased radial kernel. The mixed derivative is expressed by
polarization of the two null directions. -/
theorem ranadaField_eq_hopf_null_secondDerivatives (x y z t : ℝ) (j : Fin 3) :
    let D := fun a b => deriv (deriv (hopfKernelNullSection x y z t a b)) 0
    ranadaField x y z t j =
      (Complex.I / (4 * (Real.pi : ℂ))) *
        ![D 0 1 - D 1 0, Complex.I * (D 0 1 + D 1 0), D 1 1 - D 1 0 - D 0 1] j := by
  let w := complexDenominator x y z t
  let g : ℂ := 1 + Complex.I * ((t + z : ℝ) : ℂ)
  let h : ℂ := (x : ℂ) + Complex.I * (y : ℂ)
  have hw : conj (complexDenominator x y z (-t)) = w := by
    simp only [w, complexDenominator, radialAux, map_add, map_mul, Complex.conj_ofReal,
      Complex.conj_I]
    push_cast
    ring
  have hg : conj (alphaCommonFactor z (-t)) = g := by
    simp only [alphaCommonFactor, g, map_add, map_one, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hh : conj (betaReducedNumerator x y) = h := by
    simp only [betaReducedNumerator, h, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  let S : Fin 3 → ℂ := ![-(g ^ 2 + h ^ 2), -Complex.I * (g ^ 2 - h ^ 2), 2 * Complex.I * g * h]
  have hS : conj (spinorField (alphaCommonFactor z (-t)) (betaReducedNumerator x y) j) = S j := by
    fin_cases j <;> simp [S, spinorField, hg, hh, map_ofNat]
  let N := fun a b : ℂ => 8 * (h * a + Complex.I * g * b) ^ 2 / w ^ 3
  have hdiff : (8 / w ^ 3) * S j =
      ![N 0 1 - N 1 0, Complex.I * (N 0 1 + N 1 0), N 1 1 - N 1 0 - N 0 1] j := by
    fin_cases j
    · simp [S, N, mul_pow, Complex.I_sq]
      ring
    · simp [S, N, mul_pow, Complex.I_sq]
      ring
    · simp [S, N, mul_pow, Complex.I_sq]
      linear_combination -(8 * w⁻¹ ^ 3 * g ^ 2) * Complex.I_mul_I
  dsimp only
  rw [ranadaField_eq_bateman, rationalField_eq_spinorField, map_mul, map_div₀, map_pow, hw, hS]
  simp only [map_ofNat, second_deriv_hopfKernelNullSection]
  have hw₀ : w ≠ 0 := complex_denominator_ne_zero x y z t
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hfactor : (Complex.I / (2 * (Real.pi : ℂ))) * (4 / w ^ 3) =
      (Complex.I / (4 * (Real.pi : ℂ))) * (8 / w ^ 3) := by
    field_simp [hw₀, hπ]
    norm_num
  calc
    _ = ((Complex.I / (2 * (Real.pi : ℂ))) * (4 / w ^ 3)) * S j := (mul_assoc _ _ _).symm
    _ = ((Complex.I / (4 * (Real.pi : ℂ))) * (8 / w ^ 3)) * S j := by rw [hfactor]
    _ = (Complex.I / (4 * (Real.pi : ℂ))) * ((8 / w ^ 3) * S j) := mul_assoc _ _ _
    _ = _ := congrArg (fun v => (Complex.I / (4 * (Real.pi : ℂ))) * v) hdiff

end Qatlib.Papers.KnottedLight08.CurlEigenstate
