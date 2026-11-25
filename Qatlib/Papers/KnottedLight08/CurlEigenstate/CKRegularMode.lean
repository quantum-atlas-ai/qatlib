/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.CurlEigenstate.CKRegularRadial
public import Qatlib.Papers.KnottedLight08.CurlEigenstate.HopfDipoleExpansion

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Continuous dipole curl modes at the spatial origin

All apparent negative powers of the radius in the CK dipole can
be absorbed into the two regular radial factors. The remaining
Cartesian angular factors are polynomials. This identifies the
origin values in the reconstructed field with the continuous
extensions of its actual spectral modes.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.CurlEigenstate

/-- Vanishing radius forces all three Cartesian coordinates to vanish. -/
theorem ckRadius_zero_coords {x y z : ℝ} (h : ckRadius x y z = 0) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  have hs : x ^ 2 + y ^ 2 + z ^ 2 = 0 :=
    (Real.sqrt_eq_zero (by positivity)).1 h
  refine ⟨?_, ?_, ?_⟩
  · by_contra hx
    exact pow_ne_zero 2 hx (by nlinarith [sq_nonneg y, sq_nonneg z])
  · by_contra hy
    exact pow_ne_zero 2 hy (by nlinarith [sq_nonneg x, sq_nonneg z])
  · by_contra hz
    exact pow_ne_zero 2 hz (by nlinarith [sq_nonneg x, sq_nonneg y])

/-- The CK mode is a sum of Cartesian polynomials with globally
continuous radial coefficients, including the origin and zero frequency. -/
theorem hopfDipoleMode_eq_regular (k x y z : ℝ) (j : Fin 3) :
    let u := k * ckRadius x y z
    hopfDipoleMode k x y z j =
      ((k ^ 4 * ckRadialThree u : ℝ) : ℂ) * ckAngular x y z j +
      ((k ^ 5 * ckRadialFive u : ℝ) : ℂ) * ckCurlAngular x y z j +
      ((k ^ 3 * ckRadialThree u : ℝ) : ℂ) * ckConstantCurl j := by
  let r := ckRadius x y z
  change hopfDipoleMode k x y z j =
    ((k ^ 4 * ckRadialThree (k * r) : ℝ) : ℂ) * ckAngular x y z j +
    ((k ^ 5 * ckRadialFive (k * r) : ℝ) : ℂ) * ckCurlAngular x y z j +
    ((k ^ 3 * ckRadialThree (k * r) : ℝ) : ℂ) * ckConstantCurl j
  by_cases hr : r = 0
  · obtain ⟨rfl, rfl, rfl⟩ := ckRadius_zero_coords hr
    have h₃ : ckRadialThree (0 : ℝ) = 1 / 3 := by simp [ckRadialThree]
    have h₅ : ckRadialFive (0 : ℝ) = -(1 / 15) := by simp [ckRadialFive]
    have hA : ckAngular 0 0 0 j = 0 := by
      fin_cases j <;> simp [ckAngular]
    have hB : ckCurlAngular 0 0 0 j = 0 := by
      fin_cases j <;> simp [ckCurlAngular]
    rw [hopfDipoleMode, ite_eq_left hr, hr, mul_zero, h₃, h₅, hA, hB]
    simp only [mul_zero, zero_add]
    push_cast
    ring
  · rw [hopfDipoleMode, ite_eq_right hr]
    by_cases hk : k = 0
    · subst k
      simp [ckBeltramiPlus, ckMultipoleField, ckCurlMultipoleField, ckRadialComb, ckKernel]
    · have hk' : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
      have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
      have hkr : k * r ≠ 0 := mul_ne_zero hk hr
      simp only [ckRadialThree, ckRadialFive, ite_eq_right hkr, ckBeltramiPlus, ckMultipoleField,
        ckCurlMultipoleField, ckRadialComb]
      change (k : ℂ) * ((ckKernel (k * r) : ℂ) * ckAngular x y z j / ((r ^ 3 : ℝ) : ℂ)) +
        (((k ^ 2 * r ^ 2 * Real.sin (k * r) - 3 * ckKernel (k * r) : ℝ) : ℂ) *
          ckCurlAngular x y z j / ((r ^ 5 : ℝ) : ℂ) +
          (ckKernel (k * r) : ℂ) * ckConstantCurl j / ((r ^ 3 : ℝ) : ℂ)) = _
      push_cast
      field_simp [hk', hr']
      ring

/-- At every fixed frequency the extended CK mode is continuous in all
Cartesian spatial coordinates. -/
theorem continuous_hopfDipoleMode (k : ℝ) (j : Fin 3) :
    Continuous (fun p : ℝ × ℝ × ℝ => hopfDipoleMode k p.1 p.2.1 p.2.2 j) := by
  let r := fun p : ℝ × ℝ × ℝ => ckRadius p.1 p.2.1 p.2.2
  have hr : Continuous r := by dsimp only [r, ckRadius]; fun_prop
  have h₃ : Continuous (fun p => ckRadialThree (k * r p)) :=
    continuous_ckRadialThree.comp (continuous_const.mul hr)
  have h₅ : Continuous (fun p => ckRadialFive (k * r p)) :=
    continuous_ckRadialFive.comp (continuous_const.mul hr)
  have hA : Continuous (fun p : ℝ × ℝ × ℝ => ckAngular p.1 p.2.1 p.2.2 j) := by
    fin_cases j <;> simp only [ckAngular] <;> fun_prop
  have hB : Continuous (fun p : ℝ × ℝ × ℝ => ckCurlAngular p.1 p.2.1 p.2.2 j) := by
    fin_cases j <;> simp only [ckCurlAngular] <;> fun_prop
  simp_rw [hopfDipoleMode_eq_regular]
  change Continuous (fun p =>
    ((k ^ 4 * ckRadialThree (k * r p) : ℝ) : ℂ) * ckAngular p.1 p.2.1 p.2.2 j +
    ((k ^ 5 * ckRadialFive (k * r p) : ℝ) : ℂ) * ckCurlAngular p.1 p.2.1 p.2.2 j +
    ((k ^ 3 * ckRadialThree (k * r p) : ℝ) : ℂ) * ckConstantCurl j)
  exact (((Complex.continuous_ofReal.comp (continuous_const.mul h₃)).mul hA).add
    ((Complex.continuous_ofReal.comp (continuous_const.mul h₅)).mul hB)).add
    ((Complex.continuous_ofReal.comp (continuous_const.mul h₃)).mul continuous_const)

end Qatlib.Papers.KnottedLight08.CurlEigenstate
