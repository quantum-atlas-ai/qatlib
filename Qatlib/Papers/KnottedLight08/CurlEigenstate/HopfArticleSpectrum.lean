/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.CurlEigenstate.HopfDipoleExpansion
public import Qatlib.Papers.KnottedLight08.HopfField.RanadaBateman

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Article normalization of the Hopf potential spectrum

Equation (4) of Irvine and Bouwmeester gives the positive-frequency
potential density, followed by its complex conjugate. With the
supplement's TE and TM modes, its positive curl eigenvalue is
the frequency. The positive-frequency contribution to the complex
field `E + iB` is obtained by the multiplier `2ik`.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.CurlEigenstate

open MeasureTheory Set
open Qatlib.Papers.KnottedLight08.HopfField (ranadaField)

/-- The published prefactor and the Cartesian angular normalization
combine to give the factor `1/(2π)`. -/
private theorem hopfPotentialNormalization :
    Real.sqrt (4 / (3 * Real.pi)) * Real.sqrt (3 / (16 * Real.pi)) = 1 / (2 * Real.pi) := by
  rw [← Real.sqrt_mul (by positivity : 0 ≤ 4 / (3 * Real.pi))]
  have h : 4 / (3 * Real.pi) * (3 / (16 * Real.pi)) = (1 / (2 * Real.pi)) ^ 2 := by
    field_simp [Real.pi_ne_zero]
    ring
  rw [h, Real.sqrt_sq_eq_abs, abs_of_pos (by positivity)]

/-- The positive-frequency integrand appearing in the published
vector potential, including the coefficient in equation (4). -/
noncomputable def hopfArticlePotential (k x y z t : ℝ) (j : Fin 3) : ℂ :=
  (Real.sqrt (4 / (3 * Real.pi)) : ℂ) * (k : ℂ) ^ 3 *
    Complex.exp (-(1 + Complex.I * (t : ℂ)) * (k : ℂ)) *
    (ckTEMode k (x, y, z, 0) j - Complex.I * ckTMMode k (x, y, z, 0) j)

/-- Away from the spatial origin, the article's potential integrand is the
actual positive CK mode times `i e^{-k-ikt}/(2π k)`. -/
theorem hopfArticlePotential_eq_dipole {k x y z : ℝ} (hk : k ≠ 0)
    (hr : ckRadius x y z ≠ 0) (t : ℝ) (j : Fin 3) :
    hopfArticlePotential k x y z t j =
      Complex.I / (2 * (Real.pi : ℂ)) *
        (Complex.exp (-(1 + Complex.I * (t : ℂ)) * (k : ℂ)) * hopfDipoleMode k x y z j) / (k : ℂ) := by
  let C : ℂ := (Real.sqrt (4 / (3 * Real.pi)) : ℂ)
  let c : ℂ := (Real.sqrt (3 / (16 * Real.pi)) : ℂ)
  let E : ℂ := Complex.exp (-(1 + Complex.I * (t : ℂ)) * (k : ℂ))
  have hscale : C * c = 1 / (2 * (Real.pi : ℂ)) := by
    have h := congrArg Complex.ofReal hopfPotentialNormalization
    push_cast at h
    exact h
  have hkC : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  rw [hopfDipoleMode, ite_eq_right hr]
  simp only [hopfArticlePotential, ckTEMode, ckTMMode, ckDipoleScale, ckBeltramiPlus]
  change C * (k : ℂ) ^ 3 * E *
      (Complex.I * (c / (k : ℂ) ^ 3) * ckMultipoleField k (x, y, z, 0) j -
        Complex.I * (-(c / (k : ℂ) ^ 3 / (k : ℂ)) * ckCurlMultipoleField k (x, y, z, 0) j)) =
    _
  calc
    _ = (C * c) * Complex.I *
        (E * ((k : ℂ) * ckMultipoleField k (x, y, z, 0) j + ckCurlMultipoleField k (x, y, z, 0) j)) /
          (k : ℂ) := by
      field_simp [hkC]
      ring
    _ = _ := by rw [hscale]; ring

/-- Applying the complex field multiplier to each positive potential mode
and integrating recovers the library field with the article normalization
`-2`, for all times and points off the spatial origin. -/
theorem integral_hopfArticleMaxwell {x y z : ℝ} (hr : ckRadius x y z ≠ 0) (t : ℝ) (j : Fin 3) :
    let W := fun k : ℝ => (2 * Complex.I * (k : ℂ)) * hopfArticlePotential k x y z t j
    IntegrableOn W (Ioi 0) ∧ (∫ k in Ioi (0 : ℝ), W k) = -2 * ranadaField x y z t j := by
  let U := fun k : ℝ => Complex.exp (-(1 + Complex.I * (t : ℂ)) * (k : ℂ)) * hopfDipoleMode k x y z j
  let W := fun k : ℝ => (2 * Complex.I * (k : ℂ)) * hopfArticlePotential k x y z t j
  obtain ⟨hi, h⟩ := ranadaField_eq_hopf_dipole_superposition x y z t j
  have hW (k : ℝ) (hk : k ∈ Ioi (0 : ℝ)) : (-1 / (Real.pi : ℂ)) * U k = W k := by
    have hkC : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk.ne'
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hI : 2 * Complex.I * (Complex.I / (2 * (Real.pi : ℂ))) = -1 / (Real.pi : ℂ) := by
      field_simp [hπ]
      linear_combination Complex.I_mul_I
    dsimp only [U, W]
    rw [hopfArticlePotential_eq_dipole hk.ne' hr, ← hI]
    field_simp [hkC, hπ]
  change IntegrableOn W (Ioi 0) ∧ (∫ k in Ioi (0 : ℝ), W k) = _
  have hUi : IntegrableOn (fun k => (-1 / (Real.pi : ℂ)) * U k) (Ioi 0) :=
    hi.const_mul _
  change ranadaField x y z t j = (1 / (2 * (Real.pi : ℂ))) * ∫ k in Ioi (0 : ℝ), U k at h
  refine ⟨hUi.congr_fun hW measurableSet_Ioi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi hW, integral_const_mul, h]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hπ]

end Qatlib.Papers.KnottedLight08.CurlEigenstate
