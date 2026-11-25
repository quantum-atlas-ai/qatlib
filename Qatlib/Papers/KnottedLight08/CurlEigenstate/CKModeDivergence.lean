/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.CurlEigenstate.CKModePartials

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The divergence of the regular CK dipole

Both angular polynomials are tangent to coordinate spheres. The
divergence of the quadratic one cancels the derivative of the
radial factor multiplying the constant angular vector.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.CurlEigenstate

open Qatlib.Papers.KnotLight13.TorusFamily (Spacetime coordinateValue cartesianDivergence)

/-- The cubic radial factor differentiates to the regular quintic
factor times the radial argument, including at zero. -/
theorem deriv_ckRadialThree_eq_mul_five (u : ℝ) :
    deriv ckRadialThree u = u * ckRadialFive u := by
  rw [(hasDerivAt_ckRadialThree u).deriv]
  by_cases hu : u = 0
  · simp [hu]
  · rw [ckRadialFive, ite_eq_right hu]
    field_simp [hu]

/-- The three diagonal derivatives of the regular CK dipole sum to zero. -/
theorem sum_hopfDipolePartial_diagonal_eq_zero (k : ℝ) (s : Spacetime) :
    hopfDipolePartial k s 0 0 + hopfDipolePartial k s 1 1 + hopfDipolePartial k s 2 2 = 0 := by
  by_cases hr : ckRadius s.1 s.2.1 s.2.2.1 = 0
  · rcases s with ⟨x, y, z, t⟩
    obtain ⟨rfl, rfl, rfl⟩ := ckRadius_zero_coords hr
    simp [hopfDipolePartial, ckRadius, ckAngular, ckCurlAngular, ckAngularD, ckCurlAngularD]
  · have hd (q : ℝ) :
        deriv ckRadialThree (k * ckRadius s.1 s.2.1 s.2.2.1) *
            (k * (q / ckRadius s.1 s.2.1 s.2.2.1)) =
          k ^ 2 * q * ckRadialFive (k * ckRadius s.1 s.2.1 s.2.2.1) := by
      rw [deriv_ckRadialThree_eq_mul_five]
      field_simp [hr]
    simp only [hopfDipolePartial, hd]
    simp [coordinateValue, Fin.castSucc, Fin.castAdd, ckAngular, ckCurlAngular, ckAngularD,
      ckCurlAngularD, ckConstantCurl]
    ring

/-- The regular CK dipole is divergence free at every spatial
point, including the origin and zero frequency. -/
theorem cartesianDivergence_hopfDipoleMode (k : ℝ) (s : Spacetime) :
    cartesianDivergence (fun p => hopfDipoleMode k p.1 p.2.1 p.2.2.1) s = 0 := by
  have hx := spaceTimePartial_hopfDipoleMode k s 0 0
  have hy := spaceTimePartial_hopfDipoleMode k s 1 1
  have hz := spaceTimePartial_hopfDipoleMode k s 2 2
  simp only [show (0 : Fin 3).castSucc = 0 by decide,
    show (1 : Fin 3).castSucc = 1 by decide, show (2 : Fin 3).castSucc = 2 by decide] at hx hy hz
  simpa only [cartesianDivergence, hx, hy, hz] using sum_hopfDipolePartial_diagonal_eq_zero k s

end Qatlib.Papers.KnottedLight08.CurlEigenstate
