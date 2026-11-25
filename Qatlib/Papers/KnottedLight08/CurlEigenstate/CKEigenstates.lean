/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.CurlEigenstate.CKModes

import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Polyrith
import Mathlib.Tactic.Ring

/-!
# Chandrasekhar–Kendall curl eigenstates of the dipole building blocks

[IrvineBouwmeester2008KnottedLight], p. 718 and Supplementary Methods 1,
[DOI](https://doi.org/10.1038/nphys1056).
The second curl of the `l = m = 1` magnetic multipole `f₁(kr) LY₁₁` equals
`k²` times the mode, so the explicit superpositions `k M ± curl M` are
eigenstates of the Cartesian curl operator with eigenvalues `± k`. These are
the Chandrasekhar–Kendall states. Supplementary Methods equations (1)–(2)
give `A^TE = f₁ LY₁₁/(iω)` and `A^TM = curl (f₁ LY₁₁)/k²`. With `ω = k`,
equation (6) holds for the `A^TE ± i A^TM` combinations with eigenvalues
`∓k`. Every such state is force-free
(Beltrami): its cross product with its own curl vanishes.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.CurlEigenstate

open Qatlib.Papers.KnotLight13.TorusFamily
  (Spacetime cartesianCurl cartesianDivergence spaceTimePartial coordinateSection
    coordinateValue)
open Qatlib.Papers.KnottedLight08.HopfField (cross3)

/-! ### Section derivatives of the curl partner -/

/-- The radial combination has the section derivative `-k² c g(kr)` in the
varying coordinate `c`; this identity is where the spherical Bessel
differential equation of `j₁` enters through the closed forms. -/
theorem hasDerivAt_ckRadialComb_x {k x y z : ℝ} (hr : ckRadius x y z ≠ 0) :
    HasDerivAt (fun u => ((ckRadialComb k u y z : ℝ) : ℂ))
      (-((k ^ 2 * x * ckKernel (k * ckRadius x y z)) : ℝ) : ℂ) x := by
  have hR2 : HasDerivAt (fun u => ckRadius u y z ^ 2) (2 * x) x := by
    refine HasDerivAt.congr_deriv ((hasDerivAt_ckRadius_x hr).pow 2) ?_
    field_simp [hr]
    try ring
  have hsin : HasDerivAt (fun u => Real.sin (k * ckRadius u y z))
      (Real.cos (k * ckRadius x y z) * (k * (x / ckRadius x y z))) x :=
    HasDerivAt.congr_deriv ((Real.hasDerivAt_sin _).comp x
      ((hasDerivAt_ckRadius_x hr).const_mul k)) (by
        field_simp [hr])
  have hG : HasDerivAt (fun u => ckKernel (k * ckRadius u y z))
      ((k ^ 2 * x * Real.sin (k * ckRadius x y z))) x := by
    refine HasDerivAt.congr_deriv ((hasDerivAt_ckKernel _).comp x
      ((hasDerivAt_ckRadius_x hr).const_mul k)) ?_
    field_simp [hr]
  have hreal : HasDerivAt (fun u => ckRadialComb k u y z)
      (-(k ^ 2 * x * ckKernel (k * ckRadius x y z))) x := by
    simp only [ckRadialComb]
    refine HasDerivAt.congr_deriv
      (HasDerivAt.fun_sub
        (HasDerivAt.fun_mul
          (HasDerivAt.fun_mul (hasDerivAt_const x (k ^ 2 : ℝ)) hR2) hsin)
        (HasDerivAt.fun_mul (hasDerivAt_const x (3 : ℝ)) hG)) ?_
    field_simp [hr]
    simp only [ckKernel]
    ring
  exact HasDerivAt.congr_deriv hreal.ofReal_comp (by push_cast; ring)


/-- The derivative of the TM radial combination along the `y` section. -/
theorem hasDerivAt_ckRadialComb_y {k x y z : ℝ} (hr : ckRadius x y z ≠ 0) :
    HasDerivAt (fun u => ((ckRadialComb k x u z : ℝ) : ℂ))
      (-((k ^ 2 * y * ckKernel (k * ckRadius x y z)) : ℝ) : ℂ) y := by
  have hR2 : HasDerivAt (fun u => ckRadius x u z ^ 2) (2 * y) y := by
    refine HasDerivAt.congr_deriv ((hasDerivAt_ckRadius_y hr).pow 2) ?_
    field_simp [hr]
    try ring
  have hsin : HasDerivAt (fun u => Real.sin (k * ckRadius x u z))
      (Real.cos (k * ckRadius x y z) * (k * (y / ckRadius x y z))) y :=
    HasDerivAt.congr_deriv ((Real.hasDerivAt_sin _).comp y
      ((hasDerivAt_ckRadius_y hr).const_mul k)) (by
        field_simp [hr])
  have hG : HasDerivAt (fun u => ckKernel (k * ckRadius x u z))
      ((k ^ 2 * y * Real.sin (k * ckRadius x y z))) y := by
    refine HasDerivAt.congr_deriv ((hasDerivAt_ckKernel _).comp y
      ((hasDerivAt_ckRadius_y hr).const_mul k)) ?_
    field_simp [hr]
  have hreal : HasDerivAt (fun u => ckRadialComb k x u z)
      (-(k ^ 2 * y * ckKernel (k * ckRadius x y z))) y := by
    simp only [ckRadialComb]
    refine HasDerivAt.congr_deriv
      (HasDerivAt.fun_sub
        (HasDerivAt.fun_mul
          (HasDerivAt.fun_mul (hasDerivAt_const y (k ^ 2 : ℝ)) hR2) hsin)
        (HasDerivAt.fun_mul (hasDerivAt_const y (3 : ℝ)) hG)) ?_
    field_simp [hr]
    simp only [ckKernel]
    ring
  exact HasDerivAt.congr_deriv hreal.ofReal_comp (by push_cast; ring)

/-- The derivative of the TM radial combination along the `z` section. -/
theorem hasDerivAt_ckRadialComb_z {k x y z : ℝ} (hr : ckRadius x y z ≠ 0) :
    HasDerivAt (fun u => ((ckRadialComb k x y u : ℝ) : ℂ))
      (-((k ^ 2 * z * ckKernel (k * ckRadius x y z)) : ℝ) : ℂ) z := by
  have hR2 : HasDerivAt (fun u => ckRadius x y u ^ 2) (2 * z) z := by
    refine HasDerivAt.congr_deriv ((hasDerivAt_ckRadius_z hr).pow 2) ?_
    field_simp [hr]
    try ring
  have hsin : HasDerivAt (fun u => Real.sin (k * ckRadius x y u))
      (Real.cos (k * ckRadius x y z) * (k * (z / ckRadius x y z))) z :=
    HasDerivAt.congr_deriv ((Real.hasDerivAt_sin _).comp z
      ((hasDerivAt_ckRadius_z hr).const_mul k)) (by
        field_simp [hr])
  have hG : HasDerivAt (fun u => ckKernel (k * ckRadius x y u))
      ((k ^ 2 * z * Real.sin (k * ckRadius x y z))) z := by
    refine HasDerivAt.congr_deriv ((hasDerivAt_ckKernel _).comp z
      ((hasDerivAt_ckRadius_z hr).const_mul k)) ?_
    field_simp [hr]
  have hreal : HasDerivAt (fun u => ckRadialComb k x y u)
      (-(k ^ 2 * z * ckKernel (k * ckRadius x y z))) z := by
    simp only [ckRadialComb]
    refine HasDerivAt.congr_deriv
      (HasDerivAt.fun_sub
        (HasDerivAt.fun_mul
          (HasDerivAt.fun_mul (hasDerivAt_const z (k ^ 2 : ℝ)) hR2) hsin)
        (HasDerivAt.fun_mul (hasDerivAt_const z (3 : ℝ)) hG)) ?_
    field_simp [hr]
    simp only [ckKernel]
    ring
  exact HasDerivAt.congr_deriv hreal.ofReal_comp (by push_cast; ring)

/-- The reciprocal fifth power of the radius along the first coordinate. -/
theorem hasDerivAt_ckRadiusPow5_inv_x {x y z : ℝ} (hr : ckRadius x y z ≠ 0) :
    HasDerivAt (fun u => (((ckRadius u y z ^ 5 : ℝ) : ℂ))⁻¹)
      (-((5 * x : ℝ) : ℂ) / ((ckRadius x y z ^ 7 : ℝ) : ℂ)) x := by
  have h5 : HasDerivAt (fun u => ((ckRadius u y z ^ 5 : ℝ) : ℂ))
      (((5 * x * ckRadius x y z ^ 3) : ℝ) : ℂ) x := by
    refine HasDerivAt.congr_deriv (((hasDerivAt_ckRadius_x hr).pow 5).ofReal_comp) ?_
    rw [Complex.ofReal_inj]
    field_simp [hr]
    ring
  have hne : ((ckRadius x y z ^ 5 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero 5 hr
  refine HasDerivAt.congr_deriv (h5.inv hne) ?_
  have e2 : (((ckRadius x y z ^ 5 : ℝ) : ℂ)) ^ 2 = ((ckRadius x y z ^ 10 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [e2, div_eq_div_iff (by exact_mod_cast pow_ne_zero 10 hr)
    (by exact_mod_cast pow_ne_zero 7 hr)]
  push_cast
  ring

/-- The reciprocal fifth power of the radius along the second coordinate. -/
theorem hasDerivAt_ckRadiusPow5_inv_y {x y z : ℝ} (hr : ckRadius x y z ≠ 0) :
    HasDerivAt (fun u => (((ckRadius x u z ^ 5 : ℝ) : ℂ))⁻¹)
      (-((5 * y : ℝ) : ℂ) / ((ckRadius x y z ^ 7 : ℝ) : ℂ)) y := by
  have h5 : HasDerivAt (fun u => ((ckRadius x u z ^ 5 : ℝ) : ℂ))
      (((5 * y * ckRadius x y z ^ 3) : ℝ) : ℂ) y := by
    refine HasDerivAt.congr_deriv (((hasDerivAt_ckRadius_y hr).pow 5).ofReal_comp) ?_
    rw [Complex.ofReal_inj]
    field_simp [hr]
    ring
  have hne : ((ckRadius x y z ^ 5 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero 5 hr
  refine HasDerivAt.congr_deriv (h5.inv hne) ?_
  have e2 : (((ckRadius x y z ^ 5 : ℝ) : ℂ)) ^ 2 = ((ckRadius x y z ^ 10 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [e2, div_eq_div_iff (by exact_mod_cast pow_ne_zero 10 hr)
    (by exact_mod_cast pow_ne_zero 7 hr)]
  push_cast
  ring

/-- The reciprocal fifth power of the radius along the third coordinate. -/
theorem hasDerivAt_ckRadiusPow5_inv_z {x y z : ℝ} (hr : ckRadius x y z ≠ 0) :
    HasDerivAt (fun u => (((ckRadius x y u ^ 5 : ℝ) : ℂ))⁻¹)
      (-((5 * z : ℝ) : ℂ) / ((ckRadius x y z ^ 7 : ℝ) : ℂ)) z := by
  have h5 : HasDerivAt (fun u => ((ckRadius x y u ^ 5 : ℝ) : ℂ))
      (((5 * z * ckRadius x y z ^ 3) : ℝ) : ℂ) z := by
    refine HasDerivAt.congr_deriv (((hasDerivAt_ckRadius_z hr).pow 5).ofReal_comp) ?_
    rw [Complex.ofReal_inj]
    field_simp [hr]
    ring
  have hne : ((ckRadius x y z ^ 5 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero 5 hr
  refine HasDerivAt.congr_deriv (h5.inv hne) ?_
  have e2 : (((ckRadius x y z ^ 5 : ℝ) : ℂ)) ^ 2 = ((ckRadius x y z ^ 10 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [e2, div_eq_div_iff (by exact_mod_cast pow_ne_zero 10 hr)
    (by exact_mod_cast pow_ne_zero 7 hr)]
  push_cast
  ring


/-! ### Section derivatives of the curl partner field -/

/-- The quadratic angular factor of the curl partner has the componentwise
section derivatives `(-y, 2x+iy, iz)` in the first coordinate. -/
theorem hasDerivAt_curlAngular_x (x y z : ℝ) (j : Fin 3) :
    HasDerivAt (fun u => ckCurlAngular u y z j)
      (![-(y : ℂ), (2 : ℂ) * (x : ℂ) + Complex.I * (y : ℂ),
        Complex.I * (z : ℂ)] j) x := by
  fin_cases j
  · show HasDerivAt (fun u => -(((u : ℝ) : ℂ) * (y : ℂ))
        - Complex.I * ((y : ℂ) ^ 2 + (z : ℂ) ^ 2))
        (-(y : ℂ)) x
    exact HasDerivAt.congr_deriv
      (HasDerivAt.fun_sub (HasDerivAt.neg (HasDerivAt.fun_mul
        (hasDerivAt_id x).ofReal_comp (hasDerivAt_const x ((y : ℂ)))))
        (hasDerivAt_const x (Complex.I * ((y : ℂ) ^ 2 + (z : ℂ) ^ 2)))) (by push_cast; ring)
  · show HasDerivAt (fun u => ((u : ℝ) : ℂ) ^ 2 + (z : ℂ) ^ 2
        + Complex.I * (((u : ℝ) : ℂ) * (y : ℂ)))
        ((2 : ℂ) * (x : ℂ) + Complex.I * (y : ℂ)) x
    exact HasDerivAt.congr_deriv
      (HasDerivAt.fun_add
        (HasDerivAt.fun_add ((hasDerivAt_id x).ofReal_comp.pow 2)
          (hasDerivAt_const x ((z : ℂ) ^ 2)))
        (HasDerivAt.fun_mul (hasDerivAt_const x (Complex.I))
          (HasDerivAt.fun_mul (hasDerivAt_id x).ofReal_comp
            (hasDerivAt_const x ((y : ℂ)))))) (by simp only [id_eq]; push_cast; ring)
  · show HasDerivAt (fun u => Complex.I * (((u : ℝ) : ℂ) * (z : ℂ)) - (y : ℂ) * (z : ℂ))
        (Complex.I * (z : ℂ)) x
    exact HasDerivAt.congr_deriv
      (HasDerivAt.fun_sub (HasDerivAt.fun_mul (hasDerivAt_const x (Complex.I))
          (HasDerivAt.fun_mul (hasDerivAt_id x).ofReal_comp
            (hasDerivAt_const x ((z : ℂ)))))
        (hasDerivAt_const x ((y : ℂ) * (z : ℂ)))) (by push_cast; ring)

/-- The quadratic angular factor has the componentwise section derivatives
`(-x-2iy, ix, -z)` in the second coordinate. -/
theorem hasDerivAt_curlAngular_y (x y z : ℝ) (j : Fin 3) :
    HasDerivAt (fun u => ckCurlAngular x u z j)
      (![-((x : ℂ)) - (2 : ℂ) * Complex.I * (y : ℂ), Complex.I * (x : ℂ),
        -(z : ℂ)] j) y := by
  fin_cases j
  · show HasDerivAt (fun u => -((x : ℂ) * ((u : ℝ) : ℂ))
        - Complex.I * (((u : ℝ) : ℂ) ^ 2 + (z : ℂ) ^ 2))
        (-((x : ℂ)) - (2 : ℂ) * Complex.I * (y : ℂ)) y
    exact HasDerivAt.congr_deriv
      (HasDerivAt.fun_sub (HasDerivAt.neg (HasDerivAt.fun_mul
          (hasDerivAt_const y ((x : ℂ))) (hasDerivAt_id y).ofReal_comp))
        (HasDerivAt.fun_mul (hasDerivAt_const y (Complex.I))
          (HasDerivAt.fun_add ((hasDerivAt_id y).ofReal_comp.pow 2)
            (hasDerivAt_const y ((z : ℂ) ^ 2))))) (by simp only [id_eq]; push_cast; ring)
  · show HasDerivAt (fun u => (x : ℂ) ^ 2 + (z : ℂ) ^ 2
        + Complex.I * ((x : ℂ) * ((u : ℝ) : ℂ)))
        (Complex.I * (x : ℂ)) y
    exact hasDerivAt_const y ((x : ℂ) ^ 2 + (z : ℂ) ^ 2) |>.fun_add
      (HasDerivAt.fun_mul (hasDerivAt_const y (Complex.I))
        (HasDerivAt.fun_mul (hasDerivAt_const y ((x : ℂ)))
          (hasDerivAt_id y).ofReal_comp)) |>.congr_deriv (by simp only [id_eq]; push_cast; ring)
  · show HasDerivAt (fun u => Complex.I * ((x : ℂ) * (z : ℂ)) - ((u : ℝ) : ℂ) * (z : ℂ))
        (-(z : ℂ)) y
    exact HasDerivAt.congr_deriv
      (HasDerivAt.fun_sub (hasDerivAt_const y (Complex.I * ((x : ℂ) * (z : ℂ))))
        (HasDerivAt.fun_mul (hasDerivAt_id y).ofReal_comp
          (hasDerivAt_const y ((z : ℂ))))) (by push_cast; ring)

/-- The quadratic angular factor has the componentwise section derivatives
`(-2iz, 2z, ix-y)` in the third coordinate. -/
theorem hasDerivAt_curlAngular_z (x y z : ℝ) (j : Fin 3) :
    HasDerivAt (fun u => ckCurlAngular x y u j)
      (![-(2 : ℂ) * Complex.I * (z : ℂ), (2 : ℂ) * (z : ℂ),
        Complex.I * (x : ℂ) - (y : ℂ)] j) z := by
  fin_cases j
  · show HasDerivAt (fun u => -((x : ℂ) * (y : ℂ))
        - Complex.I * ((y : ℂ) ^ 2 + ((u : ℝ) : ℂ) ^ 2))
        (-(2 : ℂ) * Complex.I * (z : ℂ)) z
    exact HasDerivAt.congr_deriv
      (HasDerivAt.fun_sub (hasDerivAt_const z (-((x : ℂ) * (y : ℂ))))
        (HasDerivAt.fun_mul (hasDerivAt_const z (Complex.I))
          (HasDerivAt.fun_add (hasDerivAt_const z ((y : ℂ) ^ 2))
            ((hasDerivAt_id z).ofReal_comp.pow 2)))) (by simp only [id_eq]; push_cast; ring)
  · show HasDerivAt (fun u => (x : ℂ) ^ 2 + ((u : ℝ) : ℂ) ^ 2
        + Complex.I * ((x : ℂ) * (y : ℂ)))
        ((2 : ℂ) * (z : ℂ)) z
    exact HasDerivAt.congr_deriv
      (HasDerivAt.fun_add
        (HasDerivAt.fun_add (hasDerivAt_const z ((x : ℂ) ^ 2))
          ((hasDerivAt_id z).ofReal_comp.pow 2))
        (hasDerivAt_const z (Complex.I * ((x : ℂ) * (y : ℂ))))) (by simp only [id_eq]; push_cast; ring)
  · show HasDerivAt (fun u => Complex.I * ((x : ℂ) * ((u : ℝ) : ℂ)) - (y : ℂ) * ((u : ℝ) : ℂ))
        (Complex.I * (x : ℂ) - (y : ℂ)) z
    exact HasDerivAt.congr_deriv
      (HasDerivAt.fun_sub (HasDerivAt.fun_mul (hasDerivAt_const z (Complex.I))
          (HasDerivAt.fun_mul (hasDerivAt_const z ((x : ℂ)))
            (hasDerivAt_id z).ofReal_comp))
        (HasDerivAt.fun_mul (hasDerivAt_const z ((y : ℂ)))
          (hasDerivAt_id z).ofReal_comp)) (by push_cast; ring)


/-! ### The second curl and the curl eigenstates -/

/-- The first-coordinate section derivative of the curl partner field. -/
theorem hasDerivAt_curlMultipole_x (k : ℝ) (x y z t : ℝ) (hr : ckRadius x y z ≠ 0) (j : Fin 3) :
    HasDerivAt (fun u => ckCurlMultipoleField k (u, y, z, t) j)
      (-((k ^ 2 * x * ckKernel (k * ckRadius x y z) : ℝ) : ℂ) * ckCurlAngular x y z j /
          ((ckRadius x y z ^ 5 : ℝ) : ℂ) +
        ((ckRadialComb k x y z : ℝ) : ℂ) *
          (![-(y : ℂ), (2 : ℂ) * (x : ℂ) + Complex.I * (y : ℂ),
            Complex.I * (z : ℂ)] : Fin 3 → ℂ) j /
          ((ckRadius x y z ^ 5 : ℝ) : ℂ) -
        ((5 * x : ℝ) : ℂ) * ((ckRadialComb k x y z : ℝ) : ℂ) * ckCurlAngular x y z j /
          ((ckRadius x y z ^ 7 : ℝ) : ℂ) +
        ((k ^ 2 * x * Real.sin (k * ckRadius x y z) : ℝ) : ℂ) * ckConstantCurl j /
          ((ckRadius x y z ^ 3 : ℝ) : ℂ) -
        ((3 * x : ℝ) : ℂ) * ((ckKernel (k * ckRadius x y z) : ℝ) : ℂ) * ckConstantCurl j /
          ((ckRadius x y z ^ 5 : ℝ) : ℂ)) x := by
  have hR : ((ckRadius x y z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr
  have hH := hasDerivAt_ckRadialComb_x (k := k) hr
  have hW := hasDerivAt_curlAngular_x x y z j
  have hI5 := hasDerivAt_ckRadiusPow5_inv_x hr
  have hG := hasDerivAt_ckKernelComp_x (k := k) hr
  have hC := hasDerivAt_const x (ckConstantCurl j)
  have hI3 := hasDerivAt_ckRadiusPow3_inv_x hr
  simp only [ckCurlMultipoleField, div_eq_mul_inv]
  refine HasDerivAt.congr_deriv
    (HasDerivAt.fun_add
      (HasDerivAt.fun_mul (HasDerivAt.fun_mul hH hW) hI5)
      (HasDerivAt.fun_mul (HasDerivAt.fun_mul hG hC) hI3)) ?_
  field_simp [hR]
  push_cast
  ring

/-- The second-coordinate section derivative of the curl partner field. -/
theorem hasDerivAt_curlMultipole_y (k : ℝ) (x y z t : ℝ) (hr : ckRadius x y z ≠ 0) (j : Fin 3) :
    HasDerivAt (fun u => ckCurlMultipoleField k (x, u, z, t) j)
      (-((k ^ 2 * y * ckKernel (k * ckRadius x y z) : ℝ) : ℂ) * ckCurlAngular x y z j /
          ((ckRadius x y z ^ 5 : ℝ) : ℂ) +
        ((ckRadialComb k x y z : ℝ) : ℂ) *
          (![-((x : ℂ)) - (2 : ℂ) * Complex.I * (y : ℂ), Complex.I * (x : ℂ),
            -(z : ℂ)] : Fin 3 → ℂ) j /
          ((ckRadius x y z ^ 5 : ℝ) : ℂ) -
        ((5 * y : ℝ) : ℂ) * ((ckRadialComb k x y z : ℝ) : ℂ) * ckCurlAngular x y z j /
          ((ckRadius x y z ^ 7 : ℝ) : ℂ) +
        ((k ^ 2 * y * Real.sin (k * ckRadius x y z) : ℝ) : ℂ) * ckConstantCurl j /
          ((ckRadius x y z ^ 3 : ℝ) : ℂ) -
        ((3 * y : ℝ) : ℂ) * ((ckKernel (k * ckRadius x y z) : ℝ) : ℂ) * ckConstantCurl j /
          ((ckRadius x y z ^ 5 : ℝ) : ℂ)) y := by
  have hR : ((ckRadius x y z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr
  have hH := hasDerivAt_ckRadialComb_y (k := k) hr
  have hW := hasDerivAt_curlAngular_y x y z j
  have hI5 := hasDerivAt_ckRadiusPow5_inv_y hr
  have hG := hasDerivAt_ckKernelComp_y (k := k) hr
  have hC := hasDerivAt_const y (ckConstantCurl j)
  have hI3 := hasDerivAt_ckRadiusPow3_inv_y hr
  simp only [ckCurlMultipoleField, div_eq_mul_inv]
  refine HasDerivAt.congr_deriv
    (HasDerivAt.fun_add
      (HasDerivAt.fun_mul (HasDerivAt.fun_mul hH hW) hI5)
      (HasDerivAt.fun_mul (HasDerivAt.fun_mul hG hC) hI3)) ?_
  field_simp [hR]
  push_cast
  ring

/-- The third-coordinate section derivative of the curl partner field. -/
theorem hasDerivAt_curlMultipole_z (k : ℝ) (x y z t : ℝ) (hr : ckRadius x y z ≠ 0) (j : Fin 3) :
    HasDerivAt (fun u => ckCurlMultipoleField k (x, y, u, t) j)
      (-((k ^ 2 * z * ckKernel (k * ckRadius x y z) : ℝ) : ℂ) * ckCurlAngular x y z j /
          ((ckRadius x y z ^ 5 : ℝ) : ℂ) +
        ((ckRadialComb k x y z : ℝ) : ℂ) *
          (![-(2 : ℂ) * Complex.I * (z : ℂ), (2 : ℂ) * (z : ℂ),
            Complex.I * (x : ℂ) - (y : ℂ)] : Fin 3 → ℂ) j /
          ((ckRadius x y z ^ 5 : ℝ) : ℂ) -
        ((5 * z : ℝ) : ℂ) * ((ckRadialComb k x y z : ℝ) : ℂ) * ckCurlAngular x y z j /
          ((ckRadius x y z ^ 7 : ℝ) : ℂ) +
        ((k ^ 2 * z * Real.sin (k * ckRadius x y z) : ℝ) : ℂ) * ckConstantCurl j /
          ((ckRadius x y z ^ 3 : ℝ) : ℂ) -
        ((3 * z : ℝ) : ℂ) * ((ckKernel (k * ckRadius x y z) : ℝ) : ℂ) * ckConstantCurl j /
          ((ckRadius x y z ^ 5 : ℝ) : ℂ)) z := by
  have hR : ((ckRadius x y z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr
  have hH := hasDerivAt_ckRadialComb_z (k := k) hr
  have hW := hasDerivAt_curlAngular_z x y z j
  have hI5 := hasDerivAt_ckRadiusPow5_inv_z hr
  have hG := hasDerivAt_ckKernelComp_z (k := k) hr
  have hC := hasDerivAt_const z (ckConstantCurl j)
  have hI3 := hasDerivAt_ckRadiusPow3_inv_z hr
  simp only [ckCurlMultipoleField, div_eq_mul_inv]
  refine HasDerivAt.congr_deriv
    (HasDerivAt.fun_add
      (HasDerivAt.fun_mul (HasDerivAt.fun_mul hH hW) hI5)
      (HasDerivAt.fun_mul (HasDerivAt.fun_mul hG hC) hI3)) ?_
  field_simp [hR]
  push_cast
  ring


set_option maxRecDepth 8000 in
/-- The second curl of the dipole mode restores `k²` times the mode: the
Helmholtz identity underlying the eigenstate structure. -/
theorem cartesianCurl_ckCurlMultipoleField (k : ℝ) (s : Spacetime)
    (hr : ckRadius s.1 s.2.1 s.2.2.1 ≠ 0) :
    cartesianCurl (ckCurlMultipoleField k) s
      = fun j => ((k ^ 2 : ℝ) : ℂ) * ckMultipoleField k s j := by
  obtain ⟨x, y, z, t⟩ := s
  have hX := hasDerivAt_curlMultipole_x k x y z t hr
  have hY := hasDerivAt_curlMultipole_y k x y z t hr
  have hZ := hasDerivAt_curlMultipole_z k x y z t hr
  have hR : ((ckRadius x y z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr
  have hR2 : ckRadius x y z ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 := by
    rw [ckRadius]
    exact Real.sq_sqrt (by positivity)
  have hR2c : ((ckRadius x y z : ℝ) : ℂ) ^ 2 = ((x ^ 2 + y ^ 2 + z ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, hR2]
  have hR2d : ((ckRadius x y z : ℝ) : ℂ) ^ 2 =
      ((x : ℝ) : ℂ) ^ 2 + ((y : ℝ) : ℂ) ^ 2 + ((z : ℝ) : ℂ) ^ 2 := by
    rw [hR2c]
    push_cast
    ring
  simp [cartesianCurl, spaceTimePartial, coordinateSection, coordinateValue]
  rw [(hY 2).deriv, (hZ 1).deriv, (hZ 0).deriv, (hX 2).deriv, (hY 0).deriv, (hX 1).deriv]
  funext j
  fin_cases j <;>
    simp only [ckMultipoleField, ckRadialComb, ckCurlAngular, ckConstantCurl,
      ckKernel, ckAngular, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons] <;>
    push_cast <;>
    field_simp [hR] <;>
    first
    | linear_combination (((z : ℝ) : ℂ) *
        (((ckRadius x y z : ℝ) : ℂ) ^ 3 * ((k : ℝ) : ℂ) ^ 3 *
            Complex.cos (((k : ℝ) : ℂ) * ((ckRadius x y z : ℝ) : ℂ)) -
          (6 : ℂ) * ((ckRadius x y z : ℝ) : ℂ) ^ 2 * ((k : ℝ) : ℂ) ^ 2 *
            Complex.sin (((k : ℝ) : ℂ) * ((ckRadius x y z : ℝ) : ℂ)) -
          (15 : ℂ) * ((ckRadius x y z : ℝ) : ℂ) * ((k : ℝ) : ℂ) *
            Complex.cos (((k : ℝ) : ℂ) * ((ckRadius x y z : ℝ) : ℂ)) +
          (15 : ℂ) * Complex.sin (((k : ℝ) : ℂ) *
            ((ckRadius x y z : ℝ) : ℂ)))) * hR2d
    | linear_combination (Complex.I * ((z : ℝ) : ℂ) *
        (((ckRadius x y z : ℝ) : ℂ) ^ 3 * ((k : ℝ) : ℂ) ^ 3 *
            Complex.cos (((k : ℝ) : ℂ) * ((ckRadius x y z : ℝ) : ℂ)) -
          (6 : ℂ) * ((ckRadius x y z : ℝ) : ℂ) ^ 2 * ((k : ℝ) : ℂ) ^ 2 *
            Complex.sin (((k : ℝ) : ℂ) * ((ckRadius x y z : ℝ) : ℂ)) -
          (15 : ℂ) * ((ckRadius x y z : ℝ) : ℂ) * ((k : ℝ) : ℂ) *
            Complex.cos (((k : ℝ) : ℂ) * ((ckRadius x y z : ℝ) : ℂ)) +
          (15 : ℂ) * Complex.sin (((k : ℝ) : ℂ) *
            ((ckRadius x y z : ℝ) : ℂ)))) * hR2d
    | linear_combination (-(((x : ℝ) : ℂ) + Complex.I * ((y : ℝ) : ℂ)) *
        (((ckRadius x y z : ℝ) : ℂ) ^ 3 * ((k : ℝ) : ℂ) ^ 3 *
            Complex.cos (((k : ℝ) : ℂ) * ((ckRadius x y z : ℝ) : ℂ)) -
          (6 : ℂ) * ((ckRadius x y z : ℝ) : ℂ) ^ 2 * ((k : ℝ) : ℂ) ^ 2 *
            Complex.sin (((k : ℝ) : ℂ) * ((ckRadius x y z : ℝ) : ℂ)) -
          (15 : ℂ) * ((ckRadius x y z : ℝ) : ℂ) * ((k : ℝ) : ℂ) *
            Complex.cos (((k : ℝ) : ℂ) * ((ckRadius x y z : ℝ) : ℂ)) +
          (15 : ℂ) * Complex.sin (((k : ℝ) : ℂ) *
            ((ckRadius x y z : ℝ) : ℂ)))) * hR2d


/-! ### Section derivatives packaged as partial derivatives -/

/-- All four coordinate-section derivatives of the dipole mode exist and agree
with the corresponding `spaceTimePartial` values. -/
theorem hasDerivAt_multipole_section (k : ℝ) (s : Spacetime)
    (hr : ckRadius s.1 s.2.1 s.2.2.1 ≠ 0) (i : Fin 4) (j : Fin 3) :
    HasDerivAt (fun u => ckMultipoleField k (coordinateSection s i u) j)
      (spaceTimePartial (fun s' => ckMultipoleField k s' j) s i) (coordinateValue s i) := by
  obtain ⟨x, y, z, t⟩ := s
  fin_cases i
  · show HasDerivAt (fun u => ckMultipoleField k (u, y, z, t) j)
        (deriv (fun u => ckMultipoleField k (u, y, z, t) j) x) x
    rw [(hasDerivAt_multipole_x k x y z t hr j).deriv]
    exact hasDerivAt_multipole_x k x y z t hr j
  · show HasDerivAt (fun u => ckMultipoleField k (x, u, z, t) j)
        (deriv (fun u => ckMultipoleField k (x, u, z, t) j) y) y
    rw [(hasDerivAt_multipole_y k x y z t hr j).deriv]
    exact hasDerivAt_multipole_y k x y z t hr j
  · show HasDerivAt (fun u => ckMultipoleField k (x, y, u, t) j)
        (deriv (fun u => ckMultipoleField k (x, y, u, t) j) z) z
    rw [(hasDerivAt_multipole_z k x y z t hr j).deriv]
    exact hasDerivAt_multipole_z k x y z t hr j
  · show HasDerivAt (fun u => ckMultipoleField k (x, y, z, u) j)
        (deriv (fun u => ckMultipoleField k (x, y, z, u) j) t) t
    have hc : HasDerivAt (fun u => ckMultipoleField k (x, y, z, u) j) 0 t := by
      simp only [ckMultipoleField]
      exact hasDerivAt_const t _
    rw [hc.deriv]
    exact hc

/-- All four coordinate-section derivatives of the curl partner field exist
and agree with the corresponding `spaceTimePartial` values. -/
theorem hasDerivAt_curlMultipole_section (k : ℝ) (s : Spacetime)
    (hr : ckRadius s.1 s.2.1 s.2.2.1 ≠ 0) (i : Fin 4) (j : Fin 3) :
    HasDerivAt (fun u => ckCurlMultipoleField k (coordinateSection s i u) j)
      (spaceTimePartial (fun s' => ckCurlMultipoleField k s' j) s i) (coordinateValue s i) := by
  obtain ⟨x, y, z, t⟩ := s
  fin_cases i
  · show HasDerivAt (fun u => ckCurlMultipoleField k (u, y, z, t) j)
        (deriv (fun u => ckCurlMultipoleField k (u, y, z, t) j) x) x
    rw [(hasDerivAt_curlMultipole_x k x y z t hr j).deriv]
    exact hasDerivAt_curlMultipole_x k x y z t hr j
  · show HasDerivAt (fun u => ckCurlMultipoleField k (x, u, z, t) j)
        (deriv (fun u => ckCurlMultipoleField k (x, u, z, t) j) y) y
    rw [(hasDerivAt_curlMultipole_y k x y z t hr j).deriv]
    exact hasDerivAt_curlMultipole_y k x y z t hr j
  · show HasDerivAt (fun u => ckCurlMultipoleField k (x, y, u, t) j)
        (deriv (fun u => ckCurlMultipoleField k (x, y, u, t) j) z) z
    rw [(hasDerivAt_curlMultipole_z k x y z t hr j).deriv]
    exact hasDerivAt_curlMultipole_z k x y z t hr j
  · show HasDerivAt (fun u => ckCurlMultipoleField k (x, y, z, u) j)
        (deriv (fun u => ckCurlMultipoleField k (x, y, z, u) j) t) t
    have hc : HasDerivAt (fun u => ckCurlMultipoleField k (x, y, z, u) j) 0 t := by
      simp only [ckCurlMultipoleField]
      exact hasDerivAt_const t _
    rw [hc.deriv]
    exact hc

/-! ### Linearity of the partial derivative and the curl -/

/-- A constant complex multiple factors out of the partial derivative of a
component, provided the component has its section derivatives. -/
theorem spaceTimePartial_const_mul (s : Spacetime) (c : ℂ) (F : Spacetime → Fin 3 → ℂ)
    (hF : ∀ (i : Fin 4) (j : Fin 3), HasDerivAt (fun u => F (coordinateSection s i u) j)
      (spaceTimePartial (fun s' => F s' j) s i) (coordinateValue s i)) (i : Fin 4) (j : Fin 3) :
    spaceTimePartial (fun s' => c * F s' j) s i
      = c * spaceTimePartial (fun s' => F s' j) s i := by
  have H : HasDerivAt (fun u => c * F (coordinateSection s i u) j)
      (c * spaceTimePartial (fun s' => F s' j) s i) (coordinateValue s i) :=
    (hF i j).const_mul c
  rw [show spaceTimePartial (fun s' => c * F s' j) s i
      = deriv (fun u => c * F (coordinateSection s i u) j) (coordinateValue s i) from rfl,
    H.deriv]

/-- The partial derivative of a componentwise sum is the sum of the partial
derivatives. -/
theorem spaceTimePartial_add (s : Spacetime) (A B : Spacetime → Fin 3 → ℂ)
    (hA : ∀ (i : Fin 4) (j : Fin 3), HasDerivAt (fun u => A (coordinateSection s i u) j)
      (spaceTimePartial (fun s' => A s' j) s i) (coordinateValue s i))
    (hB : ∀ (i : Fin 4) (j : Fin 3), HasDerivAt (fun u => B (coordinateSection s i u) j)
      (spaceTimePartial (fun s' => B s' j) s i) (coordinateValue s i)) (i : Fin 4) (j : Fin 3) :
    spaceTimePartial (fun s' => A s' j + B s' j) s i
      = spaceTimePartial (fun s' => A s' j) s i + spaceTimePartial (fun s' => B s' j) s i := by
  rw [show spaceTimePartial (fun s' => A s' j + B s' j) s i
      = deriv (fun u => A (coordinateSection s i u) j + B (coordinateSection s i u) j)
          (coordinateValue s i) from rfl,
    ((hA i j).fun_add (hB i j)).deriv]

/-- The partial derivative of a componentwise difference is the difference of
the partial derivatives. -/
theorem spaceTimePartial_sub (s : Spacetime) (A B : Spacetime → Fin 3 → ℂ)
    (hA : ∀ (i : Fin 4) (j : Fin 3), HasDerivAt (fun u => A (coordinateSection s i u) j)
      (spaceTimePartial (fun s' => A s' j) s i) (coordinateValue s i))
    (hB : ∀ (i : Fin 4) (j : Fin 3), HasDerivAt (fun u => B (coordinateSection s i u) j)
      (spaceTimePartial (fun s' => B s' j) s i) (coordinateValue s i)) (i : Fin 4) (j : Fin 3) :
    spaceTimePartial (fun s' => A s' j - B s' j) s i
      = spaceTimePartial (fun s' => A s' j) s i - spaceTimePartial (fun s' => B s' j) s i := by
  rw [show spaceTimePartial (fun s' => A s' j - B s' j) s i
      = deriv (fun u => A (coordinateSection s i u) j - B (coordinateSection s i u) j)
          (coordinateValue s i) from rfl,
    ((hA i j).fun_sub (hB i j)).deriv]

/-- A constant complex multiple factors out of the Cartesian curl. -/
theorem cartesianCurl_const_mul (s : Spacetime) (c : ℂ) (F : Spacetime → Fin 3 → ℂ)
    (hF : ∀ (i : Fin 4) (j : Fin 3), HasDerivAt (fun u => F (coordinateSection s i u) j)
      (spaceTimePartial (fun s' => F s' j) s i) (coordinateValue s i)) :
    cartesianCurl (fun s' j => c * F s' j) s = fun j => c * cartesianCurl F s j := by
  funext j
  fin_cases j <;>
    simp [cartesianCurl, spaceTimePartial_const_mul s c F hF] <;>
    ring

/-- The Cartesian curl of a componentwise sum is the sum of the curls. -/
theorem cartesianCurl_add (s : Spacetime) (A B : Spacetime → Fin 3 → ℂ)
    (hA : ∀ (i : Fin 4) (j : Fin 3), HasDerivAt (fun u => A (coordinateSection s i u) j)
      (spaceTimePartial (fun s' => A s' j) s i) (coordinateValue s i))
    (hB : ∀ (i : Fin 4) (j : Fin 3), HasDerivAt (fun u => B (coordinateSection s i u) j)
      (spaceTimePartial (fun s' => B s' j) s i) (coordinateValue s i)) :
    cartesianCurl (fun s' j => A s' j + B s' j) s
      = fun j => cartesianCurl A s j + cartesianCurl B s j := by
  funext j
  fin_cases j <;>
    simp [cartesianCurl, spaceTimePartial_add s A B hA hB] <;>
    ring

/-- The Cartesian curl of a componentwise difference is the difference of the
curls. -/
theorem cartesianCurl_sub (s : Spacetime) (A B : Spacetime → Fin 3 → ℂ)
    (hA : ∀ (i : Fin 4) (j : Fin 3), HasDerivAt (fun u => A (coordinateSection s i u) j)
      (spaceTimePartial (fun s' => A s' j) s i) (coordinateValue s i))
    (hB : ∀ (i : Fin 4) (j : Fin 3), HasDerivAt (fun u => B (coordinateSection s i u) j)
      (spaceTimePartial (fun s' => B s' j) s i) (coordinateValue s i)) :
    cartesianCurl (fun s' j => A s' j - B s' j) s
      = fun j => cartesianCurl A s j - cartesianCurl B s j := by
  funext j
  fin_cases j <;>
    simp [cartesianCurl, spaceTimePartial_sub s A B hA hB] <;>
    ring

/-! ### The Beltrami eigenstates of the curl -/

/-- The `+` eigenstate `k M̃ + Ñ` of the Cartesian curl, with eigenvalue `+k`;
this is the Chandrasekhar–Kendall combination carried by the dipole mode. -/
noncomputable def ckBeltramiPlus (k : ℝ) : Spacetime → Fin 3 → ℂ :=
  fun s j => ((k : ℝ) : ℂ) * ckMultipoleField k s j + ckCurlMultipoleField k s j

/-- The `-` eigenstate `k M̃ - Ñ` of the Cartesian curl, with eigenvalue `-k`. -/
noncomputable def ckBeltramiMinus (k : ℝ) : Spacetime → Fin 3 → ℂ :=
  fun s j => ((k : ℝ) : ℂ) * ckMultipoleField k s j - ckCurlMultipoleField k s j

/-- `k M̃ + Ñ` is an eigenstate of the Cartesian curl with eigenvalue `+k`. -/
theorem cartesianCurl_ckBeltramiPlus (k : ℝ) (s : Spacetime)
    (hr : ckRadius s.1 s.2.1 s.2.2.1 ≠ 0) :
    cartesianCurl (ckBeltramiPlus k) s = fun j => ((k : ℝ) : ℂ) * ckBeltramiPlus k s j := by
  have hA : ∀ (i : Fin 4) (j : Fin 3), HasDerivAt
      (fun u => ((k : ℝ) : ℂ) * ckMultipoleField k (coordinateSection s i u) j)
      (spaceTimePartial (fun s' => ((k : ℝ) : ℂ) * ckMultipoleField k s' j) s i)
      (coordinateValue s i) := by
    intro i j
    refine HasDerivAt.congr_deriv
      ((hasDerivAt_multipole_section k s hr i j).const_mul ((k : ℝ) : ℂ)) ?_
    rw [spaceTimePartial_const_mul s _ (ckMultipoleField k)
      (hasDerivAt_multipole_section k s hr) i j]
  rw [show ckBeltramiPlus k = fun s' j =>
        ((k : ℝ) : ℂ) * ckMultipoleField k s' j + ckCurlMultipoleField k s' j from rfl,
    cartesianCurl_add s _ _ hA (hasDerivAt_curlMultipole_section k s hr),
    cartesianCurl_const_mul s _ (ckMultipoleField k) (hasDerivAt_multipole_section k s hr),
    cartesianCurl_ckMultipoleField k s hr, cartesianCurl_ckCurlMultipoleField k s hr]
  funext j
  push_cast
  ring

/-- `k M̃ - Ñ` is an eigenstate of the Cartesian curl with eigenvalue `-k`. -/
theorem cartesianCurl_ckBeltramiMinus (k : ℝ) (s : Spacetime)
    (hr : ckRadius s.1 s.2.1 s.2.2.1 ≠ 0) :
    cartesianCurl (ckBeltramiMinus k) s = fun j => -((k : ℝ) : ℂ) * ckBeltramiMinus k s j := by
  have hA : ∀ (i : Fin 4) (j : Fin 3), HasDerivAt
      (fun u => ((k : ℝ) : ℂ) * ckMultipoleField k (coordinateSection s i u) j)
      (spaceTimePartial (fun s' => ((k : ℝ) : ℂ) * ckMultipoleField k s' j) s i)
      (coordinateValue s i) := by
    intro i j
    refine HasDerivAt.congr_deriv
      ((hasDerivAt_multipole_section k s hr i j).const_mul ((k : ℝ) : ℂ)) ?_
    rw [spaceTimePartial_const_mul s _ (ckMultipoleField k)
      (hasDerivAt_multipole_section k s hr) i j]
  rw [show ckBeltramiMinus k = fun s' j =>
        ((k : ℝ) : ℂ) * ckMultipoleField k s' j - ckCurlMultipoleField k s' j from rfl,
    cartesianCurl_sub s _ _ hA (hasDerivAt_curlMultipole_section k s hr),
    cartesianCurl_const_mul s _ (ckMultipoleField k) (hasDerivAt_multipole_section k s hr),
    cartesianCurl_ckMultipoleField k s hr, cartesianCurl_ckCurlMultipoleField k s hr]
  funext j
  push_cast
  ring

/-! ### The TE and TM modes in the paper's normalization -/

/-- The common scale of the Cartesian dipole modes in the chosen angular convention. -/
noncomputable def ckDipoleScale (k : ℝ) : ℂ :=
  (Real.sqrt (3 / (16 * Real.pi)) : ℂ) / (k : ℂ) ^ 3

/-- The TE vector potential, with the factor `1/(iω)` from Supplementary
Methods equation (1) and `ω = k`. -/
noncomputable def ckTEMode (k : ℝ) : Spacetime → Fin 3 → ℂ :=
  fun s j => (Complex.I * ckDipoleScale k) * ckMultipoleField k s j

/-- The TM vector potential, with the factor `1/k²` on the curl of the
magnetic multipole from Supplementary Methods equation (2). -/
noncomputable def ckTMMode (k : ℝ) : Spacetime → Fin 3 → ℂ :=
  fun s j => -(ckDipoleScale k / (k : ℂ)) * ckCurlMultipoleField k s j

/-- All coordinate-section derivatives of the TE mode exist. -/
theorem hasDerivAt_ckTEMode_section (k : ℝ) (s : Spacetime)
    (hr : ckRadius s.1 s.2.1 s.2.2.1 ≠ 0) (i : Fin 4) (j : Fin 3) :
    HasDerivAt (fun u => ckTEMode k (coordinateSection s i u) j)
      (spaceTimePartial (fun s' => ckTEMode k s' j) s i) (coordinateValue s i) := by
  refine HasDerivAt.congr_deriv
    ((hasDerivAt_multipole_section k s hr i j).const_mul (Complex.I * ckDipoleScale k)) ?_
  rw [show ckTEMode k = fun s' j' =>
      (Complex.I * ckDipoleScale k) * ckMultipoleField k s' j' from rfl,
    spaceTimePartial_const_mul s _ (ckMultipoleField k)
      (hasDerivAt_multipole_section k s hr) i j]

/-- All coordinate-section derivatives of the TM mode exist. -/
theorem hasDerivAt_ckTMMode_section (k : ℝ) (s : Spacetime)
    (hr : ckRadius s.1 s.2.1 s.2.2.1 ≠ 0) (i : Fin 4) (j : Fin 3) :
    HasDerivAt (fun u => ckTMMode k (coordinateSection s i u) j)
      (spaceTimePartial (fun s' => ckTMMode k s' j) s i) (coordinateValue s i) := by
  refine HasDerivAt.congr_deriv
    ((hasDerivAt_curlMultipole_section k s hr i j).const_mul (-(ckDipoleScale k / (k : ℂ)))) ?_
  rw [show ckTMMode k = fun s' j' =>
      -(ckDipoleScale k / (k : ℂ)) * ckCurlMultipoleField k s' j' from rfl,
    spaceTimePartial_const_mul s _ (ckCurlMultipoleField k)
      (hasDerivAt_curlMultipole_section k s hr) i j]

/-- The curl of the TE mode is `-ik` times the TM mode. -/
theorem cartesianCurl_ckTEMode (k : ℝ) (hk : k ≠ 0) (s : Spacetime)
    (hr : ckRadius s.1 s.2.1 s.2.2.1 ≠ 0) (j : Fin 3) :
    cartesianCurl (ckTEMode k) s j = -Complex.I * (k : ℂ) * ckTMMode k s j := by
  have hkC : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  rw [show ckTEMode k = fun s' j' =>
      (Complex.I * ckDipoleScale k) * ckMultipoleField k s' j' from rfl,
    cartesianCurl_const_mul s _ (ckMultipoleField k) (hasDerivAt_multipole_section k s hr),
    cartesianCurl_ckMultipoleField k s hr]
  change (Complex.I * ckDipoleScale k) * ckCurlMultipoleField k s j =
    -Complex.I * (k : ℂ) * (-(ckDipoleScale k / (k : ℂ)) * ckCurlMultipoleField k s j)
  field_simp [hkC]

/-- The curl of the TM mode is `ik` times the TE mode. -/
theorem cartesianCurl_ckTMMode (k : ℝ) (hk : k ≠ 0) (s : Spacetime)
    (hr : ckRadius s.1 s.2.1 s.2.2.1 ≠ 0) (j : Fin 3) :
    cartesianCurl (ckTMMode k) s j = Complex.I * (k : ℂ) * ckTEMode k s j := by
  have hkC : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  rw [show ckTMMode k = fun s' j' =>
      -(ckDipoleScale k / (k : ℂ)) * ckCurlMultipoleField k s' j' from rfl,
    cartesianCurl_const_mul s _ (ckCurlMultipoleField k) (hasDerivAt_curlMultipole_section k s hr),
    cartesianCurl_ckCurlMultipoleField k s hr]
  change -(ckDipoleScale k / (k : ℂ)) * (((k ^ 2 : ℝ) : ℂ) * ckMultipoleField k s j) =
    Complex.I * (k : ℂ) * (Complex.I * ckDipoleScale k * ckMultipoleField k s j)
  push_cast
  calc
    _ = -(ckDipoleScale k * (k : ℂ)) * ckMultipoleField k s j := by
      field_simp [hkC]
    _ = _ := by
      linear_combination -((k : ℂ) * ckDipoleScale k * ckMultipoleField k s j) * Complex.I_mul_I

/-- The supplementary normalizations give `A^TM = (i/k) curl A^TE`. -/
theorem ckTMMode_eq_scaled_curl_ckTEMode (k : ℝ) (hk : k ≠ 0) (s : Spacetime)
    (hr : ckRadius s.1 s.2.1 s.2.2.1 ≠ 0) (j : Fin 3) :
    ckTMMode k s j = Complex.I / (k : ℂ) * cartesianCurl (ckTEMode k) s j := by
  have hkC : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  rw [cartesianCurl_ckTEMode k hk s hr]
  calc
    _ = -(Complex.I * Complex.I) * ckTMMode k s j := by rw [Complex.I_mul_I, neg_neg, one_mul]
    _ = _ := by field_simp [hkC]

/-- Multiplication of the TM mode by the relative phase `i` preserves the
existence of all coordinate-section derivatives. -/
private theorem hasDerivAt_ckPhaseTM_section (k : ℝ) (s : Spacetime)
    (hr : ckRadius s.1 s.2.1 s.2.2.1 ≠ 0) (i : Fin 4) (j : Fin 3) :
    HasDerivAt (fun u => Complex.I * ckTMMode k (coordinateSection s i u) j)
      (spaceTimePartial (fun s' => Complex.I * ckTMMode k s' j) s i) (coordinateValue s i) := by
  refine ((hasDerivAt_ckTMMode_section k s hr i j).const_mul Complex.I).congr_deriv ?_
  rw [spaceTimePartial_const_mul s _ (ckTMMode k) (hasDerivAt_ckTMMode_section k s hr) i j]

/-- The combination `A^TE + i A^TM` has curl eigenvalue `-k`, as in
equation (6) on the punctured spatial domain. -/
theorem cartesianCurl_eigenCombinationPlus (k : ℝ) (hk : k ≠ 0) (s : Spacetime)
    (hr : ckRadius s.1 s.2.1 s.2.2.1 ≠ 0) :
    cartesianCurl (fun s' j => ckTEMode k s' j + Complex.I * ckTMMode k s' j) s
      = fun j => -(k : ℂ) * (ckTEMode k s j + Complex.I * ckTMMode k s j) := by
  funext j
  rw [cartesianCurl_add s (ckTEMode k) (fun s' j => Complex.I * ckTMMode k s' j)
      (hasDerivAt_ckTEMode_section k s hr) (hasDerivAt_ckPhaseTM_section k s hr),
    cartesianCurl_const_mul s _ (ckTMMode k) (hasDerivAt_ckTMMode_section k s hr)]
  change cartesianCurl (ckTEMode k) s j + Complex.I * cartesianCurl (ckTMMode k) s j = _
  rw [cartesianCurl_ckTEMode k hk s hr, cartesianCurl_ckTMMode k hk s hr]
  linear_combination ((k : ℂ) * ckTEMode k s j) * Complex.I_mul_I

/-- The combination `A^TE - i A^TM` has curl eigenvalue `k`, as in
equation (6) on the punctured spatial domain. -/
theorem cartesianCurl_eigenCombinationMinus (k : ℝ) (hk : k ≠ 0) (s : Spacetime)
    (hr : ckRadius s.1 s.2.1 s.2.2.1 ≠ 0) :
    cartesianCurl (fun s' j => ckTEMode k s' j - Complex.I * ckTMMode k s' j) s
      = fun j => (k : ℂ) * (ckTEMode k s j - Complex.I * ckTMMode k s j) := by
  funext j
  rw [cartesianCurl_sub s (ckTEMode k) (fun s' j => Complex.I * ckTMMode k s' j)
      (hasDerivAt_ckTEMode_section k s hr) (hasDerivAt_ckPhaseTM_section k s hr),
    cartesianCurl_const_mul s _ (ckTMMode k) (hasDerivAt_ckTMMode_section k s hr)]
  change cartesianCurl (ckTEMode k) s j - Complex.I * cartesianCurl (ckTMMode k) s j = _
  rw [cartesianCurl_ckTEMode k hk s hr, cartesianCurl_ckTMMode k hk s hr]
  linear_combination -((k : ℂ) * ckTEMode k s j) * Complex.I_mul_I

/-! ### Force-freeness and nondegeneracy -/

/-- The cross product of a vector with itself vanishes. -/
theorem cross3_self_eq_zero (v : Fin 3 → ℂ) : cross3 v v = 0 := by
  funext j
  fin_cases j
  · show v 1 * v 2 - v 2 * v 1 = 0
    ring
  · show v 2 * v 0 - v 0 * v 2 = 0
    ring
  · show v 0 * v 1 - v 1 * v 0 = 0
    ring

/-- The cross product of a vector with a scalar multiple of itself vanishes. -/
theorem cross3_scale_self_eq_zero (v : Fin 3 → ℂ) (c : ℂ) :
    cross3 v (fun j => c * v j) = 0 := by
  funext j
  fin_cases j
  · show v 1 * (c * v 2) - v 2 * (c * v 1) = 0
    ring
  · show v 2 * (c * v 0) - v 0 * (c * v 2) = 0
    ring
  · show v 0 * (c * v 1) - v 1 * (c * v 0) = 0
    ring

/-- The `+` Beltrami eigenstate is force-free: its cross product with its own
curl vanishes identically on the punctured space. -/
theorem forceFree_ckBeltramiPlus (k : ℝ) (s : Spacetime)
    (hr : ckRadius s.1 s.2.1 s.2.2.1 ≠ 0) :
    cross3 (ckBeltramiPlus k s) (cartesianCurl (ckBeltramiPlus k) s) = 0 := by
  rw [cartesianCurl_ckBeltramiPlus k s hr]
  exact cross3_scale_self_eq_zero _ _

/-- The `-` Beltrami eigenstate is force-free on the punctured space. -/
theorem forceFree_ckBeltramiMinus (k : ℝ) (s : Spacetime)
    (hr : ckRadius s.1 s.2.1 s.2.2.1 ≠ 0) :
    cross3 (ckBeltramiMinus k s) (cartesianCurl (ckBeltramiMinus k) s) = 0 := by
  rw [cartesianCurl_ckBeltramiMinus k s hr]
  exact cross3_scale_self_eq_zero _ _

/-- The radius of the nondegeneracy witness point is `π/2`. -/
theorem ckRadius_pi_half : ckRadius 0 0 (Real.pi / 2) = Real.pi / 2 := by
  simp only [ckRadius]
  have h : (0 : ℝ) ^ 2 + 0 ^ 2 + (Real.pi / 2) ^ 2 = (Real.pi / 2) ^ 2 := by ring
  rw [h, Real.sqrt_sq_eq_abs, abs_of_pos (by positivity)]

/-- At the point `(0, 0, π/2)` the wavenumber-one dipole mode takes the
explicit value `(4/π², 4i/π², 0)`, so the construction is nondegenerate. -/
theorem ckMultipoleField_one_pi_half :
    ckMultipoleField 1 (0, 0, Real.pi / 2, 0)
      = fun j => ![(4 : ℂ) / Real.pi ^ 2, (4 : ℂ) / Real.pi ^ 2 * Complex.I, 0] j := by
  funext j
  fin_cases j <;>
    simp [ckMultipoleField, ckAngular, ckKernel, ckRadius_pi_half,
      Real.sin_pi_div_two, Real.cos_pi_div_two] <;>
    field_simp <;>
    ring

/-- The dipole mode is nonzero at the witness point, so it is not the zero
field. -/
theorem ckMultipoleField_one_pi_half_ne_zero :
    ckMultipoleField 1 (0, 0, Real.pi / 2, 0) 0 ≠ 0 := by
  rw [ckMultipoleField_one_pi_half]
  exact div_ne_zero (by norm_num) (pow_ne_zero 2 (by exact_mod_cast Real.pi_ne_zero))

end Qatlib.Papers.KnottedLight08.CurlEigenstate
