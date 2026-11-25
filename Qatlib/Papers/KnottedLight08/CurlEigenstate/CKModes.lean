/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.RationalPowerMaxwell

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The dipole Chandrasekhar–Kendall mode in Cartesian coordinates

[IrvineBouwmeester2008KnottedLight], Supplementary Methods 1, equations (1)–(2),
[DOI](https://doi.org/10.1038/nphys1056).
The `l = m = 1` vector spherical harmonics are written in explicit Cartesian
coordinates. The magnetic multipole `f₁(kr) LY₁₁` with the free-space radial
function `f₁ = j₁/√2` and `LY₁₁` proportional to `(z, iz, -(x+iy))/r` becomes,
up to a nonzero constant, the regular rational-trigonometric field
`g(kr) (z, iz, -(x+iy))/r³` with `g(u) = sin u - u cos u = u² j₁(u)`.
This module computes its Cartesian curl and divergence in closed form on the
punctured space `r > 0`; the companion module `CKEigenstates` turns the curl
relations into the Chandrasekhar–Kendall eigenstate structure.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.CurlEigenstate

open Qatlib.Papers.KnotLight13.TorusFamily
  (Spacetime cartesianCurl cartesianDivergence spaceTimePartial coordinateSection
    coordinateValue)

/-! ### Explicit Cartesian form of the dipole mode -/

/-- The Euclidean radius of a spatial triple. -/
noncomputable def ckRadius (x y z : ℝ) : ℝ := Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2)

/-- The regular radial kernel of the dipole mode, `u ↦ sin u - u * cos u`,
equal to `u ^ 2 * j₁ u` for the order-one spherical Bessel function `j₁`. -/
noncomputable def ckKernel (u : ℝ) : ℝ := Real.sin u - u * Real.cos u

/-- The angular factor of `LY₁₁` in Cartesian coordinates: the polynomial
vector `(z, iz, -(x+iy))`. -/
def ckAngular (x y z : ℝ) : Fin 3 → ℂ :=
  ![(z : ℂ), (Complex.I * (z : ℂ)), -((x : ℂ) + Complex.I * (y : ℂ))]

/-- The radial combination `k²r² sin(kr) - 3 g(kr)` governing the curl of the
dipole mode. -/
noncomputable def ckRadialComb (k x y z : ℝ) : ℝ :=
  k ^ 2 * ckRadius x y z ^ 2 * Real.sin (k * ckRadius x y z)
    - 3 * ckKernel (k * ckRadius x y z)

/-- The polynomial numerator of the curl partner of the dipole mode, the cross
product `(x, y, z) × (z, iz, -(x+iy))` of the radius with the angular factor. -/
def ckCurlAngular (x y z : ℝ) : Fin 3 → ℂ :=
  ![-((x : ℂ) * (y : ℂ)) - Complex.I * ((y : ℂ) ^ 2 + (z : ℂ) ^ 2),
    (x : ℂ) ^ 2 + (z : ℂ) ^ 2 + Complex.I * ((x : ℂ) * (y : ℂ)),
    Complex.I * ((x : ℂ) * (z : ℂ)) - (y : ℂ) * (z : ℂ)]

/-- The constant curl of the angular factor, `∇ × (z, iz, -(x+iy)) = (-2i, 2, 0)`. -/
def ckConstantCurl : Fin 3 → ℂ := ![-(2 * Complex.I), 2, 0]

/-- The `l = m = 1` magnetic multipole `f₁(kr) LY₁₁` in explicit Cartesian
coordinates, up to the nonzero constant `j₁(kr) = g(kr)/(kr)²`; it is carried
as a spacetime field independent of time. -/
noncomputable def ckMultipoleField (k : ℝ) : Spacetime → Fin 3 → ℂ :=
  fun s j => ((ckKernel (k * ckRadius s.1 s.2.1 s.2.2.1) : ℝ) : ℂ) *
    ckAngular s.1 s.2.1 s.2.2.1 j / ((ckRadius s.1 s.2.1 s.2.2.1 ^ 3 : ℝ) : ℂ)

/-- The closed-form Cartesian curl of the dipole mode on the punctured space:
the radial combination times the cross product, plus the constant curl term. -/
noncomputable def ckCurlMultipoleField (k : ℝ) : Spacetime → Fin 3 → ℂ :=
  fun s j => ((ckRadialComb k s.1 s.2.1 s.2.2.1 : ℝ) : ℂ) *
      ckCurlAngular s.1 s.2.1 s.2.2.1 j / ((ckRadius s.1 s.2.1 s.2.2.1 ^ 5 : ℝ) : ℂ) +
    ((ckKernel (k * ckRadius s.1 s.2.1 s.2.2.1) : ℝ) : ℂ) * ckConstantCurl j /
      ((ckRadius s.1 s.2.1 s.2.2.1 ^ 3 : ℝ) : ℂ)

/-! ### Derivatives of the radial factors along coordinate sections -/

/-- The radial kernel has derivative `u * sin u`. -/
theorem hasDerivAt_ckKernel (u : ℝ) : HasDerivAt ckKernel (u * Real.sin u) u := by
  show HasDerivAt (fun v => Real.sin v - v * Real.cos v) (u * Real.sin u) u
  exact HasDerivAt.congr_deriv (HasDerivAt.sub (Real.hasDerivAt_sin u)
    ((hasDerivAt_id u).mul (Real.hasDerivAt_cos u))) (by simp only [id_eq]; ring)

/-- The radius is differentiable in the first coordinate away from the origin. -/
theorem hasDerivAt_ckRadius_x {x y z : ℝ} (hr : ckRadius x y z ≠ 0) :
    HasDerivAt (fun u => ckRadius u y z) (x / ckRadius x y z) x := by
  have hq : x ^ 2 + y ^ 2 + z ^ 2 ≠ 0 := fun h => hr (by rw [ckRadius, h, Real.sqrt_zero])
  have hsn : Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) ≠ 0 :=
    (Real.sqrt_ne_zero (by positivity)).mpr hq
  have hw : HasDerivAt (fun u => u ^ 2 + y ^ 2 + z ^ 2) (2 * x) x :=
    HasDerivAt.fun_add (HasDerivAt.fun_add ((hasDerivAt_id x).pow 2)
        (hasDerivAt_const x (y ^ 2 : ℝ))) (hasDerivAt_const x (z ^ 2 : ℝ)) |>.congr_deriv
      (by simp only [id_eq]; ring)
  have hc := (Real.hasDerivAt_sqrt hq).comp x hw
  refine hc.congr_deriv ?_
  rw [ckRadius]
  field_simp [hsn]

/-- The radius is differentiable in the second coordinate away from the origin. -/
theorem hasDerivAt_ckRadius_y {x y z : ℝ} (hr : ckRadius x y z ≠ 0) :
    HasDerivAt (fun u => ckRadius x u z) (y / ckRadius x y z) y := by
  have hq : x ^ 2 + y ^ 2 + z ^ 2 ≠ 0 := fun h => hr (by rw [ckRadius, h, Real.sqrt_zero])
  have hsn : Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) ≠ 0 :=
    (Real.sqrt_ne_zero (by positivity)).mpr hq
  have hw : HasDerivAt (fun u => x ^ 2 + u ^ 2 + z ^ 2) (2 * y) y :=
    HasDerivAt.fun_add (HasDerivAt.fun_add (hasDerivAt_const y (x ^ 2 : ℝ))
        ((hasDerivAt_id y).pow 2)) (hasDerivAt_const y (z ^ 2 : ℝ)) |>.congr_deriv
      (by simp only [id_eq]; ring)
  have hc := (Real.hasDerivAt_sqrt hq).comp y hw
  refine hc.congr_deriv ?_
  rw [ckRadius]
  field_simp [hsn]

/-- The radius is differentiable in the third coordinate away from the origin. -/
theorem hasDerivAt_ckRadius_z {x y z : ℝ} (hr : ckRadius x y z ≠ 0) :
    HasDerivAt (fun u => ckRadius x y u) (z / ckRadius x y z) z := by
  have hq : x ^ 2 + y ^ 2 + z ^ 2 ≠ 0 := fun h => hr (by rw [ckRadius, h, Real.sqrt_zero])
  have hsn : Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) ≠ 0 :=
    (Real.sqrt_ne_zero (by positivity)).mpr hq
  have hw : HasDerivAt (fun u => x ^ 2 + y ^ 2 + u ^ 2) (2 * z) z :=
    HasDerivAt.fun_add (HasDerivAt.fun_add (hasDerivAt_const z (x ^ 2 : ℝ))
        (hasDerivAt_const z (y ^ 2 : ℝ))) ((hasDerivAt_id z).pow 2) |>.congr_deriv
      (by simp only [id_eq]; ring)
  have hc := (Real.hasDerivAt_sqrt hq).comp z hw
  refine hc.congr_deriv ?_
  rw [ckRadius]
  field_simp [hsn]

/-- The composed kernel has the denominator-free section derivative
`k² c sin(kr)` in the varying coordinate `c`. -/
theorem hasDerivAt_ckKernelComp_x {k x y z : ℝ} (hr : ckRadius x y z ≠ 0) :
    HasDerivAt (fun u => ((ckKernel (k * ckRadius u y z) : ℝ) : ℂ))
      (((k ^ 2 * x * Real.sin (k * ckRadius x y z)) : ℝ) : ℂ) x := by
  have hcomp : HasDerivAt (fun u => ckKernel (k * ckRadius u y z))
      ((k * ckRadius x y z) * Real.sin (k * ckRadius x y z) * (k * (x / ckRadius x y z))) x :=
    (hasDerivAt_ckKernel _).comp x ((hasDerivAt_ckRadius_x hr).const_mul k)
  refine hcomp.ofReal_comp.congr_deriv ?_
  rw [Complex.ofReal_inj]
  field_simp [hr]

/-- The composed kernel has a denominator-free derivative along the `y` section. -/
theorem hasDerivAt_ckKernelComp_y {k x y z : ℝ} (hr : ckRadius x y z ≠ 0) :
    HasDerivAt (fun u => ((ckKernel (k * ckRadius x u z) : ℝ) : ℂ))
      (((k ^ 2 * y * Real.sin (k * ckRadius x y z)) : ℝ) : ℂ) y := by
  have hcomp : HasDerivAt (fun u => ckKernel (k * ckRadius x u z))
      ((k * ckRadius x y z) * Real.sin (k * ckRadius x y z) * (k * (y / ckRadius x y z))) y :=
    (hasDerivAt_ckKernel _).comp y ((hasDerivAt_ckRadius_y hr).const_mul k)
  refine hcomp.ofReal_comp.congr_deriv ?_
  rw [Complex.ofReal_inj]
  field_simp [hr]

/-- The composed kernel has a denominator-free derivative along the `z` section. -/
theorem hasDerivAt_ckKernelComp_z {k x y z : ℝ} (hr : ckRadius x y z ≠ 0) :
    HasDerivAt (fun u => ((ckKernel (k * ckRadius x y u) : ℝ) : ℂ))
      (((k ^ 2 * z * Real.sin (k * ckRadius x y z)) : ℝ) : ℂ) z := by
  have hcomp : HasDerivAt (fun u => ckKernel (k * ckRadius x y u))
      ((k * ckRadius x y z) * Real.sin (k * ckRadius x y z) * (k * (z / ckRadius x y z))) z :=
    (hasDerivAt_ckKernel _).comp z ((hasDerivAt_ckRadius_z hr).const_mul k)
  refine hcomp.ofReal_comp.congr_deriv ?_
  rw [Complex.ofReal_inj]
  field_simp [hr]

/-! ### The reciprocal radius powers along coordinate sections -/

/-- The reciprocal third power of the radius along the first coordinate. -/
theorem hasDerivAt_ckRadiusPow3_inv_x {x y z : ℝ} (hr : ckRadius x y z ≠ 0) :
    HasDerivAt (fun u => (((ckRadius u y z ^ 3 : ℝ) : ℂ))⁻¹)
      (-((3 * x : ℝ) : ℂ) / ((ckRadius x y z ^ 5 : ℝ) : ℂ)) x := by
  have h3 : HasDerivAt (fun u => ((ckRadius u y z ^ 3 : ℝ) : ℂ))
      (((3 * x * ckRadius x y z) : ℝ) : ℂ) x := by
    refine HasDerivAt.congr_deriv (((hasDerivAt_ckRadius_x hr).pow 3).ofReal_comp) ?_
    rw [Complex.ofReal_inj]
    field_simp [hr]
    ring
  have hne : ((ckRadius x y z ^ 3 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero 3 hr
  refine HasDerivAt.congr_deriv (h3.inv hne) ?_
  have e2 : (((ckRadius x y z ^ 3 : ℝ) : ℂ)) ^ 2 = ((ckRadius x y z ^ 6 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [e2, div_eq_div_iff (by exact_mod_cast pow_ne_zero 6 hr)
    (by exact_mod_cast pow_ne_zero 5 hr)]
  push_cast
  ring

/-- The reciprocal third power of the radius along the second coordinate. -/
theorem hasDerivAt_ckRadiusPow3_inv_y {x y z : ℝ} (hr : ckRadius x y z ≠ 0) :
    HasDerivAt (fun u => (((ckRadius x u z ^ 3 : ℝ) : ℂ))⁻¹)
      (-((3 * y : ℝ) : ℂ) / ((ckRadius x y z ^ 5 : ℝ) : ℂ)) y := by
  have h3 : HasDerivAt (fun u => ((ckRadius x u z ^ 3 : ℝ) : ℂ))
      (((3 * y * ckRadius x y z) : ℝ) : ℂ) y := by
    refine HasDerivAt.congr_deriv (((hasDerivAt_ckRadius_y hr).pow 3).ofReal_comp) ?_
    rw [Complex.ofReal_inj]
    field_simp [hr]
    ring
  have hne : ((ckRadius x y z ^ 3 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero 3 hr
  refine HasDerivAt.congr_deriv (h3.inv hne) ?_
  have e2 : (((ckRadius x y z ^ 3 : ℝ) : ℂ)) ^ 2 = ((ckRadius x y z ^ 6 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [e2, div_eq_div_iff (by exact_mod_cast pow_ne_zero 6 hr)
    (by exact_mod_cast pow_ne_zero 5 hr)]
  push_cast
  ring

/-- The reciprocal third power of the radius along the third coordinate. -/
theorem hasDerivAt_ckRadiusPow3_inv_z {x y z : ℝ} (hr : ckRadius x y z ≠ 0) :
    HasDerivAt (fun u => (((ckRadius x y u ^ 3 : ℝ) : ℂ))⁻¹)
      (-((3 * z : ℝ) : ℂ) / ((ckRadius x y z ^ 5 : ℝ) : ℂ)) z := by
  have h3 : HasDerivAt (fun u => ((ckRadius x y u ^ 3 : ℝ) : ℂ))
      (((3 * z * ckRadius x y z) : ℝ) : ℂ) z := by
    refine HasDerivAt.congr_deriv (((hasDerivAt_ckRadius_z hr).pow 3).ofReal_comp) ?_
    rw [Complex.ofReal_inj]
    field_simp [hr]
    ring
  have hne : ((ckRadius x y z ^ 3 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero 3 hr
  refine HasDerivAt.congr_deriv (h3.inv hne) ?_
  have e2 : (((ckRadius x y z ^ 3 : ℝ) : ℂ)) ^ 2 = ((ckRadius x y z ^ 6 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [e2, div_eq_div_iff (by exact_mod_cast pow_ne_zero 6 hr)
    (by exact_mod_cast pow_ne_zero 5 hr)]
  push_cast
  ring

/-! ### Section derivatives of the dipole mode -/

/-- The angular factor has the componentwise section derivatives
`(0, 0, -1)` in the first coordinate. -/
theorem hasDerivAt_angular_x (x y z : ℝ) (j : Fin 3) :
    HasDerivAt (fun u => ckAngular u y z j) (![0, 0, -(1 : ℂ)] j) x := by
  fin_cases j
  · exact hasDerivAt_const x ((z : ℂ))
  · exact hasDerivAt_const x (Complex.I * (z : ℂ))
  · show HasDerivAt (fun u => -(((u : ℝ) : ℂ) + Complex.I * (y : ℂ))) (-(1 : ℂ)) x
    exact HasDerivAt.congr_deriv
      (HasDerivAt.neg (HasDerivAt.fun_add (hasDerivAt_id x).ofReal_comp
        (hasDerivAt_const x (Complex.I * (y : ℂ))))) (by push_cast; ring)

/-- The angular factor has the componentwise section derivatives
`(0, 0, -i)` in the second coordinate. -/
theorem hasDerivAt_angular_y (x y z : ℝ) (j : Fin 3) :
    HasDerivAt (fun u => ckAngular x u z j) (![0, 0, -(Complex.I)] j) y := by
  fin_cases j
  · exact hasDerivAt_const y ((z : ℂ))
  · exact hasDerivAt_const y (Complex.I * (z : ℂ))
  · show HasDerivAt (fun u => -(((x : ℝ) : ℂ) + Complex.I * ((u : ℝ) : ℂ))) (-(Complex.I)) y
    exact HasDerivAt.congr_deriv
      (HasDerivAt.neg (HasDerivAt.fun_add (hasDerivAt_const y ((x : ℂ)))
        (HasDerivAt.fun_mul (hasDerivAt_const y (Complex.I))
          (hasDerivAt_id y).ofReal_comp))) (by push_cast; ring)

/-- The angular factor has the componentwise section derivatives
`(1, i, 0)` in the third coordinate. -/
theorem hasDerivAt_angular_z (x y z : ℝ) (j : Fin 3) :
    HasDerivAt (fun u => ckAngular x y u j) (![(1 : ℂ), Complex.I, 0] j) z := by
  fin_cases j
  · exact (hasDerivAt_id z).ofReal_comp
  · show HasDerivAt (fun u => Complex.I * ((u : ℝ) : ℂ)) (Complex.I) z
    exact HasDerivAt.congr_deriv (HasDerivAt.fun_mul (hasDerivAt_const z (Complex.I))
      (hasDerivAt_id z).ofReal_comp) (by push_cast; ring)
  · exact hasDerivAt_const z (-((x : ℂ) + Complex.I * (y : ℂ)))

/-- The first-coordinate section derivative of the dipole mode, with the
common factors `k²x sin(kr)`, `g(kr)` and `3x g(kr)` over `r³` and `r⁵`. -/
theorem hasDerivAt_multipole_x (k : ℝ) (x y z t : ℝ) (hr : ckRadius x y z ≠ 0) (j : Fin 3) :
    HasDerivAt (fun u => ckMultipoleField k (u, y, z, t) j)
      (((k ^ 2 * x * Real.sin (k * ckRadius x y z) : ℝ) : ℂ) * ckAngular x y z j /
          ((ckRadius x y z ^ 3 : ℝ) : ℂ) +
        ((ckKernel (k * ckRadius x y z) : ℝ) : ℂ) * (![0, 0, -(1 : ℂ)] : Fin 3 → ℂ) j /
          ((ckRadius x y z ^ 3 : ℝ) : ℂ) -
        ((3 * x * ckKernel (k * ckRadius x y z) : ℝ) : ℂ) * ckAngular x y z j /
          ((ckRadius x y z ^ 5 : ℝ) : ℂ)) x := by
  have hG : HasDerivAt (fun u => ((ckKernel (k * ckRadius u y z) : ℝ) : ℂ))
      (((k ^ 2 * x * Real.sin (k * ckRadius x y z)) : ℝ) : ℂ) x :=
    hasDerivAt_ckKernelComp_x hr
  have hA := hasDerivAt_angular_x x y z j
  have hI := hasDerivAt_ckRadiusPow3_inv_x hr
  have h3 : ((ckRadius x y z ^ 3 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero 3 hr
  have h5 : ((ckRadius x y z ^ 5 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero 5 hr
  simp only [ckMultipoleField, div_eq_mul_inv]
  refine HasDerivAt.congr_deriv (HasDerivAt.fun_mul (HasDerivAt.fun_mul hG hA) hI) ?_
  field_simp
  push_cast
  ring

/-- The second-coordinate section derivative of the dipole mode. -/
theorem hasDerivAt_multipole_y (k : ℝ) (x y z t : ℝ) (hr : ckRadius x y z ≠ 0) (j : Fin 3) :
    HasDerivAt (fun u => ckMultipoleField k (x, u, z, t) j)
      (((k ^ 2 * y * Real.sin (k * ckRadius x y z) : ℝ) : ℂ) * ckAngular x y z j /
          ((ckRadius x y z ^ 3 : ℝ) : ℂ) +
        ((ckKernel (k * ckRadius x y z) : ℝ) : ℂ) * (![0, 0, -(Complex.I)] : Fin 3 → ℂ) j /
          ((ckRadius x y z ^ 3 : ℝ) : ℂ) -
        ((3 * y * ckKernel (k * ckRadius x y z) : ℝ) : ℂ) * ckAngular x y z j /
          ((ckRadius x y z ^ 5 : ℝ) : ℂ)) y := by
  have hG : HasDerivAt (fun u => ((ckKernel (k * ckRadius x u z) : ℝ) : ℂ))
      (((k ^ 2 * y * Real.sin (k * ckRadius x y z)) : ℝ) : ℂ) y :=
    hasDerivAt_ckKernelComp_y hr
  have hA := hasDerivAt_angular_y x y z j
  have hI := hasDerivAt_ckRadiusPow3_inv_y hr
  have h3 : ((ckRadius x y z ^ 3 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero 3 hr
  have h5 : ((ckRadius x y z ^ 5 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero 5 hr
  simp only [ckMultipoleField, div_eq_mul_inv]
  refine HasDerivAt.congr_deriv (HasDerivAt.fun_mul (HasDerivAt.fun_mul hG hA) hI) ?_
  field_simp
  push_cast
  ring

/-- The third-coordinate section derivative of the dipole mode. -/
theorem hasDerivAt_multipole_z (k : ℝ) (x y z t : ℝ) (hr : ckRadius x y z ≠ 0) (j : Fin 3) :
    HasDerivAt (fun u => ckMultipoleField k (x, y, u, t) j)
      (((k ^ 2 * z * Real.sin (k * ckRadius x y z) : ℝ) : ℂ) * ckAngular x y z j /
          ((ckRadius x y z ^ 3 : ℝ) : ℂ) +
        ((ckKernel (k * ckRadius x y z) : ℝ) : ℂ) * (![(1 : ℂ), Complex.I, 0] : Fin 3 → ℂ) j /
          ((ckRadius x y z ^ 3 : ℝ) : ℂ) -
        ((3 * z * ckKernel (k * ckRadius x y z) : ℝ) : ℂ) * ckAngular x y z j /
          ((ckRadius x y z ^ 5 : ℝ) : ℂ)) z := by
  have hG : HasDerivAt (fun u => ((ckKernel (k * ckRadius x y u) : ℝ) : ℂ))
      (((k ^ 2 * z * Real.sin (k * ckRadius x y z)) : ℝ) : ℂ) z :=
    hasDerivAt_ckKernelComp_z hr
  have hA := hasDerivAt_angular_z x y z j
  have hI := hasDerivAt_ckRadiusPow3_inv_z hr
  have h3 : ((ckRadius x y z ^ 3 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero 3 hr
  have h5 : ((ckRadius x y z ^ 5 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero 5 hr
  simp only [ckMultipoleField, div_eq_mul_inv]
  refine HasDerivAt.congr_deriv (HasDerivAt.fun_mul (HasDerivAt.fun_mul hG hA) hI) ?_
  field_simp
  push_cast
  ring


/-! ### The closed-form curl and divergence of the dipole mode -/

/-- On the punctured space the Cartesian curl of the `l = m = 1` magnetic
multipole is the explicit radial-combination field: the first curl identity
underlying the Chandrasekhar–Kendall structure. -/
theorem cartesianCurl_ckMultipoleField (k : ℝ) (s : Spacetime)
    (hr : ckRadius s.1 s.2.1 s.2.2.1 ≠ 0) :
    cartesianCurl (ckMultipoleField k) s = ckCurlMultipoleField k s := by
  obtain ⟨x, y, z, t⟩ := s
  have hx := hasDerivAt_multipole_x k x y z t hr
  have hy := hasDerivAt_multipole_y k x y z t hr
  have hz := hasDerivAt_multipole_z k x y z t hr
  have hR : ((ckRadius x y z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr
  have h3 : ((ckRadius x y z ^ 3 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero 3 hr
  have h5 : ((ckRadius x y z ^ 5 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero 5 hr
  simp [cartesianCurl, spaceTimePartial, coordinateSection, coordinateValue]
  rw [(hy 2).deriv, (hz 1).deriv, (hz 0).deriv, (hx 2).deriv, (hy 0).deriv, (hx 1).deriv]
  funext j
  fin_cases j <;>
    simp only [ckCurlMultipoleField, ckRadialComb, ckCurlAngular, ckConstantCurl,
      ckKernel, ckAngular, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons] <;>
    push_cast <;>
    field_simp [hR] <;>
    ring

/-- The `l = m = 1` magnetic multipole is divergence-free on the punctured
space. -/
theorem cartesianDivergence_ckMultipoleField (k : ℝ) (s : Spacetime)
    (hr : ckRadius s.1 s.2.1 s.2.2.1 ≠ 0) :
    cartesianDivergence (ckMultipoleField k) s = 0 := by
  obtain ⟨x, y, z, t⟩ := s
  have hx := hasDerivAt_multipole_x k x y z t hr
  have hy := hasDerivAt_multipole_y k x y z t hr
  have hz := hasDerivAt_multipole_z k x y z t hr
  have hR : ((ckRadius x y z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr
  simp [cartesianDivergence, spaceTimePartial, coordinateSection, coordinateValue]
  rw [(hx 0).deriv, (hy 1).deriv, (hz 2).deriv]
  simp only [ckAngular, ckKernel, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  push_cast
  field_simp [hR]
  ring

end Qatlib.Papers.KnottedLight08.CurlEigenstate
