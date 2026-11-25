/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.HopfField.RanadaMaxwell

import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# A global magnetic vector potential at the initial time

[IrvineBouwmeester2008KnottedLight], Eq. (2),
[DOI](https://doi.org/10.1038/nphys1056).
At time zero the homogeneous Rañada magnetic field equals a polynomial
vector divided by the cube of the stereographic denominator. The same
vector divided by the square of the denominator, with the appropriate
constant, gives a smooth magnetic vector potential. Its verified curl is
the actual Rañada magnetic field, including at poles of the affine scalar.
The magnetic helicity density in this gauge is a radial rational function.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.HopfField

open Qatlib.Papers.KnottedLight08.HopfField (dot3)
open Qatlib.Papers.KnotLight13.TorusFamily (radialAux)
open Qatlib.Papers.KnotLight13.TorusFamily
open scoped ComplexConjugate

/-- The real initial stereographic denominator. -/
noncomputable def hopfScale (x y z : ℝ) : ℝ := x ^ 2 + y ^ 2 + z ^ 2 + 1

/-- The polynomial direction of the initial magnetic field in Cartesian coordinates. -/
noncomputable def initialMagneticDirection (x y z : ℝ) : Fin 3 → ℝ :=
  ![1 + x ^ 2 - y ^ 2 - z ^ 2, 2 * (x * y - z), 2 * (x * z + y)]

/-- The stereographic denominator has no real zeros. -/
theorem hopf_scale_pos (x y z : ℝ) : 0 < hopfScale x y z := by
  unfold hopfScale
  positivity

/-- The squared length of the polynomial direction is the squared denominator. -/
theorem initial_magnetic_direction_length (x y z : ℝ) :
    dot3 (initialMagneticDirection x y z) (initialMagneticDirection x y z) =
      hopfScale x y z ^ 2 := by
  simp [dot3, initialMagneticDirection, hopfScale]
  ring

/-- The initial Bateman denominator is the real stereographic denominator. -/
private theorem initial_denominator (x y z : ℝ) :
    complexDenominator x y z 0 = (hopfScale x y z : ℂ) := by
  simp [complexDenominator, radialAux, hopfScale]

/-- The real part of the initial Bateman field is the negative polynomial
direction with radial weight four over the cubed denominator. -/
private theorem rational_field_initial_re (x y z : ℝ) (j : Fin 3) :
    (rationalField x y z 0 j).re =
      -4 * initialMagneticDirection x y z j / hopfScale x y z ^ 3 := by
  rw [rationalField_eq_spinorField, initial_denominator]
  have hc : (4 : ℂ) / (hopfScale x y z : ℂ) ^ 3 = ((4 / hopfScale x y z ^ 3 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  fin_cases j <;>
    simp [initialMagneticDirection, spinorField, alphaCommonFactor, betaReducedNumerator,
      pow_two, Complex.mul_re, Complex.mul_im] <;> ring

/-- With the normalization of Eq. (2), the initial magnetic field is
the negative polynomial direction times two over the cubed denominator
and pi. -/
theorem ranada_b_initial_re (x y z : ℝ) (j : Fin 3) :
    (ranadaB x y z 0 j).re =
      -2 * initialMagneticDirection x y z j / (Real.pi * hopfScale x y z ^ 3) := by
  have h := congrArg Complex.im (ranadaField_eq_bateman x y z 0 j)
  have hκ : (Complex.I / (2 * (Real.pi : ℂ))) =
      Complex.I * ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hκ] at h
  simp only [ranadaField, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    ranadaE_im, Complex.ofReal_im, Complex.ofReal_re, zero_mul, one_mul, zero_add,
    neg_zero, Complex.conj_re, Complex.mul_re, sub_zero] at h
  rw [h, rational_field_initial_re]
  ring

/-- A global real magnetic vector potential for the initial Rañada field. -/
noncomputable def ranadaInitialPotential (x y z : ℝ) (j : Fin 3) : ℝ :=
  (-1 / (2 * Real.pi)) * (initialMagneticDirection x y z j / hopfScale x y z ^ 2)

/-- Every component of the potential is smooth on the whole Cartesian
slice. The unused time coordinate supplies a constant extension. -/
theorem contDiff_ranada_initial_potential (j : Fin 3) :
    ContDiff ℝ ⊤ (fun s : Spacetime => ranadaInitialPotential s.1 s.2.1 s.2.2.1 j) := by
  have hN : ContDiff ℝ ⊤ (fun s : Spacetime =>
      initialMagneticDirection s.1 s.2.1 s.2.2.1 j) := by
    fin_cases j <;> simp [initialMagneticDirection] <;> fun_prop
  have hS : ContDiff ℝ ⊤ (fun s : Spacetime => hopfScale s.1 s.2.1 s.2.2.1) := by
    unfold hopfScale
    fun_prop
  exact contDiff_const.mul (hN.div (hS.pow 2)
    (fun s => pow_ne_zero 2 (hopf_scale_pos s.1 s.2.1 s.2.2.1).ne'))

/-- The rows are vector components and the columns are Cartesian coordinates
including the unused time coordinate. -/
private noncomputable def directionPartials (x y z : ℝ) (j : Fin 3) (i : Fin 4) : ℝ :=
  ![![2 * x, -(2 * y), -(2 * z), 0], ![2 * y, 2 * x, -2, 0],
    ![2 * z, 2, 2 * x, 0]] j i

/-- The coordinate square has derivative twice the coordinate. -/
private theorem hasDerivAt_coordinate_square (x : ℝ) :
    HasDerivAt (fun u : ℝ => u ^ 2) (2 * x) x := by
  convert (hasDerivAt_id x).mul (hasDerivAt_id x) using 1
  · funext u
    exact pow_two u
  · simp [two_mul]

/-- The polynomial component has the indicated derivative along each
actual Cartesian section. -/
private theorem hasDerivAt_direction_section (s : Spacetime) (j : Fin 3) (i : Fin 4) :
    HasDerivAt (fun u =>
      initialMagneticDirection (coordinateSection s i u).1 (coordinateSection s i u).2.1
        (coordinateSection s i u).2.2.1 j)
      (directionPartials s.1 s.2.1 s.2.2.1 j i) (coordinateValue s i) := by
  rcases s with ⟨x, y, z, t⟩
  fin_cases j <;> fin_cases i
  · change HasDerivAt (fun u => 1 + u ^ 2 - y ^ 2 - z ^ 2) (2 * x) x
    exact (((hasDerivAt_coordinate_square x).const_add 1).sub_const (y ^ 2)).sub_const (z ^ 2)
  · change HasDerivAt (fun u => 1 + x ^ 2 - u ^ 2 - z ^ 2) (-(2 * y)) y
    exact ((hasDerivAt_coordinate_square y).const_sub (1 + x ^ 2)).sub_const (z ^ 2)
  · change HasDerivAt (fun u => 1 + x ^ 2 - y ^ 2 - u ^ 2) (-(2 * z)) z
    exact (hasDerivAt_coordinate_square z).const_sub (1 + x ^ 2 - y ^ 2)
  · change HasDerivAt (fun _ : ℝ => 1 + x ^ 2 - y ^ 2 - z ^ 2) 0 t
    exact hasDerivAt_const t (1 + x ^ 2 - y ^ 2 - z ^ 2)
  · change HasDerivAt (fun u => 2 * (u * y - z)) (2 * y) x
    simpa using (((hasDerivAt_id x).mul_const y).sub_const z).const_mul 2
  · change HasDerivAt (fun u => 2 * (x * u - z)) (2 * x) y
    simpa using (((hasDerivAt_id y).const_mul x).sub_const z).const_mul 2
  · change HasDerivAt (fun u => 2 * (x * y - u)) (-2) z
    simpa using ((hasDerivAt_id z).const_sub (x * y)).const_mul 2
  · change HasDerivAt (fun _ : ℝ => 2 * (x * y - z)) 0 t
    exact hasDerivAt_const t (2 * (x * y - z))
  · change HasDerivAt (fun u => 2 * (u * z + y)) (2 * z) x
    simpa using (((hasDerivAt_id x).mul_const z).add_const y).const_mul 2
  · change HasDerivAt (fun u => 2 * (x * z + u)) 2 y
    simpa using ((hasDerivAt_id y).const_add (x * z)).const_mul 2
  · change HasDerivAt (fun u => 2 * (x * u + y)) (2 * x) z
    simpa using (((hasDerivAt_id z).const_mul x).add_const y).const_mul 2
  · change HasDerivAt (fun _ : ℝ => 2 * (x * z + y)) 0 t
    exact hasDerivAt_const t (2 * (x * z + y))

/-- The derivative of the positive denominator along each Cartesian section. -/
private theorem hasDerivAt_scale_section (s : Spacetime) (i : Fin 4) :
    HasDerivAt (fun u =>
      hopfScale (coordinateSection s i u).1 (coordinateSection s i u).2.1
        (coordinateSection s i u).2.2.1)
      (![2 * s.1, 2 * s.2.1, 2 * s.2.2.1, 0] i) (coordinateValue s i) := by
  rcases s with ⟨x, y, z, t⟩
  fin_cases i
  · change HasDerivAt (fun u => u ^ 2 + y ^ 2 + z ^ 2 + 1) (2 * x) x
    exact (((hasDerivAt_coordinate_square x).add_const (y ^ 2)).add_const (z ^ 2)).add_const 1
  · change HasDerivAt (fun u => x ^ 2 + u ^ 2 + z ^ 2 + 1) (2 * y) y
    exact (((hasDerivAt_coordinate_square y).const_add (x ^ 2)).add_const (z ^ 2)).add_const 1
  · change HasDerivAt (fun u => x ^ 2 + y ^ 2 + u ^ 2 + 1) (2 * z) z
    exact ((hasDerivAt_coordinate_square z).const_add (x ^ 2 + y ^ 2)).add_const 1
  · change HasDerivAt (fun _ : ℝ => x ^ 2 + y ^ 2 + z ^ 2 + 1) 0 t
    exact hasDerivAt_const t (x ^ 2 + y ^ 2 + z ^ 2 + 1)

/-- Quotient differentiation of a component divided by the squared
stereographic denominator, expressed over the cubed denominator. -/
private theorem hasDerivAt_normalized_component (n d : ℝ → ℝ) (u n' d' : ℝ)
    (hn : HasDerivAt n n' u) (hd : HasDerivAt d d' u) (h0 : d u ≠ 0) :
    HasDerivAt (fun v => (-1 / (2 * Real.pi)) * (n v / d v ^ 2))
      ((-1 / (2 * Real.pi)) * ((n' * d u - 2 * d' * n u) / d u ^ 3)) u := by
  have hd2 : HasDerivAt (fun v => d v ^ 2) (2 * d' * d u) u := by
    convert hd.mul hd using 1
    · funext v
      exact pow_two (d v)
    · ring
  convert (hn.div hd2 (pow_ne_zero 2 h0)).const_mul (-1 / (2 * Real.pi)) using 1
  field_simp [h0, Real.pi_ne_zero]

/-- The real value of a coordinate derivative of the initial potential. -/
private noncomputable def initialPotentialDerivative (s : Spacetime) (j : Fin 3) (i : Fin 4) : ℝ :=
  (-1 / (2 * Real.pi)) *
    ((directionPartials s.1 s.2.1 s.2.2.1 j i * hopfScale s.1 s.2.1 s.2.2.1 -
      2 * (![2 * s.1, 2 * s.2.1, 2 * s.2.2.1, 0] i) *
        initialMagneticDirection s.1 s.2.1 s.2.2.1 j) / hopfScale s.1 s.2.1 s.2.2.1 ^ 3)

/-- The actual partial derivative of the potential, using real derivatives
embedded in the complex Cartesian curl from the Maxwell development. -/
private theorem initial_potential_partial (s : Spacetime) (j : Fin 3) (i : Fin 4) :
    spaceTimePartial (fun w => (ranadaInitialPotential w.1 w.2.1 w.2.2.1 j : ℂ)) s i =
      (initialPotentialDerivative s j i : ℂ) := by
  have h0 : hopfScale (coordinateSection s i (coordinateValue s i)).1
      (coordinateSection s i (coordinateValue s i)).2.1
      (coordinateSection s i (coordinateValue s i)).2.2.1 ≠ 0 := by
    rw [coordinateSection_at]
    exact (hopf_scale_pos s.1 s.2.1 s.2.2.1).ne'
  have h := hasDerivAt_normalized_component _ _ _ _ _
    (hasDerivAt_direction_section s j i) (hasDerivAt_scale_section s i) h0
  unfold spaceTimePartial ranadaInitialPotential initialPotentialDerivative
  simpa only [coordinateSection_at] using h.ofReal_comp.deriv

/-- The Cartesian curl of the initial potential equals the actual
magnetic field at time zero, including where the affine chart has poles. -/
theorem curl_ranada_initial_potential (x y z : ℝ) (j : Fin 3) :
    cartesianCurl (fun s j => (ranadaInitialPotential s.1 s.2.1 s.2.2.1 j : ℂ))
      (x, y, z, 0) j = ranadaB x y z 0 j := by
  have h (k : Fin 3) (i : Fin 4) :
      spaceTimePartial (fun s => (ranadaInitialPotential s.1 s.2.1 s.2.2.1 k : ℂ))
        (x, y, z, 0) i = (initialPotentialDerivative (x, y, z, 0) k i : ℂ) :=
    initial_potential_partial _ _ _
  have hS : hopfScale x y z ≠ 0 := (hopf_scale_pos x y z).ne'
  unfold cartesianCurl
  fin_cases j
  · change spaceTimePartial _ _ 1 - spaceTimePartial _ _ 2 = ranadaB x y z 0 0
    rw [h 2 1, h 1 2, ← Complex.ofReal_sub]
    apply Complex.ext
    · rw [Complex.ofReal_re, ranada_b_initial_re]
      simp [initialPotentialDerivative, initialMagneticDirection, directionPartials]
      field_simp [hS, Real.pi_ne_zero]
      unfold hopfScale
      ring
    · simp only [Complex.ofReal_im, ranadaB_im]
  · change spaceTimePartial _ _ 2 - spaceTimePartial _ _ 0 = ranadaB x y z 0 1
    rw [h 0 2, h 2 0, ← Complex.ofReal_sub]
    apply Complex.ext
    · rw [Complex.ofReal_re, ranada_b_initial_re]
      simp [initialPotentialDerivative, initialMagneticDirection, directionPartials]
      field_simp [hS, Real.pi_ne_zero]
      unfold hopfScale
      ring
    · simp only [Complex.ofReal_im, ranadaB_im]
  · change spaceTimePartial _ _ 0 - spaceTimePartial _ _ 1 = ranadaB x y z 0 2
    rw [h 1 0, h 0 1, ← Complex.ofReal_sub]
    apply Complex.ext
    · rw [Complex.ofReal_re, ranada_b_initial_re]
      simp [initialPotentialDerivative, initialMagneticDirection, directionPartials]
      field_simp [hS, Real.pi_ne_zero]
      unfold hopfScale
      ring
    · simp only [Complex.ofReal_im, ranadaB_im]

/-- In this smooth gauge the initial helicity density is the exact radial
function whose integral gives the magnetic helicity. -/
theorem ranada_initial_helicity_density (x y z : ℝ) :
    dot3 (ranadaInitialPotential x y z) (fun j => (ranadaB x y z 0 j).re) =
      1 / (Real.pi ^ 2 * hopfScale x y z ^ 3) := by
  let V := initialMagneticDirection x y z
  let S := hopfScale x y z
  have hd := initial_magnetic_direction_length x y z
  change dot3 V V = S ^ 2 at hd
  simp only [dot3] at hd
  simp only [dot3, ranadaInitialPotential, ranada_b_initial_re]
  change (-1 / (2 * Real.pi)) * (V 0 / S ^ 2) * (-2 * V 0 / (Real.pi * S ^ 3)) +
      (-1 / (2 * Real.pi)) * (V 1 / S ^ 2) * (-2 * V 1 / (Real.pi * S ^ 3)) +
      (-1 / (2 * Real.pi)) * (V 2 / S ^ 2) * (-2 * V 2 / (Real.pi * S ^ 3)) = _
  have hS : S ≠ 0 := (hopf_scale_pos x y z).ne'
  change _ = 1 / (Real.pi ^ 2 * S ^ 3)
  field_simp [hS, Real.pi_ne_zero]
  linear_combination hd

end Qatlib.Papers.KnottedLight08.HopfField
