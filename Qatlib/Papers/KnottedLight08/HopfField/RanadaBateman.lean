/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.HopfField.RanadaField
public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanPoyntingRays

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The Rañada field in Bateman coordinates

[IrvineBouwmeester2008KnottedLight], Eq. (2),
[DOI](https://doi.org/10.1038/nphys1056), and [Kedia2013TyingKnots], Eqs. (5)–(6),
[DOI](https://doi.org/10.1103/physrevlett.111.150404).
The Rañada electric and magnetic fields combine into the time-reflected,
complex-conjugated Bateman Hopf field with the prefactor `i / (2π)`.
The identity uses the homogeneous formulas, so it applies at the poles
of either affine scalar chart.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.HopfField

open Qatlib.Papers.KnottedLight08.HopfField (cross3)
open Qatlib.Papers.KnotLight13.TorusFamily (radialAux)
open Qatlib.Papers.KnotLight13.TorusFamily
open scoped ComplexConjugate

/-- The complex Riemann–Silberstein field of the Rañada construction. -/
noncomputable def ranadaField (x y z t : ℝ) : Fin 3 → ℂ :=
  fun j => ranadaE x y z t j + Complex.I * ranadaB x y z t j

/-- The common denominator before the Bateman factor of two, at reflected time. -/
private noncomputable def reflectedDen (x y z t : ℝ) : ℂ :=
  (ranadaA x y z t : ℂ) - Complex.I * (t : ℂ)

/-- The real product of the reduced denominator with its complex conjugate. -/
private theorem reflectedDen_mul_conj (x y z t : ℝ) :
    reflectedDen x y z t * conj (reflectedDen x y z t) =
      ((ranadaA x y z t ^ 2 + t ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj]
  congr 1
  simp [reflectedDen, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, pow_two]

/-- The total squared modulus of the magnetic homogeneous pair is the
square of the reduced spacetime denominator's squared norm. -/
private theorem etaSumSq_eq_square (x y z t : ℝ) :
    etaSumSq x y z t = (((ranadaA x y z t ^ 2 + t ^ 2) ^ 2 : ℝ) : ℂ) := by
  rw [etaSumSq, etaPairNormSq, ranadaNormSq_eq]
  congr 1
  unfold ranadaA
  ring

/-- Both homogeneous pairs have the same total squared modulus. -/
private theorem zetaSumSq_eq_square (x y z t : ℝ) :
    zetaSumSq x y z t = (((ranadaA x y z t ^ 2 + t ^ 2) ^ 2 : ℝ) : ℂ) := by
  rw [zetaSumSq, zetaPairNormSq, ← etaPairNormSq, ← etaSumSq, etaSumSq_eq_square]

/-- The Bateman denominator at reflected time is twice the reduced
Rañada denominator. -/
private theorem complexDenominator_reflected (x y z t : ℝ) :
    complexDenominator x y z (-t) = 2 * reflectedDen x y z t := by
  rw [complexDenominator, show radialAux x y z (-t) = 2 * ranadaA x y z t by
    unfold radialAux ranadaA
    ring]
  unfold reflectedDen
  push_cast
  ring

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
/-- Combining the two homogeneous cross products factors out the reduced
denominator and leaves the conjugate Bateman spinor numerator. -/
private theorem ranada_homogeneous_factor (x y z t : ℝ) (j : Fin 3) :
    cross3 (zetaHomog x y z t) (fun k => conj (zetaHomog x y z t k)) j +
        Complex.I * cross3 (etaHomog x y z t) (fun k => conj (etaHomog x y z t k)) j =
      -((ranadaA x y z t ^ 2 + t ^ 2 : ℝ) : ℂ) * reflectedDen x y z t ^ 3 *
        conj (spinorField (alphaCommonFactor z (-t)) (betaReducedNumerator x y) j) := by
  unfold cross3 etaHomog zetaHomog etaNum etaDen zetaNum zetaDen
    etaNumGrad etaDenGrad zetaNumGrad zetaDenGrad
    etaNumX etaNumY etaNumZ etaDenX etaDenY etaDenZ
    zetaNumX zetaNumY zetaNumZ zetaDenX zetaDenY zetaDenZ
    reflectedDen spinorField alphaCommonFactor betaReducedNumerator
    ranadaP ranadaQ ranadaR ranadaS
  generalize ha : ranadaA x y z t = a
  have hA : z ^ 2 + x ^ 2 + y ^ 2 - t ^ 2 - 2 * a + 1 = 0 := by
    rw [← ha]
    unfold ranadaA
    ring
  fin_cases j <;> apply Complex.ext <;>
    simp [pow_succ, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      -Complex.ofReal_pow, -Complex.ofReal_mul, -Complex.ofReal_add, -Complex.ofReal_sub]
  -- Each normalized component is a multiple of the same quadratic relation.
  · linear_combination ((3 * a - 2) * t ^ 4
      + (6 * a * z - 2 * z - 2 * x * y) * t ^ 3
      + (4 * a * z ^ 2 + 4 * a * y ^ 2 + 2 * a ^ 3) * t ^ 2
      + (2 * a ^ 3 * z + 2 * a ^ 2 * z + 2 * a ^ 2 * x * y) * t
      + (-a ^ 5 + 2 * a ^ 4)) * hA
  · linear_combination (-t ^ 5
      - 2 * z * t ^ 4
      + (-2 * z ^ 2 - 2 * y ^ 2 + 2 * a ^ 2 - 4 * a) * t ^ 3
      + (4 * a ^ 2 * z - 4 * a * z - 4 * a * x * y) * t ^ 2
      + (2 * a ^ 2 * z ^ 2 + 2 * a ^ 2 * y ^ 2 + 3 * a ^ 4 - 4 * a ^ 3) * t
      + 2 * a ^ 4 * z) * hA
  · linear_combination (t ^ 5
      + 2 * z * t ^ 4
      + (2 * z ^ 2 + 2 * x ^ 2 - 2 * a ^ 2 + 4 * a) * t ^ 3
      + (-4 * a ^ 2 * z + 4 * a * z - 4 * a * x * y) * t ^ 2
      + (-2 * a ^ 2 * z ^ 2 - 2 * a ^ 2 * x ^ 2 - 3 * a ^ 4 + 4 * a ^ 3) * t
      - 2 * a ^ 4 * z) * hA
  · linear_combination ((3 * a - 2) * t ^ 4
      + (6 * a * z - 2 * z + 2 * x * y) * t ^ 3
      + (4 * a * z ^ 2 + 4 * a * x ^ 2 + 2 * a ^ 3) * t ^ 2
      + (2 * a ^ 3 * z + 2 * a ^ 2 * z - 2 * a ^ 2 * x * y) * t
      + (-a ^ 5 + 2 * a ^ 4)) * hA
  · linear_combination (-2 * y * t ^ 4
      + (-2 * y * z - 6 * a * x + 2 * x) * t ^ 3
      + (-4 * a * x * z + 4 * a ^ 2 * y - 4 * a * y) * t ^ 2
      + (2 * a ^ 2 * y * z - 2 * a ^ 3 * x - 2 * a ^ 2 * x) * t
      + 2 * a ^ 4 * y) * hA
  · linear_combination (2 * x * t ^ 4
      + (2 * x * z - 6 * a * y + 2 * y) * t ^ 3
      + (-4 * a * y * z - 4 * a ^ 2 * x + 4 * a * x) * t ^ 2
      + (-2 * a ^ 2 * x * z - 2 * a ^ 3 * y - 2 * a ^ 2 * y) * t
      - 2 * a ^ 4 * x) * hA

/-- The literal Rañada field of Eq. (2) equals the reflected and
conjugated base Bateman field, with its exact normalization. -/
theorem ranadaField_eq_bateman (x y z t : ℝ) (j : Fin 3) :
    ranadaField x y z t j =
      (Complex.I / (2 * (Real.pi : ℂ))) * conj (rationalField x y z (-t) j) := by
  let d : ℂ := ((ranadaA x y z t ^ 2 + t ^ 2 : ℝ) : ℂ)
  let w := reflectedDen x y z t
  let p := conj (spinorField (alphaCommonFactor z (-t)) (betaReducedNumerator x y) j)
  have hd : d ≠ 0 := Complex.ofReal_ne_zero.mpr (ranadaA_sq_add_t_sq_pos x y z t).ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hdw : w * conj w = d := reflectedDen_mul_conj x y z t
  have hw : conj w ≠ 0 := by
    intro h
    rw [h, mul_zero] at hdw
    exact hd hdw.symm
  have hw' : w = d / conj w := (eq_div_iff hw).2 hdw
  have hE : zetaSumSq x y z t = d ^ 2 := by
    rw [zetaSumSq_eq_square, Complex.ofReal_pow]
  have hB : etaSumSq x y z t = d ^ 2 := by
    rw [etaSumSq_eq_square, Complex.ofReal_pow]
  have hI : -(1 : ℂ) / Complex.I = Complex.I := by
    apply (div_eq_iff Complex.I_ne_zero).2
    exact Complex.I_mul_I.symm
  rw [rationalField_eq_spinorField, complexDenominator_reflected, conj_mul', conj_div', conj_pow', conj_mul']
  simp only [map_ofNat]
  change ranadaField x y z t j = Complex.I / (2 * (Real.pi : ℂ)) * (4 / (2 * conj w) ^ 3 * p)
  calc
    _ = (1 / (4 * (Real.pi : ℂ) * Complex.I)) *
        (cross3 (zetaHomog x y z t) (fun k => conj (zetaHomog x y z t k)) j +
          Complex.I * cross3 (etaHomog x y z t) (fun k => conj (etaHomog x y z t k)) j) /
        (d ^ 2) ^ 2 := by
      rw [ranadaField, ranadaE, ranadaB, hE, hB]
      ring
    _ = (1 / (4 * (Real.pi : ℂ) * Complex.I)) * (-d * w ^ 3 * p) / (d ^ 2) ^ 2 := by
      rw [ranada_homogeneous_factor]
    _ = (-(1 : ℂ) / Complex.I) * (4 / (2 * (Real.pi : ℂ) * (2 * conj w) ^ 3)) * p := by
      conv_lhs => rw [hw']
      field_simp [hd, hw, hπ, Complex.I_ne_zero]
      ring
    _ = _ := by rw [hI]; ring

end Qatlib.Papers.KnottedLight08.HopfField
