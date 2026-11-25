/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.HopfField.RanadaBateman
public import Qatlib.Papers.KnotLight13.TorusFamily.RationalPowerMaxwell

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.Ring

/-!
# The source-free Maxwell equations for the Rañada field

[IrvineBouwmeester2008KnottedLight], Eq. (2),
[DOI](https://doi.org/10.1038/nphys1056).
The exact relation between the Rañada and Bateman solutions transfers
smoothness and the four source-free Maxwell equations to the Rañada
field on all of real spacetime. Complex conjugation reverses the sign
of the imaginary unit, and time reflection reverses the time derivative.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.HopfField

open Qatlib.Papers.KnotLight13.TorusFamily
open scoped ComplexConjugate

/-- The Rañada field as a function of a Cartesian spacetime tuple. -/
noncomputable def ranadaFieldAt (s : Spacetime) : Fin 3 → ℂ :=
  ranadaField s.1 s.2.1 s.2.2.1 s.2.2.2

/-- The reference Bateman field in the same tuple coordinates. -/
private noncomputable def batemanFieldAt (s : Spacetime) : Fin 3 → ℂ :=
  rationalField s.1 s.2.1 s.2.2.1 s.2.2.2
local notation "κ" => (Complex.I / (2 * (Real.pi : ℂ)))

/-- Componentwise complex conjugation and multiplication by the fixed
normalization commute with differentiation in a real variable. -/
private theorem deriv_scaled_conj {f : ℝ → ℂ} {s : ℝ} (h : DifferentiableAt ℝ f s) :
    deriv (fun u => κ * conj (f u)) s = κ * conj (deriv f s) :=
  ((Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt s h.hasDerivAt).const_mul
    κ).deriv

/-- A Cartesian section of the Bateman field is differentiable. -/
private theorem differentiable_bateman_section (s : Spacetime) (i : Fin 4) (j : Fin 3) :
    Differentiable ℝ (fun u => batemanFieldAt (coordinateSection s i u) j) := by
  have hs : Differentiable ℝ (coordinateSection s i) := by
    change Differentiable ℝ (fun u => coordinateSection s i u)
    unfold coordinateSection
    fin_cases i <;> simp <;> fun_prop
  exact ((contDiff_rationalField j).differentiable (by simp)).comp hs

/-- Time reflection contributes a minus sign only in the time section. -/
private theorem ranada_partial_eq (x y z t : ℝ) (i : Fin 4) (j : Fin 3) :
    spaceTimePartial (fun s => ranadaFieldAt s j) (x, y, z, t) i =
      if i = 3 then -(κ * conj (spaceTimePartial (fun s => batemanFieldAt s j) (x, y, z, -t) i))
      else κ * conj (spaceTimePartial (fun s => batemanFieldAt s j) (x, y, z, -t) i) := by
  unfold spaceTimePartial
  simp_rw [ranadaFieldAt, ranadaField_eq_bateman]
  fin_cases i
  · exact deriv_scaled_conj (differentiable_bateman_section (x, y, z, -t) 0 j x)
  · exact deriv_scaled_conj (differentiable_bateman_section (x, y, z, -t) 1 j y)
  · exact deriv_scaled_conj (differentiable_bateman_section (x, y, z, -t) 2 j z)
  · change deriv (fun u => κ * conj (rationalField x y z (-u) j)) t =
      -(κ * conj (deriv (fun u => rationalField x y z u j) (-t)))
    have hAt : HasDerivAt (fun u => rationalField x y z u j)
        (deriv (fun u => rationalField x y z u j) (-t)) (-t) :=
      (differentiable_bateman_section (x, y, z, -t) 3 j (-t)).hasDerivAt
    have hRev : HasDerivAt (fun u => rationalField x y z (-u) j)
        (-(deriv (fun u => rationalField x y z u j) (-t))) t := by
      simpa [Function.comp_def] using hAt.scomp t (hasDerivAt_id t).neg
    rw [deriv_scaled_conj hRev.differentiableAt, hRev.deriv, conj_neg', mul_neg]

/-- Every component of the Rañada field is smooth, including at poles of
the scalar charts. -/
theorem contDiff_ranadaField (j : Fin 3) :
    ContDiff ℝ ⊤ (fun s : Spacetime => ranadaFieldAt s j) := by
  have hRev : ContDiff ℝ ⊤ (fun s : Spacetime => (s.1, s.2.1, s.2.2.1, -s.2.2.2)) := by
    fun_prop
  have hF := (contDiff_rationalField j).comp hRev
  have hConj : ContDiff ℝ ⊤ (fun s : Spacetime =>
      conj (rationalField s.1 s.2.1 s.2.2.1 (-s.2.2.2) j)) :=
    Complex.conjCLE.contDiff.comp hF
  simp_rw [ranadaFieldAt, ranadaField_eq_bateman]
  exact contDiff_const.mul hConj

/-- Spatial curl commutes with conjugation and the constant
normalization, with all quantities evaluated at reflected time. -/
private theorem ranada_curl_eq (x y z t : ℝ) (j : Fin 3) :
    cartesianCurl ranadaFieldAt (x, y, z, t) j = κ * conj (fieldCurl x y z (-t) j) := by
  have h : ∀ i : Fin 4, i ≠ 3 → ∀ k : Fin 3,
      spaceTimePartial (fun s => ranadaFieldAt s k) (x, y, z, t) i =
        κ * conj (spaceTimePartial (fun s => batemanFieldAt s k) (x, y, z, -t) i) :=
    fun i hi k => by rw [ranada_partial_eq, ite_eq_right hi]
  unfold cartesianCurl fieldCurl
  fin_cases j
  · change spaceTimePartial (fun s => ranadaFieldAt s 2) (x, y, z, t) 1 -
      spaceTimePartial (fun s => ranadaFieldAt s 1) (x, y, z, t) 2 = _
    rw [h 1 (by decide), h 2 (by decide)]
    exact (mul_sub _ _ _).symm.trans (congrArg (κ * ·) (conj_sub' _ _).symm)
  · change spaceTimePartial (fun s => ranadaFieldAt s 0) (x, y, z, t) 2 -
      spaceTimePartial (fun s => ranadaFieldAt s 2) (x, y, z, t) 0 = _
    rw [h 2 (by decide), h 0 (by decide)]
    exact (mul_sub _ _ _).symm.trans (congrArg (κ * ·) (conj_sub' _ _).symm)
  · change spaceTimePartial (fun s => ranadaFieldAt s 1) (x, y, z, t) 0 -
      spaceTimePartial (fun s => ranadaFieldAt s 0) (x, y, z, t) 1 = _
    rw [h 0 (by decide), h 1 (by decide)]
    exact (mul_sub _ _ _).symm.trans (congrArg (κ * ·) (conj_sub' _ _).symm)

/-- The true Cartesian curl of the Rañada field is `i` times its true
time derivative. -/
theorem maxwell_ranadaField (x y z t : ℝ) (j : Fin 3) :
    cartesianCurl ranadaFieldAt (x, y, z, t) j =
      Complex.I * spaceTimePartial (fun s => ranadaFieldAt s j) (x, y, z, t) 3 := by
  rw [ranada_curl_eq, maxwell_rational_field, ranada_partial_eq, ite_eq_left rfl,
    conj_mul', Complex.conj_I]
  change κ * (-Complex.I * conj (fieldTimeDeriv x y z (-t) j)) =
    Complex.I * (-(κ * conj (fieldTimeDeriv x y z (-t) j)))
  ring

/-- The true Cartesian divergence of the Rañada field vanishes. -/
theorem ranadaField_divergence_free (x y z t : ℝ) :
    cartesianDivergence ranadaFieldAt (x, y, z, t) = 0 := by
  unfold cartesianDivergence
  rw [ranada_partial_eq, ite_eq_right (by decide : (0 : Fin 4) ≠ 3),
    ranada_partial_eq, ite_eq_right (by decide : (1 : Fin 4) ≠ 3),
    ranada_partial_eq, ite_eq_right (by decide : (2 : Fin 4) ≠ 3),
    ← mul_add, ← mul_add, ← conj_add', ← conj_add']
  change κ * conj (deriv (fun u => rationalField u y z (-t) 0) x +
    deriv (fun u => rationalField x u z (-t) 1) y +
    deriv (fun u => rationalField x y u (-t) 2) z) = 0
  rw [rational_field_divergence_free]
  simp

end Qatlib.Papers.KnottedLight08.HopfField
