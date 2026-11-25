/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.RationalLineGeometry
public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanPoyntingRays

/-! Regression consumers for the field-line geometry of the rational Bateman
field. The witness point (1, 2, 3, 4) is nondegenerate: the real profile
polynomial evaluates to 2800, the cross and product-gradient numerators are
evaluated against independently computed values, the `HasDerivAt` derivative
bridge for the product `α * β` is instantiated, and both level-surface
orthogonality theorems are specialized. The spatial trefoil witness
instantiates the initial topological parametrization and its transport to
a nonzero time. -/

@[expose] public section
set_option autoImplicit false

open Qatlib.Papers.KnotLight13.TorusFamily (radialAux rationalAlpha rationalBeta
  pairDenominator pair_denominator_pos)
open Qatlib.Papers.KnottedLight08.HopfField (cross3 dot3)
open Qatlib.Papers.KnotLight13.TorusFamily

-- The real profile polynomial evaluates explicitly to 2800 at the witness.
example : lineGeometryProfile 1 2 3 4 = 2800 := by
  norm_num [lineGeometryProfile]

-- The first cross-numerator entry evaluates against the independently
-- computed value.
example :
    cross3 (alphaGradientNumerators 1 2 3 4) (betaGradientNumerators 1 2 3 4) 0 =
      ((-76 : ℂ) + Complex.I * 88) := by
  apply Complex.ext
  · simp [cross3, alphaGradientNumerators, betaGradientNumerators,
      alphaXNumerator, alphaYNumerator, alphaZNumerator, betaXNumerator,
      betaYNumerator, betaZNumerator, alphaCommonFactor, betaReducedNumerator,
      complexDenominator, radialAux, Complex.mul_re, Complex.mul_im]
    norm_num
  · simp [cross3, alphaGradientNumerators, betaGradientNumerators,
      alphaXNumerator, alphaYNumerator, alphaZNumerator, betaXNumerator,
      betaYNumerator, betaZNumerator, alphaCommonFactor, betaReducedNumerator,
      complexDenominator, radialAux, Complex.mul_re, Complex.mul_im]
    norm_num

-- The product-gradient numerator entries evaluate against the independently
-- computed values.
example :
    productGradientNumerators 1 2 3 4 0 =
      ((-102 : ℂ) - Complex.I * 116) := by
  apply Complex.ext
  · simp [productGradientNumerators, betaNumerator, alphaNumerator,
      alphaGradientNumerators, betaGradientNumerators,
      alphaXNumerator, betaXNumerator, alphaCommonFactor, betaReducedNumerator,
      complexDenominator, radialAux, Complex.mul_re, Complex.mul_im]
    norm_num
  · simp [productGradientNumerators, betaNumerator, alphaNumerator,
      alphaGradientNumerators, betaGradientNumerators,
      alphaXNumerator, betaXNumerator, alphaCommonFactor, betaReducedNumerator,
      complexDenominator, radialAux, Complex.mul_re, Complex.mul_im]
    norm_num

example :
    productGradientNumerators 1 2 3 4 2 =
      ((-76 : ℂ) - Complex.I * 108) := by
  apply Complex.ext
  · simp [productGradientNumerators, betaNumerator, alphaNumerator,
      alphaGradientNumerators, betaGradientNumerators,
      alphaZNumerator, betaZNumerator, alphaCommonFactor, betaReducedNumerator,
      complexDenominator, radialAux, Complex.mul_re, Complex.mul_im]
    norm_num
  · simp [productGradientNumerators, betaNumerator, alphaNumerator,
      alphaGradientNumerators, betaGradientNumerators,
      alphaZNumerator, betaZNumerator, alphaCommonFactor, betaReducedNumerator,
      complexDenominator, radialAux, Complex.mul_re, Complex.mul_im]
    norm_num

-- The z-partial of the product `α * β` at the witness point is its numerator
-- over the cube of the common denominator, via the derivative bridge.
example :
    deriv (fun z' => rationalAlpha 1 2 z' 4 * rationalBeta 1 2 z' 4) 3 =
      productGradientNumerators 1 2 3 4 2 / complexDenominator 1 2 3 4 ^ 3 :=
  (hasDerivAt_rationalAB_z 1 2 3 4).deriv

-- The field is orthogonal to the product gradient, at the witness point as
-- everywhere.
example : dot3 (rationalField 1 2 3 4) (productGradient 1 2 3 4) = 0 :=
  field_dot_productGradient 1 2 3 4

-- The conjugate dot product is real and evaluates to the profile over the
-- cube of the pair denominator: 2800 / 65 ^ 3.
example :
    dot3 (rationalField 1 2 3 4)
        (fun j => (starRingEnd ℂ) (productGradient 1 2 3 4 j)) =
      ((2800 / 274625 : ℝ) : ℂ) := by
  rw [field_dot_conj_productGradient]
  norm_num [lineGeometryProfile, pairDenominator, radialAux]

-- Both level-surface orthogonality relations at the witness point.
example :
    dot3 (fun j => (rationalField 1 2 3 4 j).im)
        (fun j => (productGradient 1 2 3 4 j).re) = 0 :=
  magnetic_field_line_level 1 2 3 4

example :
    dot3 (fun j => (rationalField 1 2 3 4 j).re)
        (fun j => (productGradient 1 2 3 4 j).im) = 0 :=
  electric_field_line_level 1 2 3 4

/-- The initial trefoil locus has the topology of its standard phase circle. -/
example : Nonempty (Circle ≃ₜ ↥(initialSpatialKnot 2 3)) := by
  have hp : (0 : ℕ) < 2 := by decide
  have hq : (0 : ℕ) < 3 := by decide
  obtain ⟨a, b, ha, hb, hs, he⟩ := exists_balanced_torus_radii hp hq
  exact ⟨initialSpatialKnotHomeomorph hp hq (by decide) ha hb hs he⟩

/-- The ray from the origin moves along the negative third axis. -/
example : batemanRay 2 (0, 0, 0) = (0, 0, -2) := by
  norm_num [batemanRay]

/-- The whole trefoil zero locus is carried to its time-two zero locus. -/
example : batemanSliceHomeomorph 2 '' initialSpatialKnot 2 3 = spatialKnotAt 2 3 2 :=
  batemanSliceHomeomorph_image_initialSpatialKnot 2 3 2

/-- The ray from the origin has the actual normalized Poynting velocity
on the second spatial axis at time two. -/
example : HasDerivAt (fun τ => (batemanRay τ (0, 0, 0)).2.1) (poyntingFlow 0 0 (-2) 2 1) 2 := by
  have hpos : batemanRay 2 (0, 0, 0) = (0, 0, -2) := by norm_num [batemanRay]
  have h := (batemanRay_hasDerivAt 2 (0, 0, 0)).2.1
  rw [hpos] at h
  exact h

/-- A point of the trefoil travels with the powered field at a nonzero time. -/
example : ∃ s ∈ initialSpatialKnot 2 3,
    HasDerivAt (fun τ => (batemanRay τ s).2.2)
      (poyntingPowerFlow 2 3 (batemanRay 2 s).1 (batemanRay 2 s).2.1 (batemanRay 2 s).2.2 2 2) 2 := by
  have hp : (0 : ℕ) < 2 := by decide
  have hq : (0 : ℕ) < 3 := by decide
  obtain ⟨a, b, ha, hb, hs, he⟩ := exists_balanced_torus_radii hp hq
  let s := initialSpatialKnotHomeomorph hp hq (by decide) ha hb hs he (1 : Circle)
  exact ⟨s.val, s.property, (batemanRay_hasDerivAt_power hp hq 2 s.property).2.2⟩

#print axioms Qatlib.Papers.KnotLight13.TorusFamily.initialSpatialKnotHomeomorph
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.batemanSliceHomeomorph_image_initialSpatialKnot
#print axioms Qatlib.Papers.KnotLight13.TorusFamily.batemanRay_hasDerivAt_power
