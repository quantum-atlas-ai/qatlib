/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.NullLinking.MagneticCircleTransport
public import Qatlib.Papers.KnottedLight08.NullLinking.RayGradientTransport

import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The tangent of every transported magnetic circle

[IrvineBouwmeester2008KnottedLight], Eq. (2) and Fig. 1,
[DOI](https://doi.org/10.1038/nphys1056).
On every time slice the derivative of the periodic parameterization
of a finite nonzero or pole magnetic fiber is a strictly positive
multiple of the actual nonvanishing Rañada magnetic vector. The
tangent statement uses the true spatial differential of the ray map.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.NullLinking

open Qatlib.Papers.KnotLight13.TorusFamily
open Qatlib.Papers.KnottedLight08.HopfField

/-- The chain rule and the positive ray determinant preserve the
orientation of a tangent that follows the initial magnetic field. -/
private theorem hasDerivAt_ray_of_magnetic_tangent (t θ : ℝ) (c : ℝ → ℝ × ℝ × ℝ)
    (v : ℝ × ℝ × ℝ) {a : ℝ} (ha : 0 < a) (hc : HasDerivAt c v θ)
    (hB : ranadaMagneticVector 0 (c θ) = a • v) :
    ∃ μ : ℝ, 0 < μ ∧ HasDerivAt (fun u => batemanRay (-t) (c u))
      (μ • ranadaMagneticVector t (batemanRay (-t) (c θ))) θ := by
  let D := fderiv ℝ (batemanRay (-t)) (c θ)
  let b := ranadaMagneticVector t (batemanRay (-t) (c θ))
  let δ := LinearMap.det D.toLinearMap
  have hδ : 0 < δ := det_bateman_ray_pos (-t) (c θ)
  have h := reflected_ray_transports_magnetic_vector t (c θ)
  change D (ranadaMagneticVector 0 (c θ)) = δ • b at h
  rw [hB, map_smul] at h
  have hD : D v = (δ / a) • b := by
    calc
      D v = a⁻¹ • (a • D v) := by rw [smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
      _ = _ := by rw [h, smul_smul, div_eq_mul_inv, mul_comm]
  refine ⟨δ / a, div_pos hδ ha, ?_⟩
  have hF : HasFDerivAt (batemanRay (-t)) D (c θ) :=
    ((contDiff_bateman_ray (-t)).differentiable (by simp) (c θ)).hasFDerivAt
  exact (hF.comp_hasDerivAt θ hc).congr_deriv hD

/-- At every real time the full finite nonzero level circle follows
the actual magnetic field with a nonzero tangent in the correct
orientation. -/
theorem hasDerivAt_magnetic_circle_at (u v t θ : ℝ) (hd : 0 < u ^ 2 + v ^ 2) :
    ∃ μ : ℝ, 0 < μ ∧ (μ • ranadaMagneticVector t (magneticCircleAt u v t θ)) ≠ 0 ∧
      HasDerivAt (magneticCircleAt u v t) (μ • ranadaMagneticVector t (magneticCircleAt u v t θ)) θ := by
  let c := fun u' : ℝ =>
    ((initialMagneticCircle u v u') 0, (initialMagneticCircle u v u') 1,
      (initialMagneticCircle u v u') 2)
  let V := cartesianCoordinates.symm (initialMagneticCircleTangent u v θ)
  have hc : HasDerivAt c V θ :=
    (hasDerivAt_initial_magnetic_circle u v θ 0).prodMk
      ((hasDerivAt_initial_magnetic_circle u v θ 1).prodMk
        (hasDerivAt_initial_magnetic_circle u v θ 2))
  obtain ⟨a, ha, hB⟩ := ranada_b_along_initial_magnetic_circle u v θ hd
  have hBV : ranadaMagneticVector 0 (c θ) = a • V := by
    apply cartesianCoordinates.injective
    rw [map_smul]
    change cartesianCoordinates (cartesianCoordinates.symm _) =
      a • cartesianCoordinates (cartesianCoordinates.symm _)
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact funext hB
  obtain ⟨μ, hμ, hD⟩ := hasDerivAt_ray_of_magnetic_tangent t θ c V ha hc hBV
  exact ⟨μ, hμ, smul_ne_zero hμ.ne' (ranada_magnetic_vector_ne_zero _ _), hD⟩

/-- The full pole circle also follows the actual magnetic field at every
time with a nonzero tangent in the correct orientation. -/
theorem hasDerivAt_magnetic_pole_circle_at (t θ : ℝ) :
    ∃ μ : ℝ, 0 < μ ∧ (μ • ranadaMagneticVector t (magneticPoleCircleAt t θ)) ≠ 0 ∧
      HasDerivAt (magneticPoleCircleAt t) (μ • ranadaMagneticVector t (magneticPoleCircleAt t θ)) θ := by
  let c := magneticPoleCircleAt 0
  let V := cartesianCoordinates.symm (![0, -Real.sin θ, -Real.cos θ] : Fin 3 → ℝ)
  have hc : HasDerivAt c V θ := by
    exact (hasDerivAt_initial_magnetic_pole_circle θ 0).prodMk
      ((hasDerivAt_initial_magnetic_pole_circle θ 1).prodMk
        (hasDerivAt_initial_magnetic_pole_circle θ 2))
  have hBV : ranadaMagneticVector 0 (c θ) = (1 / (2 * Real.pi)) • V := by
    apply cartesianCoordinates.injective
    rw [map_smul]
    change cartesianCoordinates (cartesianCoordinates.symm _) =
      (1 / (2 * Real.pi)) • cartesianCoordinates (cartesianCoordinates.symm _)
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact funext (ranada_b_along_initial_magnetic_pole_circle θ)
  obtain ⟨μ, hμ, hD⟩ := hasDerivAt_ray_of_magnetic_tangent t θ c V (by positivity) hc hBV
  have hD' : HasDerivAt (magneticPoleCircleAt t)
      (μ • ranadaMagneticVector t (magneticPoleCircleAt t θ)) θ := by
    change HasDerivAt (fun u => batemanRay (-t) (0, Real.cos u, -Real.sin u))
      (μ • ranadaMagneticVector t (batemanRay (-t) (0, Real.cos θ, -Real.sin θ))) θ
    simpa only [c, magneticPoleCircleAt, neg_zero, batemanRay_zero] using hD
  exact ⟨μ, hμ, smul_ne_zero hμ.ne' (ranada_magnetic_vector_ne_zero _ _), hD'⟩

end Qatlib.Papers.KnottedLight08.NullLinking
