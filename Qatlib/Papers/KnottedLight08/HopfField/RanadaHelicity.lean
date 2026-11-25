/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.HopfField.RanadaInitialHelicity
public import Qatlib.Papers.KnottedLight08.NullLinking.RayGradientTransport

import Mathlib.MeasureTheory.Function.Jacobian

/-!
# The transported magnetic helicity integral

[IrvineBouwmeester2008KnottedLight], Eqs. (1) and (2),
[DOI](https://doi.org/10.1038/nphys1056).
The reflected ray is an orientation-preserving diffeomorphism of
physical space. Pulling the initial potential back by the inverse ray
gives a smooth spatial covector. Pairing with the actual magnetic
vector yields the change-of-variables density of the initial helicity.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.KnottedLight08.HopfField

open Qatlib.Papers.KnottedLight08.NullLinking
open Qatlib.Papers.KnotLight13.TorusFamily
open Qatlib.Papers.KnottedLight08.HopfField (dot3)
open Set MeasureTheory

local notation "Spatial" => ℝ × ℝ × ℝ

/-- Pairing with physical Cartesian coordinates, as a continuous linear
map from coefficient vectors to spatial covectors. -/
def spatialCovectorMap : (Fin 3 → ℝ) →L[ℝ] (Spatial →L[ℝ] ℝ) :=
  (ContinuousLinearMap.proj 0).smulRight (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) +
  (ContinuousLinearMap.proj 1).smulRight
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) +
  (ContinuousLinearMap.proj 2).smulRight
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))

/-- The initial potential as a spatial covector on the physical triples. -/
def ranadaInitialCovector (x : Spatial) : Spatial →L[ℝ] ℝ :=
  spatialCovectorMap (ranadaInitialPotential x.1 x.2.1 x.2.2)

/-- The covector evaluates by ordinary Cartesian pairing with the initial potential. -/
theorem ranadaInitialCovector_apply (x u : Spatial) :
    ranadaInitialCovector x u =
      dot3 (ranadaInitialPotential x.1 x.2.1 x.2.2) (cartesianCoordinates u) := by
  simp [ranadaInitialCovector, spatialCovectorMap, cartesianCoordinates, dot3]

/-- The covector field inherits the smoothness of its three coefficient functions. -/
theorem contDiff_ranadaInitialCovector : ContDiff ℝ ⊤ ranadaInitialCovector := by
  have hp : ContDiff ℝ ⊤ (fun x : Spatial => (x.1, x.2.1, x.2.2, (0 : ℝ))) := by fun_prop
  have ha : ContDiff ℝ ⊤ (fun x : Spatial => ranadaInitialPotential x.1 x.2.1 x.2.2) := by
    rw [contDiff_pi]
    intro j
    have h := (contDiff_ranada_initial_potential j).comp hp
    simpa only [Function.comp_def] using h
  have h := spatialCovectorMap.contDiff.comp ha
  unfold ranadaInitialCovector
  simpa only [Function.comp_def] using h

/-- Pulling the initial gauge back along the inverse reflected ray assigns
a covector to each point in the time slice. -/
def ranadaMagneticCovector (t : ℝ) (y : Spatial) : Spatial →L[ℝ] ℝ :=
  let g := (batemanSliceHomeomorph (-t)).symm
  (ranadaInitialCovector (g y)).comp (fderiv ℝ g y)

/-- For every fixed time the transported covector is smooth on all of
physical space, with no restriction to an affine fiber chart. -/
theorem contDiff_ranadaMagneticCovector (t : ℝ) :
    ContDiff ℝ ⊤ (ranadaMagneticCovector t) := by
  let g : Spatial → Spatial := (batemanSliceHomeomorph (-t)).symm
  have hg : ContDiff ℝ ⊤ g := contDiff_bateman_slice_inverse (-t)
  exact (contDiff_ranadaInitialCovector.comp hg).clm_comp
    (hg.fderiv_right (by simp))

/-- The helicity pairing of the transported covector with the actual
Rañada magnetic vector at time `t`. -/
def ranadaMagneticHelicityDensity (t : ℝ) (y : Spatial) : ℝ :=
  ranadaMagneticCovector t y (ranadaMagneticVector t y)

/-- The forward and inverse slice differentials compose to the identity
at the corresponding physical points. -/
theorem fderiv_bateman_slice_inverse_comp_ray (t : ℝ) (x : Spatial) :
    (fderiv ℝ (batemanSliceHomeomorph t).symm (batemanRay t x)).comp
      (fderiv ℝ (batemanRay t) x) = ContinuousLinearMap.id ℝ Spatial := by
  let g : Spatial → Spatial := (batemanSliceHomeomorph t).symm
  let f := batemanRay t
  have hg : Differentiable ℝ g := (contDiff_bateman_slice_inverse t).differentiable (by simp)
  have hf : Differentiable ℝ f := (contDiff_bateman_ray t).differentiable (by simp)
  have hcomp : g ∘ f = id := funext (batemanSliceHomeomorph t).symm_apply_apply
  have hd := ((hg (f x)).hasFDerivAt.comp x (hf x).hasFDerivAt).fderiv
  rw [hcomp, fderiv_id] at hd
  exact hd.symm

/-- The transported helicity density times the forward Jacobian
is the initial magnetic pairing. -/
theorem ranadaMagneticHelicityDensity_jacobian (t : ℝ) (x : Spatial) :
    LinearMap.det (fderiv ℝ (batemanRay (-t)) x).toLinearMap *
      ranadaMagneticHelicityDensity t (batemanRay (-t) x) =
        ranadaInitialCovector x (ranadaMagneticVector 0 x) := by
  let f := batemanRay (-t)
  let g : Spatial → Spatial := (batemanSliceHomeomorph (-t)).symm
  have hg : g (f x) = x := (batemanSliceHomeomorph (-t)).symm_apply_apply x
  have hb := reflected_ray_transports_magnetic_vector t x
  change fderiv ℝ f x (ranadaMagneticVector 0 x) =
    LinearMap.det (fderiv ℝ f x).toLinearMap • ranadaMagneticVector t (f x) at hb
  change LinearMap.det (fderiv ℝ f x).toLinearMap *
    (ranadaInitialCovector (g (f x))).comp (fderiv ℝ g (f x))
      (ranadaMagneticVector t (f x)) = _
  rw [← smul_eq_mul, ← map_smul, ← hb, hg]
  change ranadaInitialCovector x (((fderiv ℝ g (f x)).comp (fderiv ℝ f x))
    (ranadaMagneticVector 0 x)) = _
  have hD : (fderiv ℝ g (f x)).comp (fderiv ℝ f x) = ContinuousLinearMap.id ℝ Spatial :=
    fderiv_bateman_slice_inverse_comp_ray (-t) x
  rw [hD, ContinuousLinearMap.id_apply]

/-- The canonical coordinate conversion from product Lebesgue volume
to Euclidean three-space. -/
def spatialEuclidean : Spatial ≃ᵐ EuclideanSpace ℝ (Fin 3) :=
  (((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    ((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.finTwoArrow)).symm).trans
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))

/-- The canonical conversion preserves the normalized Lebesgue measure. -/
theorem measurePreserving_spatialEuclidean : MeasurePreserving spatialEuclidean := by
  have h₁ := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have h₂ : MeasurePreserving ((MeasurableEquiv.refl ℝ).prodCongr
      (MeasurableEquiv.finTwoArrow (α := ℝ))) :=
    (MeasurePreserving.id volume).prod (volume_preserving_finTwoArrow ℝ)
  exact (PiLp.volume_preserving_toLp (Fin 3)).comp
    (h₂.comp h₁).symm

/-- This conversion sends a physical triple to its literal coordinates. -/
theorem spatialEuclidean_apply (x : Spatial) (j : Fin 3) :
    spatialEuclidean x j = cartesianCoordinates x j := by
  rcases x with ⟨x, y, z⟩
  fin_cases j <;> rfl

/-- The initial covector pairing is the already evaluated Euclidean
initial helicity integrand in Cartesian coordinates. -/
private theorem initial_pairing_eq_euclidean (x : Spatial) :
    ranadaInitialCovector x (ranadaMagneticVector 0 x) =
      ranadaInitialHelicityDensity (spatialEuclidean x) := by
  rw [ranadaInitialCovector_apply, ranadaMagneticVector, LinearEquiv.apply_symm_apply]
  unfold ranadaInitialHelicityDensity
  simp only [spatialEuclidean_apply]
  rfl

/-- The transported magnetic pairing is absolutely integrable and its
integral is one quarter on every physical slice. -/
theorem integrable_and_integral_ranadaMagneticHelicityDensity (t : ℝ) :
    Integrable (ranadaMagneticHelicityDensity t) ∧
      (∫ y : Spatial, ranadaMagneticHelicityDensity t y) = 1 / 4 := by
  let f := batemanRay (-t)
  let D := fderiv ℝ f
  let g := ranadaMagneticHelicityDensity t
  have hsurj : f '' (univ : Set Spatial) = univ := by
    rw [image_univ]
    exact (batemanSliceHomeomorph (-t)).surjective.range_eq
  have hinj : InjOn f univ := (batemanSliceHomeomorph (-t)).injective.injOn
  have hD : ∀ x ∈ univ, HasFDerivWithinAt f (D x) univ x :=
    fun x _ => ((contDiff_bateman_ray (-t)).differentiable (by simp) x).hasFDerivAt.hasFDerivWithinAt
  have hweight (x : Spatial) :
      |LinearMap.det (D x).toLinearMap| • g (f x) =
        ranadaInitialHelicityDensity (spatialEuclidean x) := by
    rw [abs_of_pos (det_bateman_ray_pos (-t) x), smul_eq_mul,
      ranadaMagneticHelicityDensity_jacobian, initial_pairing_eq_euclidean]
  have hi : Integrable (ranadaInitialHelicityDensity ∘ spatialEuclidean) :=
    measurePreserving_spatialEuclidean.integrable_comp_of_integrable
      integrable_ranada_initial_helicity
  have : (volume : Measure Spatial).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod ℝ (ℝ × ℝ), Measure.volume_eq_prod ℝ ℝ]
    infer_instance
  constructor
  · have hh := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
      MeasurableSet.univ hD hinj g
    rw [hsurj, integrableOn_univ, integrableOn_univ] at hh
    exact hh.mpr (hi.congr (Filter.Eventually.of_forall fun x => (hweight x).symm))
  · have hh := integral_image_eq_integral_abs_det_fderiv_smul volume MeasurableSet.univ hD hinj g
    rw [hsurj, setIntegral_univ, setIntegral_univ] at hh
    rw [hh, integral_congr_ae (Filter.Eventually.of_forall hweight)]
    exact (measurePreserving_spatialEuclidean.integral_comp'
      ranadaInitialHelicityDensity).trans integral_ranada_initial_helicity

end Qatlib.Papers.KnottedLight08.HopfField
