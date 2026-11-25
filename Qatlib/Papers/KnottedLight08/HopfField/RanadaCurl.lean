/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.HopfField.RanadaHelicity
public import Qatlib.Papers.KnottedLight08.NullLinking.ElectricCircles
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# The curls and helicities of the transported Rañada potentials

[IrvineBouwmeester2008KnottedLight], Eqs. (1) and (2),
[DOI](https://doi.org/10.1038/nphys1056).
The antisymmetric derivative of the inverse-ray pullback is the
pullback of the initial magnetic flux form. The actual magnetic
vector obeys the matching determinant-weighted transport law, so the
transported covector is a global magnetic potential on each slice.
The proper spatial quarter-turn then gives the actual electric
potential and preserves its full helicity integral.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.KnottedLight08.HopfField

open Qatlib.Papers.KnottedLight08.NullLinking
open Qatlib.Papers.KnotLight13.TorusFamily
open Qatlib.Papers.KnottedLight08.HopfField (dot3)
open Set MeasureTheory

local notation "PhysicalPoint" => ℝ × ℝ × ℝ

/-- The exterior derivative of a spatial covector field, evaluated on two vectors. -/
def spatialExteriorPair (A : PhysicalPoint → PhysicalPoint →L[ℝ] ℝ) (x u v : PhysicalPoint) : ℝ :=
  fderiv ℝ A x u v - fderiv ℝ A x v u

/-- The positive Cartesian directions in physical coordinates. -/
def physicalAxis (i : Fin 3) : PhysicalPoint :=
  ![(1, 0, 0), (0, 1, 0), (0, 0, 1)] i

/-- The real Cartesian curl of a spatial covector in the Euclidean orientation. -/
def spatialCovectorCurl (A : PhysicalPoint → PhysicalPoint →L[ℝ] ℝ) (x : PhysicalPoint) : PhysicalPoint :=
  (spatialExteriorPair A x (physicalAxis 1) (physicalAxis 2),
   spatialExteriorPair A x (physicalAxis 2) (physicalAxis 0),
   spatialExteriorPair A x (physicalAxis 0) (physicalAxis 1))

/-- The Cartesian determinant of a triple of vectors, written out in physical coordinates. -/
private theorem cartesianDet_eq (b u v : PhysicalPoint) :
    cartesianBasis.det ![b, u, v] =
      b.1 * (u.2.1 * v.2.2 - u.2.2 * v.2.1) +
      b.2.1 * (u.2.2 * v.1 - u.1 * v.2.2) +
      b.2.2 * (u.1 * v.2.1 - u.2.1 * v.1) := by
  have hrepr (x : PhysicalPoint) (j : Fin 3) :
      cartesianBasis.repr x j = cartesianCoordinates x j := by
    change (Pi.basisFun ℝ (Fin 3)).repr (cartesianCoordinates x) j = _
    exact Pi.basisFun_repr ℝ (Fin 3) (cartesianCoordinates x) j
  rw [Module.Basis.det_apply, Matrix.det_fin_three]
  simp [Module.Basis.toMatrix_apply, hrepr, cartesianCoordinates]
  ring

/-- The antisymmetric derivative is the oriented flux pairing of its curl. -/
theorem spatialExteriorPair_eq_cartesianDet (A : PhysicalPoint → PhysicalPoint →L[ℝ] ℝ)
    (x u v : PhysicalPoint) :
    spatialExteriorPair A x u v = cartesianBasis.det ![spatialCovectorCurl A x, u, v] := by
  have hexp (w : PhysicalPoint) : w =
      w.1 • physicalAxis 0 + w.2.1 • physicalAxis 1 + w.2.2 • physicalAxis 2 := by
    rcases w with ⟨a, b, c⟩
    simp [physicalAxis]
  rw [cartesianDet_eq]
  conv_lhs => rw [hexp u, hexp v]
  simp only [spatialCovectorCurl, spatialExteriorPair, map_add, map_smul, add_apply, smul_apply,
    smul_eq_mul]
  ring

/-- Cartesian flux pairing with every pair of vectors determines a unique curl vector. -/
private theorem cartesianDet_injective (b c : PhysicalPoint)
    (h : ∀ u v : PhysicalPoint, cartesianBasis.det ![b, u, v] = cartesianBasis.det ![c, u, v]) :
    b = c := by
  have h₀ := h (physicalAxis 1) (physicalAxis 2)
  have h₁ := h (physicalAxis 2) (physicalAxis 0)
  have h₂ := h (physicalAxis 0) (physicalAxis 1)
  simp [cartesianDet_eq, physicalAxis] at h₀ h₁ h₂
  exact Prod.ext h₀ (Prod.ext h₁ h₂)

/-- The real exterior pairing commutes with a smooth pullback. In the
chain rule the symmetric second derivatives cancel. -/
theorem spatialExteriorPair_pullback {A : PhysicalPoint → PhysicalPoint →L[ℝ] ℝ}
    {f : PhysicalPoint → PhysicalPoint} {x : PhysicalPoint} (hA : DifferentiableAt ℝ A (f x))
    (hf : ContDiffAt ℝ 2 f x) (u v : PhysicalPoint) :
    spatialExteriorPair (fun x => (A (f x)).comp (fderiv ℝ f x)) x u v =
      spatialExteriorPair A (f x) (fderiv ℝ f x u) (fderiv ℝ f x v) := by
  have hd := hf.differentiableAt (by norm_num)
  have hD := (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt
    (by norm_num)
  have hsym := hf.isSymmSndFDerivAt (by simp : minSmoothness ℝ 2 ≤ 2)
  unfold spatialExteriorPair
  have h := fderiv_clm_comp (hA.comp x hd) hD
  simp only [Function.comp_def] at h
  rw [h, fderiv_fun_comp x hA hd]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply]
  rw [hsym.eq u v]
  ring

/-- Differentiating the initial covector's Cartesian coefficient in
a basis direction agrees with the real part of the published partial
of the constant time extension. -/
private theorem initialCovector_partial (x : PhysicalPoint) (i j : Fin 3) :
    fderiv ℝ ranadaInitialCovector x (physicalAxis i) (physicalAxis j) =
      (spaceTimePartial (fun s => (ranadaInitialPotential s.1 s.2.1 s.2.2.1 j : ℂ))
        (x.1, x.2.1, x.2.2, 0) (Fin.castSucc i)).re := by
  let r := cartesianCoordinates x i
  let L (u : ℝ) := x + (u - r) • physicalAxis i
  have hL : HasDerivAt L (physicalAxis i) r := by
    simpa only [L, id_eq, one_smul] using
      ((((hasDerivAt_id r).sub_const r).smul_const (physicalAxis i)).const_add x)
  have hLx : L r = x := by simp [L]
  have hA : HasFDerivAt ranadaInitialCovector (fderiv ℝ ranadaInitialCovector x) (L r) := by
    rw [hLx]
    exact ((contDiff_ranadaInitialCovector.differentiable (by simp)) x).hasFDerivAt
  have hd : HasDerivAt (fun u => ranadaInitialCovector (L u) (physicalAxis j))
      (fderiv ℝ ranadaInitialCovector x (physicalAxis i) (physicalAxis j)) r := by
    simpa only [Function.comp_def, map_zero, add_zero] using
      (hA.comp_hasDerivAt r hL).clm_apply (hasDerivAt_const r (physicalAxis j))
  have he (u : ℝ) :
      coordinateSection (x.1, x.2.1, x.2.2, 0) (Fin.castSucc i) u =
        ((L u).1, (L u).2.1, (L u).2.2, 0) := by
    rcases x with ⟨a, b, c⟩
    fin_cases i <;> simp [coordinateSection, L, r, physicalAxis, cartesianCoordinates]
  have hr : coordinateValue (x.1, x.2.1, x.2.2, 0) (Fin.castSucc i) = r := by
    fin_cases i <;> rfl
  have hcoeff (y : PhysicalPoint) :
      ranadaInitialCovector y (physicalAxis j) = ranadaInitialPotential y.1 y.2.1 y.2.2 j := by
    rw [ranadaInitialCovector_apply]
    fin_cases j <;> simp [dot3, physicalAxis, cartesianCoordinates]
  have hfun (u : ℝ) :
      (ranadaInitialPotential
        (coordinateSection (x.1, x.2.1, x.2.2, 0) (Fin.castSucc i) u).1
        (coordinateSection (x.1, x.2.1, x.2.2, 0) (Fin.castSucc i) u).2.1
        (coordinateSection (x.1, x.2.1, x.2.2, 0) (Fin.castSucc i) u).2.2.1 j : ℂ) =
        (ranadaInitialCovector (L u) (physicalAxis j) : ℂ) := by
    rw [he, hcoeff]
  unfold spaceTimePartial
  simp_rw [hfun, hr]
  rw [hd.ofReal_comp.deriv, Complex.ofReal_re]

/-- The curl in the covector representation agrees with the actual
initial magnetic vector on the whole physical slice. -/
theorem spatialCovectorCurl_ranadaInitial (x : PhysicalPoint) :
    spatialCovectorCurl ranadaInitialCovector x = ranadaMagneticVector 0 x := by
  have hk (i : Fin 3) := congrArg Complex.re
    (curl_ranada_initial_potential x.1 x.2.1 x.2.2 i)
  have h₀ := hk 0
  have h₁ := hk 1
  have h₂ := hk 2
  unfold cartesianCurl at h₀ h₁ h₂
  apply cartesianCoordinates.injective
  rw [ranadaMagneticVector, LinearEquiv.apply_symm_apply]
  funext i
  fin_cases i
  · change spatialExteriorPair ranadaInitialCovector x (physicalAxis 1) (physicalAxis 2) = _
    rw [spatialExteriorPair, initialCovector_partial, initialCovector_partial]
    simpa [Complex.sub_re] using h₀
  · change spatialExteriorPair ranadaInitialCovector x (physicalAxis 2) (physicalAxis 0) = _
    rw [spatialExteriorPair, initialCovector_partial, initialCovector_partial]
    simpa [Complex.sub_re] using h₁
  · change spatialExteriorPair ranadaInitialCovector x (physicalAxis 0) (physicalAxis 1) = _
    rw [spatialExteriorPair, initialCovector_partial, initialCovector_partial]
    simpa [Complex.sub_re] using h₂

/-- The two ray differentials in the other order also compose to the identity. -/
private theorem fderiv_ray_comp_slice_inverse (t : ℝ) (y : PhysicalPoint) :
    let f : PhysicalPoint → PhysicalPoint := batemanRay t
    let g : PhysicalPoint → PhysicalPoint := (batemanSliceHomeomorph t).symm
    (fderiv ℝ f (g y)).comp (fderiv ℝ g y) = ContinuousLinearMap.id ℝ PhysicalPoint := by
  let f := batemanRay t
  let g : PhysicalPoint → PhysicalPoint := (batemanSliceHomeomorph t).symm
  have hcomp : f ∘ g = id := funext (batemanSliceHomeomorph t).apply_symm_apply
  have hf := (contDiff_bateman_ray t).differentiable (by simp)
  have hg := (contDiff_bateman_slice_inverse t).differentiable (by simp)
  have hh := ((hf (g y)).hasFDerivAt.comp y (hg y).hasFDerivAt).fderiv
  rw [hcomp, fderiv_id] at hh
  exact hh.symm

set_option maxHeartbeats 500000 in
/-- At every real time the transported covector is a genuine magnetic
potential: its Cartesian curl is the actual magnetic Rañada vector. -/
theorem spatialCovectorCurl_ranadaMagnetic (t : ℝ) (y : PhysicalPoint) :
    spatialCovectorCurl (ranadaMagneticCovector t) y = ranadaMagneticVector t y := by
  let f := batemanRay (-t)
  let g : PhysicalPoint → PhysicalPoint := (batemanSliceHomeomorph (-t)).symm
  obtain ⟨x, rfl⟩ : ∃ x, f x = y := (batemanSliceHomeomorph (-t)).surjective y
  have hg : g (f x) = x := (batemanSliceHomeomorph (-t)).symm_apply_apply x
  let D := fderiv ℝ f x
  let E := fderiv ℝ g (f x)
  let δ := LinearMap.det D.toLinearMap
  have hδ : δ ≠ 0 := (det_bateman_ray_pos (-t) x).ne'
  have hDE : D.comp E = ContinuousLinearMap.id ℝ PhysicalPoint := by
    have hh := fderiv_ray_comp_slice_inverse (-t) (f x)
    change (fderiv ℝ f (g (f x))).comp E = _ at hh
    rw [hg] at hh
    exact hh
  have hE (u : PhysicalPoint) : D (E u) = u :=
    DFunLike.congr_fun hDE u
  have hb : D (ranadaMagneticVector 0 x) = δ • ranadaMagneticVector t (f x) :=
    reflected_ray_transports_magnetic_vector t x
  have hdiff : ContDiffAt ℝ 2 g (f x) :=
    ((contDiff_bateman_slice_inverse (-t)).of_le le_top).contDiffAt
  have hA : DifferentiableAt ℝ ranadaInitialCovector (g (f x)) :=
    (contDiff_ranadaInitialCovector.differentiable (by simp)) _
  apply cartesianDet_injective
  intro u v
  rw [← spatialExteriorPair_eq_cartesianDet]
  change spatialExteriorPair (fun y => (ranadaInitialCovector (g y)).comp (fderiv ℝ g y))
    (f x) u v = _
  rw [spatialExteriorPair_pullback hA hdiff u v, hg, spatialExteriorPair_eq_cartesianDet,
    spatialCovectorCurl_ranadaInitial]
  change cartesianBasis.det ![ranadaMagneticVector 0 x, E u, E v] =
    cartesianBasis.det ![ranadaMagneticVector t (f x), u, v]
  have hcomp : (D.toLinearMap ∘ ![ranadaMagneticVector 0 x, E u, E v]) =
      ![δ • ranadaMagneticVector t (f x), u, v] := by
    funext j
    fin_cases j
    · exact hb
    · exact hE u
    · exact hE v
  have hdet := Module.Basis.det_comp cartesianBasis D.toLinearMap
    ![ranadaMagneticVector 0 x, E u, E v]

  have hscale :
      cartesianBasis.det ![δ • ranadaMagneticVector t (f x), u, v] =
        δ * cartesianBasis.det ![ranadaMagneticVector t (f x), u, v] := by
    rw [cartesianDet_eq, cartesianDet_eq]
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [hcomp, hscale] at hdet
  exact mul_left_cancel₀ hδ hdet.symm

/-- The electric-to-magnetic quarter-turn as a continuous spatial linear map. -/
def electricRotationCLM : PhysicalPoint →L[ℝ] PhysicalPoint :=
  electricToMagnetic.toContinuousLinearEquiv.toContinuousLinearMap

/-- The physical quarter-turn preserves orientation and has unit Jacobian. -/
theorem det_electricRotationCLM : LinearMap.det electricRotationCLM.toLinearMap = 1 := by
  let e : Fin 3 → PhysicalPoint := ![physicalAxis 0, physicalAxis 1, physicalAxis 2]
  have h := Module.Basis.det_comp cartesianBasis electricRotationCLM.toLinearMap e
  have hm : electricRotationCLM.toLinearMap ∘ e =
      (![(0, 1, 0), (-1, 0, 0), (0, 0, 1)] : Fin 3 → PhysicalPoint) := by
    funext j
    fin_cases j <;> simp [e, electricRotationCLM, electricToMagnetic, physicalAxis]
  rw [hm] at h
  change cartesianBasis.det ![(0, 1, 0), (-1, 0, 0), (0, 0, 1)] =
    LinearMap.det electricRotationCLM.toLinearMap *
      cartesianBasis.det ![physicalAxis 0, physicalAxis 1, physicalAxis 2] at h
  norm_num [cartesianDet_eq, physicalAxis] at h
  exact h.symm

/-- The quarter-turn pulls the magnetic gauge back to an electric covector. -/
def ranadaElectricCovector (t : ℝ) (x : PhysicalPoint) : PhysicalPoint →L[ℝ] ℝ :=
  (ranadaMagneticCovector t (electricToMagnetic x)).comp electricRotationCLM

/-- The rotated electric covector is smooth in physical space at every time. -/
theorem contDiff_ranadaElectricCovector (t : ℝ) :
    ContDiff ℝ ⊤ (ranadaElectricCovector t) :=
  ((contDiff_ranadaMagneticCovector t).comp electricRotationCLM.contDiff).clm_comp contDiff_const

/-- The electric covector is a global electric potential, with curl
equal to the actual electric vector of the wave. -/
theorem spatialCovectorCurl_ranadaElectric (t : ℝ) (x : PhysicalPoint) :
    spatialCovectorCurl (ranadaElectricCovector t) x = ranadaElectricVector t x := by
  let D := electricRotationCLM
  have hd (y : PhysicalPoint) : fderiv ℝ (D : PhysicalPoint → PhysicalPoint) y = D := D.fderiv
  have hA := (contDiff_ranadaMagneticCovector t).differentiable (by simp) (D x)
  have hD : ContDiffAt ℝ 2 (D : PhysicalPoint → PhysicalPoint) x := D.contDiff.contDiffAt
  have hP : (fun y => (ranadaMagneticCovector t (D y)).comp (fderiv ℝ (D : _ → _) y)) =
      ranadaElectricCovector t := by
    funext y
    rw [hd]
    rfl
  apply cartesianDet_injective
  intro u v
  rw [← spatialExteriorPair_eq_cartesianDet, ← hP, spatialExteriorPair_pullback hA hD u v,
    hd, spatialExteriorPair_eq_cartesianDet, spatialCovectorCurl_ranadaMagnetic]
  have hb : ranadaMagneticVector t (D x) = D (ranadaElectricVector t x) :=
    ranadaMagneticVector_electricToMagnetic t x
  rw [hb]
  have hcomp : (D.toLinearMap ∘ ![ranadaElectricVector t x, u, v]) =
      ![D (ranadaElectricVector t x), D u, D v] := by
    funext j
    fin_cases j <;> rfl
  rw [← hcomp, Module.Basis.det_comp, det_electricRotationCLM, one_mul]

/-- The proper quarter-turn preserves the physical Cartesian Lebesgue measure. -/
private theorem measurePreserving_electricRotation : MeasurePreserving electricRotationCLM := by
  let D := electricRotationCLM
  have hvol : (volume : Measure PhysicalPoint).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod ℝ (ℝ × ℝ), Measure.volume_eq_prod ℝ ℝ]
    infer_instance
  have hderiv : ∀ x ∈ univ, HasFDerivWithinAt (D : PhysicalPoint → PhysicalPoint) D univ x :=
    fun x _ => D.hasFDerivAt.hasFDerivWithinAt
  have hsurj : D '' (univ : Set PhysicalPoint) = univ := by
    rw [image_univ]
    exact electricToMagnetic.surjective.range_eq
  have hinj : InjOn (D : PhysicalPoint → PhysicalPoint) univ :=
    electricToMagnetic.injective.injOn
  have h := map_withDensity_abs_det_fderiv_eq_addHaar volume
    MeasurableSet.univ.nullMeasurableSet hderiv hinj
  refine ⟨D.continuous.measurable, ?_⟩
  rw [hsurj, Measure.restrict_univ] at h
  have hdet : D.det = 1 := det_electricRotationCLM
  rw [hdet, abs_one, ENNReal.ofReal_one] at h
  change Measure.map D (volume.withDensity (1 : PhysicalPoint → ENNReal)) = volume at h
  rw [withDensity_one] at h
  exact h

/-- The electric helicity density pairs the actual electric field with its
global rotated potential. -/
def ranadaElectricHelicityDensity (t : ℝ) (x : PhysicalPoint) : ℝ :=
  ranadaElectricCovector t x (ranadaElectricVector t x)

/-- The electric helicity density is the rotated magnetic helicity density. -/
theorem ranadaElectricHelicityDensity_eq_rotated (t : ℝ) (x : PhysicalPoint) :
    ranadaElectricHelicityDensity t x = ranadaMagneticHelicityDensity t (electricToMagnetic x) := by
  unfold ranadaElectricHelicityDensity ranadaElectricCovector ranadaMagneticHelicityDensity
  rw [ranadaMagneticVector_electricToMagnetic]
  rfl

/-- Electric helicity is absolutely integrable on every real time slice,
equals the magnetic helicity, and has the normalized value one quarter. -/
theorem integrable_and_integral_ranadaElectricHelicityDensity (t : ℝ) :
    Integrable (ranadaElectricHelicityDensity t) ∧
      (∫ x : PhysicalPoint, ranadaElectricHelicityDensity t x) = 1 / 4 := by
  obtain ⟨hi, hI⟩ := integrable_and_integral_ranadaMagneticHelicityDensity t
  have he : ranadaElectricHelicityDensity t =
      ranadaMagneticHelicityDensity t ∘ electricRotationCLM :=
    funext (ranadaElectricHelicityDensity_eq_rotated t)
  rw [he]
  refine ⟨measurePreserving_electricRotation.integrable_comp_of_integrable hi, ?_⟩
  have hme : MeasurableEmbedding electricRotationCLM :=
    electricToMagnetic.toContinuousLinearEquiv.toHomeomorph.isClosedEmbedding.measurableEmbedding
  exact (measurePreserving_electricRotation.integral_comp hme
    (ranadaMagneticHelicityDensity t)).trans hI

end Qatlib.Papers.KnottedLight08.HopfField
