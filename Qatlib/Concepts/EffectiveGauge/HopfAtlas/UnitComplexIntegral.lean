/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.FourierCoefficient
import Qatlib.Concepts.EffectiveGauge.RationalFlow.MeanIntegral

set_option backward.isDefEq.respectTransparency false

/-!
# Unit Complex Integral

Hopf Atlas constructions for Effective Gauge.
Defines `CoefficientCoordinatePoint`, `coefficientCoordinateTop`, `unitComplexCubeIntegral`.
Proves `unitComplexCubeIntegral_add`, `unitComplexCubeIntegral_const_mul`, `unit_complex_partial_integral_paired_faces`.
-/


set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Abbreviation for Coefficient Coordinate Point in the Hopf Atlas construction. -/
private abbrev CoefficientCoordinatePoint := Fin 3 → ℝ
/-- Definition of coefficient Coordinate Top in the Hopf Atlas construction. -/
private def coefficientCoordinateTop : CoefficientCoordinatePoint := fun _ => 1

/-- Definition of unit Complex Cube Integral in the Hopf Atlas construction. -/
def unitComplexCubeIntegral (f : SpatialPoint → ℂ) : ℂ :=
  ∫ u : CoefficientCoordinatePoint in Icc 0 coefficientCoordinateTop, f (WithLp.toLp 2 u)

/-- Original `unitComplexCubeIntegral_add` guarantee for the `UnitComplexIntegral` construction; the complete source hypotheses are retained. -/
theorem unitComplexCubeIntegral_add (f g : SpatialPoint → ℂ) (hf : Continuous f) (hg : Continuous g) :
    unitComplexCubeIntegral (fun x => f x+g x)=unitComplexCubeIntegral f+unitComplexCubeIntegral g := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  exact integral_add (μ := (volume : Measure CoefficientCoordinatePoint).restrict (Icc 0 coefficientCoordinateTop))
    ((hf.comp e.continuous).integrableOn_Icc) ((hg.comp e.continuous).integrableOn_Icc)

/-- Original `unitComplexCubeIntegral_const_mul` guarantee for the `UnitComplexIntegral` construction; the complete source hypotheses are retained. -/
theorem unitComplexCubeIntegral_const_mul (c : ℂ) (f : SpatialPoint → ℂ) :
    unitComplexCubeIntegral (fun x => c*f x)=c*unitComplexCubeIntegral f := by
  unfold unitComplexCubeIntegral
  exact integral_const_mul c _

/-- Original `unit_complex_partial_integral_paired_faces` guarantee for the `UnitComplexIntegral` construction; the complete source hypotheses are retained. -/
private theorem unit_complex_partial_integral_paired_faces (f : CoefficientCoordinatePoint → ℂ) (hf : ContDiff ℝ ∞ f)
    (hfaces : ∀ (j : Fin 3) (y : Fin 2 → ℝ),
      f (j.insertNth 1 y)=f (j.insertNth 0 y)) (i : Fin 3) :
    (∫ x in Icc (0 : CoefficientCoordinatePoint) coefficientCoordinateTop,
      fderiv ℝ f x (Pi.single i 1))=0 := by
  let fs : Fin 3 → CoefficientCoordinatePoint → ℂ := fun j => if j=i then f else fun _ => 0
  let dfs : Fin 3 → CoefficientCoordinatePoint → CoefficientCoordinatePoint →L[ℝ] ℂ :=
    fun j => if j=i then fderiv ℝ f else fun _ => 0
  have hc (j : Fin 3) : ContinuousOn (fs j) (Icc (0 : CoefficientCoordinatePoint) coefficientCoordinateTop) := by
    by_cases h : j=i
    · simpa [fs,h] using hf.continuous.continuousOn
    · simp only [fs,h,ite_false]
      exact continuousOn_const
  have hd (x : CoefficientCoordinatePoint) (j : Fin 3) : HasFDerivAt (fs j) (dfs j x) x := by
    by_cases h : j=i
    · simpa [fs,dfs,h] using (hf.differentiable (by simp) x).hasFDerivAt
    · simpa [fs,dfs,h] using hasFDerivAt_const (0 : ℂ) x
  have heq (x : CoefficientCoordinatePoint) : (∑ j : Fin 3, dfs j x (Pi.single j 1))=
      fderiv ℝ f x (Pi.single i 1) := by
    have heach (j : Fin 3) : dfs j x (Pi.single j 1)=
        if j=i then fderiv ℝ f x (Pi.single j 1) else 0 := by
      by_cases h : j=i <;> simp [dfs,h]
    simp_rw [heach]
    simp
  have hi : IntegrableOn (fun x => ∑ j : Fin 3, dfs j x (Pi.single j 1))
      (Icc (0 : CoefficientCoordinatePoint) coefficientCoordinateTop) := by
    simp only [heq]
    exact (((hf.fderiv_right (m := ∞) (by rfl)).continuous).clm_apply continuous_const).integrableOn_Icc
  have hdiv := integral_divergence_of_hasFDerivAt_off_countable' (0 : CoefficientCoordinatePoint) coefficientCoordinateTop
    (by intro j; exact zero_le_one) fs dfs ∅ countable_empty hc (fun x _ j => hd x j) hi
  have hfrontback (j : Fin 3) :
      (∫ y in Icc ((0 : CoefficientCoordinatePoint) ∘ j.succAbove) (coefficientCoordinateTop ∘ j.succAbove),
        fs j (j.insertNth (coefficientCoordinateTop j) y))=
      ∫ y in Icc ((0 : CoefficientCoordinatePoint) ∘ j.succAbove) (coefficientCoordinateTop ∘ j.succAbove),
        fs j (j.insertNth ((0 : CoefficientCoordinatePoint) j) y) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro y _hy
    by_cases hji : j=i
    · simpa [fs,hji,coefficientCoordinateTop] using hfaces j y
    · simp [fs,hji]
  simpa only [heq,hfrontback,sub_self,Finset.sum_const_zero] using hdiv


/-- True unit-periodic complex derivatives have zero actual cube integral.
The proof is face cancellation for the original smooth function, not a
hypothesis about Fourier coefficients. -/
theorem unitComplexCubeIntegral_partial_periodic (f : SpatialPoint → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : IsUnitPeriodicField f) (i : Fin 3) :
    unitComplexCubeIntegral (spatialWordPartial f [i])=0 := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have hc : ContDiff ℝ ∞ (fun x : CoefficientCoordinatePoint => f (e x)) := hf.comp e.contDiff
  have hfaces (j : Fin 3) (y : Fin 2 → ℝ) :
      f (e (j.insertNth 1 y))=f (e (j.insertNth 0 y)) := by
    have hpoint : e (j.insertNth 1 y)=e (j.insertNth 0 y)+unitIntegerShift (Pi.single j 1) := by
      change WithLp.toLp 2 (j.insertNth 1 y)=WithLp.toLp 2 (j.insertNth 0 y)+unitIntegerShift (Pi.single j 1)
      apply PiLp.ext
      rw [Fin.forall_iff_succAbove j]
      constructor
      · simp [unitIntegerShift]
      · intro k
        simp [unitIntegerShift,Pi.single_apply,Fin.succAbove_ne]
    rw [hpoint]
    exact hp _ _
  have hder (x : CoefficientCoordinatePoint) :
      fderiv ℝ (fun y => f (e y)) x (Pi.single i 1)=
        fderiv ℝ f (e x) (EuclideanSpace.single i 1) := by
    have hd := (hf.differentiable (by simp) (e x)).hasFDerivAt.comp x e.hasFDerivAt
    change fderiv ℝ (f ∘ e) x (Pi.single i 1)=_
    rw [hd.fderiv]
    rfl
  have h := unit_complex_partial_integral_paired_faces (fun x => f (e x)) hc hfaces i
  simp only [hder] at h
  exact h

/-- The half-open torus integration box and the closed cube differ only on
null faces; all normalizations are the actual unit Lebesgue measure. -/
theorem unitFourierCoefficient_eq_cubeIntegral (f : SpatialPoint → ℂ) (hf : Continuous f)
    (hp : IsUnitPeriodicField f) (k : SpatialFrequency) :
    unitFourierCoefficient f hf hp k=unitComplexCubeIntegral (fun x => unitFourierMode (-k) x*f x) := by
  rw [unitFourierCoefficient_eq_integral]
  unfold unitComplexCubeIntegral
  apply setIntegral_congr_set
  exact Measure.univ_pi_Ioc_ae_eq_Icc

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
