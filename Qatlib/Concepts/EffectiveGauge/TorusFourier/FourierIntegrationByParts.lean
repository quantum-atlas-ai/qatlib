/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.UnitComplexIntegral
import Mathlib.Tactic.LinearCombination

set_option backward.isDefEq.respectTransparency false

/-!
# Fourier Integration By Parts

Torus Fourier constructions for Effective Gauge.
Proves `unitPeriodicField_fderiv`, `unitPeriodicField_spatialWordPartial`, `spatialWordPartial_complex_mul_first`.
-/


set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Original `unitPeriodicField_fderiv` guarantee for the `FourierIntegrationByParts` construction; the complete source hypotheses are retained. -/
theorem unitPeriodicField_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SpatialPoint → E) (hf : ContDiff ℝ ∞ f) (hp : IsUnitPeriodicField f) :
    IsUnitPeriodicField (fderiv ℝ f) := by
  intro x n
  have hc := (hf.differentiable (by simp) (x+unitIntegerShift n)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).add_const (unitIntegerShift n))
  have heq : (fun y => f (y+unitIntegerShift n))=f := funext (fun y => hp y n)
  change HasFDerivAt (fun y => f (y+unitIntegerShift n)) _ x at hc
  rw [heq] at hc
  simpa using hc.unique (hf.differentiable (by simp) x).hasFDerivAt

/-- Original `unitPeriodicField_spatialWordPartial` guarantee for the `FourierIntegrationByParts` construction; the complete source hypotheses are retained. -/
theorem unitPeriodicField_spatialWordPartial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SpatialPoint → E) (hf : ContDiff ℝ ∞ f) (hp : IsUnitPeriodicField f) (w : List (Fin 3)) :
    IsUnitPeriodicField (spatialWordPartial f w) := by
  induction w with
  | nil => exact hp
  | cons i w ih =>
    have hd := unitPeriodicField_fderiv _ (contDiff_spatialWordPartial f hf w) ih
    intro x n
    simp only [spatialWordPartial]
    rw [hd x n]

/-- Original `spatialWordPartial_complex_mul_first` guarantee for the `FourierIntegrationByParts` construction; the complete source hypotheses are retained. -/
theorem spatialWordPartial_complex_mul_first (f g : SpatialPoint → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (i : Fin 3) :
    spatialWordPartial (fun x => f x*g x) [i]=fun x =>
      spatialWordPartial f [i] x*g x+f x*spatialWordPartial g [i] x := by
  funext x
  have hd := ((hf.differentiable (by simp) x).hasFDerivAt).mul'
    ((hg.differentiable (by simp) x).hasFDerivAt)
  change HasFDerivAt (fun y => f y*g y) _ x at hd
  simp only [spatialWordPartial]
  rw [hd.fderiv]
  simp [add_comm,mul_comm]

/-- Actual integration by parts with the correct normalized frequency L*k.
Only smoothness and true unit periodicity are hypotheses. -/
theorem unitFourierCoefficient_partial (f : SpatialPoint → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : IsUnitPeriodicField f) (k : SpatialFrequency) (i : Fin 3) :
    unitFourierCoefficient (spatialWordPartial f [i])
      (contDiff_spatialWordPartial f hf [i]).continuous
      (unitPeriodicField_spatialWordPartial f hf hp [i]) k=
      ((physicalPeriod : ℂ)*Complex.I*(k i : ℂ))*unitFourierCoefficient f hf.continuous hp k := by
  let c : ℂ := (physicalPeriod : ℂ)*Complex.I*(k i : ℂ)
  let e := unitFourierMode (-k)
  have he : ContDiff ℝ ∞ e := contDiff_unitFourierMode (-k)
  let h := fun x => e x*f x
  have hh : ContDiff ℝ ∞ h := he.mul hf
  have hperiod : IsUnitPeriodicField h := by
    intro x n
    change e (x+unitIntegerShift n)*f (x+unitIntegerShift n)=e x*f x
    change unitFourierMode (-k) (x+unitIntegerShift n)*f (x+unitIntegerShift n)=unitFourierMode (-k) x*f x
    rw [unitFourierMode_periodic (-k) x n,hp x n]
  have hcneg : ((physicalPeriod : ℂ)*Complex.I*((-k) i : ℂ))= -c := by simp [c]
  have hpartial : spatialWordPartial h [i]=fun x =>
      (-c)*(e x*f x)+e x*spatialWordPartial f [i] x := by
    rw [spatialWordPartial_complex_mul_first e f he hf i,unitFourierMode_first]
    funext x
    rw [hcneg]
    ring
  have hz := unitComplexCubeIntegral_partial_periodic h hh hperiod i
  have hA := unitComplexCubeIntegral_add
    (fun x => (-c)*(e x*f x)) (fun x => e x*spatialWordPartial f [i] x)
    ((he.continuous.mul hf.continuous).const_mul (-c))
    (he.continuous.mul (contDiff_spatialWordPartial f hf [i]).continuous)
  rw [hpartial,hA,unitComplexCubeIntegral_const_mul] at hz
  rw [unitFourierCoefficient_eq_cubeIntegral,unitFourierCoefficient_eq_cubeIntegral]
  change unitComplexCubeIntegral (fun x => e x*spatialWordPartial f [i] x)=
    c*unitComplexCubeIntegral (fun x => e x*f x)
  linear_combination hz

end Qatlib.Concepts.EffectiveGauge.TorusFourier
