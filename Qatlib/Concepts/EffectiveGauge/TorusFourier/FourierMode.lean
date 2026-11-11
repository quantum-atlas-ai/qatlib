/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.WordProduct
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Fourier.AddCircleMulti

/-! # Actual normalized Fourier modes and their spatial derivatives -/
set_option autoImplicit false
noncomputable section
open scoped ContDiff
open Finset
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Abbreviation for Spatial Frequency in the Torus Fourier construction. -/
abbrev SpatialFrequency := Fin 3 → ℤ

/-- Definition of frequency Linear in the Torus Fourier construction. -/
def frequencyLinear (k : SpatialFrequency) : SpatialPoint →L[ℝ] ℝ :=
  ∑ j : Fin 3, (k j : ℝ) • (EuclideanSpace.proj j : SpatialPoint →L[ℝ] ℝ)

/-- Original `frequencyLinear_apply` guarantee for the `FourierMode` construction; the complete source hypotheses are retained. -/
theorem frequencyLinear_apply (k : SpatialFrequency) (x : SpatialPoint) :
    frequencyLinear k x=∑ j : Fin 3, (k j : ℝ)*x j := by
  simp [frequencyLinear]

/-- Original `frequencyLinear_axis` guarantee for the `FourierMode` construction; the complete source hypotheses are retained. -/
theorem frequencyLinear_axis (k : SpatialFrequency) (i : Fin 3) :
    frequencyLinear k (EuclideanSpace.single i 1)=(k i : ℝ) := by
  simp [frequencyLinear_apply]

/-- Definition of fourier Mode Exponent in the Torus Fourier construction. -/
def fourierModeExponent (k : SpatialFrequency) : SpatialPoint →L[ℝ] ℂ :=
  ((physicalPeriod : ℂ)*Complex.I) • (Complex.ofRealCLM.comp (frequencyLinear k))

/-- Definition of unit Fourier Mode in the Torus Fourier construction. -/
def unitFourierMode (k : SpatialFrequency) (x : SpatialPoint) : ℂ :=
  Complex.exp (fourierModeExponent k x)

/-- Original `unitFourierMode_zero` guarantee for the `FourierMode` construction; the complete source hypotheses are retained. -/
theorem unitFourierMode_zero : unitFourierMode 0=fun _ => (1 : ℂ) := by
  funext x
  simp [unitFourierMode,fourierModeExponent,frequencyLinear_apply]

/-- Original `contDiff_unitFourierMode` guarantee for the `FourierMode` construction; the complete source hypotheses are retained. -/
theorem contDiff_unitFourierMode (k : SpatialFrequency) : ContDiff ℝ ∞ (unitFourierMode k) :=
  (fourierModeExponent k).contDiff.cexp

/-- Original `unitFourierMode_norm` guarantee for the `FourierMode` construction; the complete source hypotheses are retained. -/
theorem unitFourierMode_norm (k : SpatialFrequency) (x : SpatialPoint) : ‖unitFourierMode k x‖=1 := by
  simp [unitFourierMode,Complex.norm_exp,fourierModeExponent]

/-- Original `unitFourierMode_first` guarantee for the `FourierMode` construction; the complete source hypotheses are retained. -/
theorem unitFourierMode_first (k : SpatialFrequency) (i : Fin 3) :
    spatialWordPartial (unitFourierMode k) [i]=fun x =>
      ((physicalPeriod : ℂ)*Complex.I*(k i : ℂ))*unitFourierMode k x := by
  funext x
  have hd := (fourierModeExponent k).hasFDerivAt.cexp (x := x)
  change HasFDerivAt (unitFourierMode k) _ x at hd
  change fderiv ℝ (unitFourierMode k) x (EuclideanSpace.single i 1)=_
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul,fourierModeExponent,
    ContinuousLinearMap.comp_apply,Complex.ofRealCLM_apply,frequencyLinear_axis,
    Complex.ofReal_intCast,unitFourierMode]
  ring


/-- Definition of unit Mode Word Factor in the Torus Fourier construction. -/
def unitModeWordFactor (k : SpatialFrequency) (w : List (Fin 3)) : ℂ :=
  (w.map (fun i => (physicalPeriod : ℂ)*Complex.I*(k i : ℂ))).prod

/-- Every ordered coordinate word has its actual Fourier eigenfactor. -/
theorem unitFourierMode_word (k : SpatialFrequency) (w : List (Fin 3)) :
    spatialWordPartial (unitFourierMode k) w=fun x => unitModeWordFactor k w*unitFourierMode k x := by
  induction w using List.reverseRecOn with
  | nil => simp only [spatialWordPartial,unitModeWordFactor,List.map_nil,List.prod_nil,one_mul]
  | append_singleton w i ih =>
    let c : ℂ := (physicalPeriod : ℂ)*Complex.I*(k i : ℂ)
    let A : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.mul ℝ ℂ) c
    have hclm := spatialWordPartial_clm A (unitFourierMode k) (contDiff_unitFourierMode k) w
    change spatialWordPartial (fun x => c*unitFourierMode k x) w=
      (fun x => c*spatialWordPartial (unitFourierMode k) w x) at hclm
    rw [spatialWordPartial_append,unitFourierMode_first,hclm,ih]
    funext x
    simp only [unitModeWordFactor,List.map_append,List.prod_append,List.map_singleton,List.prod_singleton]
    dsimp only [c]
    ring

/-- This is the same torus Fourier character used by the pinned inversion
 theorem, evaluated at the real quotient coordinates with period one. -/
theorem unitFourierMode_eq_mFourier (k : SpatialFrequency) (x : SpatialPoint) :
    unitFourierMode k x=UnitAddTorus.mFourier k (fun j => (x j : UnitAddCircle)) := by
  simp only [UnitAddTorus.mFourier,ContinuousMap.coe_mk,fourier_coe_apply]
  rw [← Complex.exp_sum]
  apply congrArg Complex.exp
  simp only [fourierModeExponent,ContinuousLinearMap.smul_apply,smul_eq_mul,
    ContinuousLinearMap.comp_apply,Complex.ofRealCLM_apply,frequencyLinear_apply,
    Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_intCast]
  dsimp only [physicalPeriod]
  push_cast
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro j hj
  ring


/-- Definition of unit Integer Shift in the Torus Fourier construction. -/
def unitIntegerShift (n : SpatialFrequency) : SpatialPoint := WithLp.toLp 2 (fun j => (n j : ℝ))

/-- Definition of Is Unit Periodic Field in the Torus Fourier construction. -/
def IsUnitPeriodicField {E : Type*} (f : SpatialPoint → E) : Prop :=
  ∀ x n, f (x+unitIntegerShift n)=f x

/-- Original `unitFourierMode_periodic` guarantee for the `FourierMode` construction; the complete source hypotheses are retained. -/
theorem unitFourierMode_periodic (k : SpatialFrequency) : IsUnitPeriodicField (unitFourierMode k) := by
  intro x n
  rw [unitFourierMode_eq_mFourier,unitFourierMode_eq_mFourier]
  apply congrArg (UnitAddTorus.mFourier k)
  funext j
  change ((x j+(n j : ℝ) : ℝ) : UnitAddCircle)=(x j : UnitAddCircle)
  have hn : ((n j : ℝ) : UnitAddCircle)=0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨n j,by simp⟩
  rw [AddCircle.coe_add,hn,add_zero]

/-- Physical L-periodicity becomes unit integer periodicity under precisely
 the rescaling used by the actual source reference. -/
theorem periodicField_rescale_unit {E : Type*} (f : SpatialPoint → E) (hp : IsPeriodicField f) :
    IsUnitPeriodicField (fun x => f (physicalPeriod • x)) := by
  intro x n
  have heq : physicalPeriod • (x+unitIntegerShift n)=physicalPeriod • x+latticeShift n := by
    ext j
    simp only [PiLp.smul_apply,PiLp.add_apply,unitIntegerShift,latticeShift,
      smul_eq_mul]
    ring
  change f (physicalPeriod • (x+unitIntegerShift n))=f (physicalPeriod • x)
  rw [heq]
  exact hp _ _

end Qatlib.Concepts.EffectiveGauge.TorusFourier
