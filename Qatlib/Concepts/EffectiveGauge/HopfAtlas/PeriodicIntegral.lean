/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.MeanIntegral

set_option backward.isDefEq.respectTransparency false

/-! Opposite periodic faces cancel; no flat-collar premise is used. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff BigOperators
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow
/-- Abbreviation for Coordinate Point in the Hopf Atlas construction. -/
private abbrev CoordinatePoint := Fin 3 → ℝ
/-- Definition of coordinate Top in the Hopf Atlas construction. -/
private def coordinateTop : CoordinatePoint := fun _ => physicalPeriod

/-- Original `scalar_partial_integral_paired_faces` guarantee for the `PeriodicIntegral` construction; the complete source hypotheses are retained. -/
private theorem scalar_partial_integral_paired_faces (f : CoordinatePoint → ℝ) (hf : ContDiff ℝ ∞ f)
    (hfaces : ∀ (j : Fin 3) (y : Fin 2 → ℝ),
      f (j.insertNth physicalPeriod y)=f (j.insertNth 0 y)) (i : Fin 3) :
    (∫ x in Icc (0 : CoordinatePoint) coordinateTop,
      fderiv ℝ f x (Pi.single i 1))=0 := by
  let fs : Fin 3 → CoordinatePoint → ℝ := fun j => if j=i then f else fun _ => 0
  let dfs : Fin 3 → CoordinatePoint → CoordinatePoint →L[ℝ] ℝ :=
    fun j => if j=i then fderiv ℝ f else fun _ => 0
  have hc (j : Fin 3) : ContinuousOn (fs j) (Icc (0 : CoordinatePoint) coordinateTop) := by
    by_cases h : j=i
    · simpa [fs,h] using hf.continuous.continuousOn
    · simp only [fs,h,ite_false]
      exact continuousOn_const
  have hd (x : CoordinatePoint) (j : Fin 3) : HasFDerivAt (fs j) (dfs j x) x := by
    by_cases h : j=i
    · simpa [fs,dfs,h] using (hf.differentiable (by simp) x).hasFDerivAt
    · simpa [fs,dfs,h] using hasFDerivAt_const (0 : ℝ) x
  have heq (x : CoordinatePoint) : (∑ j : Fin 3, dfs j x (Pi.single j 1))=
      fderiv ℝ f x (Pi.single i 1) := by
    have heach (j : Fin 3) : dfs j x (Pi.single j 1)=
        if j=i then fderiv ℝ f x (Pi.single j 1) else 0 := by
      by_cases h : j=i <;> simp [dfs,h]
    simp_rw [heach]
    simp
  have hi : IntegrableOn (fun x => ∑ j : Fin 3, dfs j x (Pi.single j 1))
      (Icc (0 : CoordinatePoint) coordinateTop) := by
    simp only [heq]
    exact (((hf.fderiv_right (m := ∞) (by rfl)).continuous).clm_apply continuous_const).integrableOn_Icc
  have hdiv := integral_divergence_of_hasFDerivAt_off_countable' (0 : CoordinatePoint) coordinateTop
    (by intro j; exact physicalPeriod_pos.le) fs dfs ∅ countable_empty hc (fun x _ j => hd x j) hi
  have hfrontback (j : Fin 3) :
      (∫ y in Icc ((0 : CoordinatePoint) ∘ j.succAbove) (coordinateTop ∘ j.succAbove),
        fs j (j.insertNth (coordinateTop j) y))=
      ∫ y in Icc ((0 : CoordinatePoint) ∘ j.succAbove) (coordinateTop ∘ j.succAbove),
        fs j (j.insertNth ((0 : CoordinatePoint) j) y) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro y _hy
    by_cases hji : j=i
    · simpa [fs,hji,coordinateTop] using hfaces j y
    · simp [fs,hji]
  simpa only [heq,hfrontback,sub_self,Finset.sum_const_zero] using hdiv

/-- Integrating a genuine partial of a smooth periodic scalar over the physical
cube gives zero by opposite-face cancellation, even when its boundary values
are nonzero. -/
theorem physicalCubeIntegral_partial_periodic (f : SpatialPoint → ℝ)
    (hf : ContDiff ℝ ∞ f) (hp : IsPeriodicField f) (i : Fin 3) :
    physicalCubeIntegral (fun x => fderiv ℝ f x (EuclideanSpace.single i 1))=0 := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have hc : ContDiff ℝ ∞ (fun x : CoordinatePoint => f (e x)) := hf.comp e.contDiff
  have hfaces (j : Fin 3) (y : Fin 2 → ℝ) :
      f (e (j.insertNth physicalPeriod y))=f (e (j.insertNth 0 y)) := by
    have hpoint : e (j.insertNth physicalPeriod y)=
        e (j.insertNth 0 y)+latticeShift (Pi.single j 1) := by
      change WithLp.toLp 2 (j.insertNth physicalPeriod y)=
        WithLp.toLp 2 (j.insertNth 0 y)+latticeShift (Pi.single j 1)
      apply PiLp.ext
      rw [Fin.forall_iff_succAbove j]
      constructor
      · simp [latticeShift]
      · intro k
        simp [latticeShift,Pi.single_apply,Fin.succAbove_ne]
    rw [hpoint]
    exact hp _ _
  have hder (x : CoordinatePoint) :
      fderiv ℝ (fun y => f (e y)) x (Pi.single i 1)=
        fderiv ℝ f (e x) (EuclideanSpace.single i 1) := by
    have hd := (hf.differentiable (by simp) (e x)).hasFDerivAt.comp x e.hasFDerivAt
    change fderiv ℝ (f ∘ e) x (Pi.single i 1)=_
    rw [hd.fderiv]
    rfl
  have h := scalar_partial_integral_paired_faces (fun x => f (e x)) hc hfaces i
  simp only [hder] at h
  exact h

/-- The actual physical mean, with its existing L-cubed normalization. -/
theorem physicalCubeMean_partial_periodic (f : SpatialPoint → ℝ)
    (hf : ContDiff ℝ ∞ f) (hp : IsPeriodicField f) (i : Fin 3) :
    physicalCubeMean (fun x => fderiv ℝ f x (EuclideanSpace.single i 1))=0 := by
  rw [physicalCubeMean,physicalCubeIntegral_partial_periodic f hf hp,zero_div]

/-- Actual Fréchet derivatives inherit the same integer-lattice periods. -/
theorem periodicField_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SpatialPoint → E) (hf : ContDiff ℝ ∞ f) (hp : IsPeriodicField f) :
    IsPeriodicField (fderiv ℝ f) := by
  intro x n
  have hcomp := (hf.differentiable (by simp) (x+latticeShift n)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).add_const (latticeShift n))
  have heq : (fun y => f (y+latticeShift n))=f := funext (fun y => hp y n)
  change HasFDerivAt (fun y => f (y+latticeShift n)) _ x at hcomp
  rw [heq] at hcomp
  simpa using hcomp.unique (hf.differentiable (by simp) x).hasFDerivAt

/-- The true connection of a smooth periodic lift is periodic; its boundary
values need not vanish. -/
theorem periodicField_connection (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hp : IsPeriodicField q) (j : Fin 3) : IsPeriodicField (fun x => connection q x j) := by
  intro x n
  have hd := periodicField_fderiv q hq hp x n
  change connectionValue (q (x+latticeShift n))
    ((fderiv ℝ q (x+latticeShift n)) (EuclideanSpace.single j 1))=connectionValue (q x)
      ((fderiv ℝ q x) (EuclideanSpace.single j 1))
  rw [hp x n,hd]

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
