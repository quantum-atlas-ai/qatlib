/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.EffectiveGauge.HopfAtlas.WordProduct

@[expose] public section

/-! # Coordinate-face restrictions and quaternion-linear operations on actual words -/
set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Affine restriction to one fixed coordinate face, retaining all others. -/
def coordinateFace (j : Fin 3) (a : ℝ) (x : SpatialPoint) : SpatialPoint :=
  x+(a-x j) • EuclideanSpace.single j (1 : ℝ)

/-- Setting coordinate `j` to `a` makes the resulting value at `j` equal to `a`. -/
theorem coordinateFace_same (j : Fin 3) (a : ℝ) (x : SpatialPoint) : coordinateFace j a x j=a := by
  simp [coordinateFace]

/-- Setting coordinate `j` leaves the value at any different coordinate `i` unchanged. -/
theorem coordinateFace_other (j i : Fin 3) (a : ℝ) (x : SpatialPoint) (hi : i≠j) :
    coordinateFace j a x i=x i := by
  simp [coordinateFace,hi]

/-- The affine map setting a chosen spatial coordinate to a constant is smooth. -/
theorem contDiff_coordinateFace (j : Fin 3) (a : ℝ) : ContDiff ℝ ∞ (coordinateFace j a) :=
  contDiff_id.add ((contDiff_const.sub (EuclideanSpace.proj j : SpatialPoint →L[ℝ] ℝ).contDiff).smul contDiff_const)

/-- The Fréchet derivative of setting coordinate `j` to a constant is the linear projection that
subtracts the `j`-th axis component. -/
theorem coordinateFace_hasFDerivAt (j : Fin 3) (a : ℝ) (x : SpatialPoint) :
    HasFDerivAt (coordinateFace j a)
      (ContinuousLinearMap.id ℝ SpatialPoint-(EuclideanSpace.proj j : SpatialPoint →L[ℝ] ℝ).smulRight (EuclideanSpace.single j (1 : ℝ))) x := by
  apply ((hasFDerivAt_id x).add
    (((hasFDerivAt_const a x).sub (EuclideanSpace.proj j : SpatialPoint →L[ℝ] ℝ).hasFDerivAt).smul_const
      (EuclideanSpace.single j (1 : ℝ)))).congr_fderiv
  ext y
  simp [sub_eq_add_neg]

/-- The derivative projection of the coordinate-setting map kills the `j`-th coordinate unit vector
and fixes every other coordinate unit vector. -/
theorem coordinateFace_derivative_axis (j i : Fin 3) :
    (ContinuousLinearMap.id ℝ SpatialPoint-(EuclideanSpace.proj j : SpatialPoint →L[ℝ] ℝ).smulRight
      (EuclideanSpace.single j (1 : ℝ))) (EuclideanSpace.single i (1 : ℝ))=
        if i=j then 0 else EuclideanSpace.single i (1 : ℝ) := by
  by_cases h : i=j
  · subst i
    simp
  · simp [h,Ne.symm h]

/-- Only transverse words survive restriction to a fixed face. The same
ordered derivative is evaluated on that face, without an operator-norm loss. -/
theorem spatialWordPartial_coordinateFace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SpatialPoint → E) (hf : ContDiff ℝ ∞ f) (j : Fin 3) (a : ℝ) (w : List (Fin 3)) :
    spatialWordPartial (fun x => f (coordinateFace j a x)) w=
      fun x => if j ∈ w then 0 else spatialWordPartial f w (coordinateFace j a x) := by
  induction w with
  | nil => simp only [spatialWordPartial,List.not_mem_nil,ite_false]
  | cons i w ih =>
    funext x
    by_cases hw : j∈w
    · simp [spatialWordPartial,ih,hw]
    · have heq : (fun y => if j∈w then 0 else spatialWordPartial f w (coordinateFace j a y))=
          (fun y => spatialWordPartial f w (coordinateFace j a y)) := by simp only [ite_eq_right hw]
      simp only [spatialWordPartial,ih,heq]
      have hd := (((contDiff_spatialWordPartial f hf w).differentiable (by simp)
        (coordinateFace j a x)).hasFDerivAt).comp x (coordinateFace_hasFDerivAt j a x)
      change HasFDerivAt (fun y => spatialWordPartial f w (coordinateFace j a y)) _ x at hd
      rw [hd.fderiv]
      simp only [ContinuousLinearMap.comp_apply,coordinateFace_derivative_axis]
      by_cases hi : i=j
      · subst i
        simp
      · simp [hi,Ne.symm hi,hw]

/-- Quaternion conjugation commutes with real scalar multiplication. -/
local instance : StarModule ℝ ℍ where
  star_smul r q := by ext <;> simp

/-- Taking quaternion conjugates commutes with every coordinate-word derivative of a smooth
quaternion field. -/
theorem spatialWordPartial_star (f : SpatialPoint → ℍ) (hf : ContDiff ℝ ∞ f) (w : List (Fin 3)) :
    spatialWordPartial (fun x => star (f x)) w=fun x => star (spatialWordPartial f w x) :=
  spatialWordPartial_clm (starL' ℝ : ℍ ≃L[ℝ] ℍ).toContinuousLinearMap f hf w

/-- Every coordinate-word derivative of a smooth quaternion field commutes with right
multiplication by a fixed quaternion. -/
theorem spatialWordPartial_mul_const (f : SpatialPoint → ℍ) (hf : ContDiff ℝ ∞ f)
    (c : ℍ) (w : List (Fin 3)) :
    spatialWordPartial (fun x => f x*c) w=fun x => spatialWordPartial f w x*c :=
  spatialWordPartial_clm ((ContinuousLinearMap.mul ℝ ℍ).flip c) f hf w

/-- Every coordinate-word derivative of a smooth quaternion field commutes with left multiplication
by a fixed quaternion. -/
theorem spatialWordPartial_const_mul (f : SpatialPoint → ℍ) (hf : ContDiff ℝ ∞ f)
    (c : ℍ) (w : List (Fin 3)) :
    spatialWordPartial (fun x => c*f x) w=fun x => c*spatialWordPartial f w x :=
  spatialWordPartial_clm ((ContinuousLinearMap.mul ℝ ℍ) c) f hf w

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
