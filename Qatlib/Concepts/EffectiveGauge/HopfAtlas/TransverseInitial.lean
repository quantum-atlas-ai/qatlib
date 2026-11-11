/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceWord

/-! # Initial-plane coordinate derivatives of the actual smooth transport -/
set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Differentiating in a transverse coordinate stays inside the initial plane.
No differentiation of the discontinuous wrapping map is involved. -/
theorem spatialPartial_of_plane_constant {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SpatialPoint → E) (hf : ContDiff ℝ ∞ f) (c : E)
    (hplane : ∀ x : SpatialPoint, x 0=0 → f x=c)
    (x : SpatialPoint) (hx : x 0=0) (i : Fin 3) (hi : i≠0) :
    spatialWordPartial f [i] x=0 := by
  let line : ℝ → SpatialPoint := fun t => x+t • EuclideanSpace.single i 1
  have hline : HasDerivAt line (EuclideanSpace.single i 1) 0 := by
    convert (hasDerivAt_const (0 : ℝ) x).add
      ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single i (1 : ℝ))) using 1 <;>
      first | rfl | simp only [zero_add,one_smul]
  have hcomp := ((hf.differentiable (by simp) (line 0)).hasFDerivAt).comp_hasDerivAt (0 : ℝ) hline
  have heq : (fun t : ℝ => f (line t))=fun _ => c := by
    funext t
    apply hplane
    simp [line,hx,Ne.symm hi]
  change HasDerivAt (fun t => f (line t)) _ (0 : ℝ) at hcomp
  rw [heq] at hcomp
  have hzero := (hasDerivAt_const (0 : ℝ) c).unique hcomp
  simpa [spatialWordPartial,line] using hzero.symm

/-- All positive pure transverse words have zero initial data, as needed by
inhomogeneous transport of arbitrary-order parameter derivatives. -/
theorem spatialWordPartial_plane_constant {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SpatialPoint → E) (hf : ContDiff ℝ ∞ f) (c : E)
    (hplane : ∀ x : SpatialPoint, x 0=0 → f x=c)
    (w : List (Fin 3)) (htrans : ∀ i ∈ w, i≠0) (hw : w≠[])
    (x : SpatialPoint) (hx : x 0=0) : spatialWordPartial f w x=0 := by
  induction w generalizing x with
  | nil => exact (hw rfl).elim
  | cons i w ih =>
    have hi : i≠0 := htrans i (by simp)
    have hwt : ∀ j ∈ w, j≠0 := fun j hj => htrans j (by simp [hj])
    by_cases he : w=[]
    · subst w
      exact spatialPartial_of_plane_constant f hf c hplane x hx i hi
    · have hwp : ∀ y : SpatialPoint, y 0=0 → spatialWordPartial f w y=0 :=
        fun y hy => ih hwt he y hy
      exact spatialPartial_of_plane_constant (spatialWordPartial f w)
        (contDiff_spatialWordPartial f hf w) 0 hwp x hx i hi

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
