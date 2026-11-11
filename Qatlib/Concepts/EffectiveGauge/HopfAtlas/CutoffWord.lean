/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.CutoffTransition
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceWord
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.ReferenceRescaling
import Mathlib.Data.List.Induction

set_option backward.isDefEq.respectTransparency false

/-! # Actual coordinate-word bounds for the same physical collar cutoff -/
set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Original `spatialWordPartial_coordinate_first` guarantee for the `CutoffWord` construction; the complete source hypotheses are retained. -/
theorem spatialWordPartial_coordinate_first (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (j i : Fin 3) : spatialWordPartial (fun x : SpatialPoint => f (x j)) [i]=
      fun x => if i=j then deriv f (x j) else 0 := by
  funext x
  have hd := ((hf.differentiable (by simp) (x j)).hasDerivAt).hasFDerivAt.comp x
    (EuclideanSpace.proj j : SpatialPoint →L[ℝ] ℝ).hasFDerivAt
  change HasFDerivAt (fun y : SpatialPoint => f (y j)) _ x at hd
  change fderiv ℝ (fun y : SpatialPoint => f (y j)) x (EuclideanSpace.single i 1)=_
  rw [hd.fderiv]
  by_cases hi : i=j
  · subst i
    simp
  · simp [hi,Ne.symm hi]

/-- No operator norm or dimension factor is inserted. A word with a
transverse direction vanishes, and each parallel direction is one real derivative. -/
theorem spatialWordPartial_coordinate (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (j : Fin 3) (w : List (Fin 3)) :
    spatialWordPartial (fun x : SpatialPoint => f (x j)) w=
      fun x => if (∀ i ∈ w, i=j) then iteratedDeriv w.length f (x j) else 0 := by
  classical
  induction w using List.reverseRecOn generalizing f with
  | nil => funext x; simp only [spatialWordPartial,List.length_nil,iteratedDeriv_zero,List.not_mem_nil,false_implies,implies_true,ite_true]
  | append_singleton w i ih =>
    have hderiv : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
    rw [spatialWordPartial_append,spatialWordPartial_coordinate_first f hf j i]
    by_cases hi : i=j
    · subst i
      simp only [ite_true]
      rw [ih (deriv f) hderiv]
      have hpred : (∀ k ∈ w++[j], k=j) ↔ (∀ k ∈ w, k=j) := by
        simp only [List.mem_append,List.mem_singleton]
        constructor
        · intro h k hk
          exact h k (Or.inl hk)
        · intro h k hk
          rcases hk with hk|hk
          · exact h k hk
          · exact hk
      funext x
      simp only [List.length_append,List.length_singleton,iteratedDeriv_succ',hpred]
    · have heq : (fun x : SpatialPoint => if i=j then deriv f (x j) else 0)=fun _ => (0 : ℝ) := by
        simp only [if_neg hi]
      rw [heq,spatialWordPartial_const]
      funext x
      have hnot : ¬(∀ k ∈ w++[i], k=j) := fun h => hi (h i (by simp))
      simp only [if_neg hnot,ite_self]

/-- Definition of unit Cutoff Field in the Hopf Atlas construction. -/
def unitCutoffField (eta : ℝ) (x : SpatialPoint) : ℝ := unitGluingCutoff eta (x 0)

/-- Original `contDiff_unitCutoffField` guarantee for the `CutoffWord` construction; the complete source hypotheses are retained. -/
theorem contDiff_unitCutoffField (eta : ℝ) : ContDiff ℝ ∞ (unitCutoffField eta) :=
  (contDiff_unitGluingCutoff eta).comp
    (EuclideanSpace.proj (0 : Fin 3) : SpatialPoint →L[ℝ] ℝ).contDiff

/-- The actual normalized cutoff is the existing physical cutoff, with
physical collar width L*eta, in precisely the range used by the source frame. -/
theorem unitCutoffField_eq_physical (eta : ℝ) (he : 0<eta) (he1 : eta ≤ 1/2) (x : SpatialPoint) :
    unitCutoffField eta x=gluingCutoff (physicalPeriod*eta) (physicalPeriod*x 0) :=
  (gluingCutoff_scaled eta (x 0) he he1).symm

/-- Original `unitCutoffField_word_bound` guarantee for the `CutoffWord` construction; the complete source hypotheses are retained. -/
theorem unitCutoffField_word_bound (eta : ℚ) (he : 0<eta) (w : List (Fin 3)) (x : SpatialPoint) :
    ‖spatialWordPartial (unitCutoffField (eta : ℝ)) w x‖ ≤
      (cutoffUnitMajorant eta w.length : ℝ) := by
  have hD : (0 : ℝ) ≤ cutoffUnitMajorant eta w.length := by
    have heR : (0 : ℝ)<eta := Rat.cast_pos.mpr he
    by_cases hw : w.length=0
    · simp [cutoffUnitMajorant,hw]
    · simp only [cutoffUnitMajorant,if_neg hw,Rat.cast_mul,Rat.cast_pow,Rat.cast_div,
        Rat.cast_ofNat,Rat.cast_natCast]
      positivity
  change ‖spatialWordPartial (fun y : SpatialPoint => unitGluingCutoff (eta : ℝ) (y 0)) w x‖ ≤ _
  rw [spatialWordPartial_coordinate _ (contDiff_unitGluingCutoff (eta : ℝ))]
  by_cases hw : ∀ i ∈ w, i=(0 : Fin 3)
  · simpa only [if_pos hw,Real.norm_eq_abs] using unitGluingCutoff_derivative_bound eta he w.length (x 0)
  · simpa only [if_neg hw,norm_zero] using hD

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
