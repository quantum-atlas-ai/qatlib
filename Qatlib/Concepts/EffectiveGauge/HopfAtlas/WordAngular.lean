/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.WordAffine

set_option backward.isDefEq.respectTransparency false

/-! # Binomial bounds for the actual circle angular derivative -/
set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Quaternion conjugation commutes with real scalar multiplication. -/
local instance : StarModule ℝ ℍ where
  star_smul r q := by ext <;> simp

/-- Imaginary coordinate one as a continuous real linear functional. -/
def quaternionImICoordinate : ℍ →L[ℝ] ℝ :=
  (EuclideanSpace.proj (1 : Fin 4)).comp Quaternion.linearIsometryEquivTuple.toContinuousLinearMap

/-- Original `quaternion_imI_abs_le_norm` guarantee for the `WordAngular` construction; the complete source hypotheses are retained. -/
theorem quaternion_imI_abs_le_norm (q : ℍ) : |q.imI| ≤ ‖q‖ := by
  apply (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
  rw [sq_abs,pow_two,pow_two,← Quaternion.normSq_eq_norm_mul_self,Quaternion.normSq_def']
  nlinarith [sq_nonneg q.re,sq_nonneg q.imJ,sq_nonneg q.imK]

/-- Spatial extension of the circle angular derivative in one coordinate. -/
def wordAngularRate (g : SpatialPoint → ℍ) (i : Fin 3) (x : SpatialPoint) : ℝ :=
  (star (g x)*spatialWordPartial g [i] x).imI

/-- Original `contDiff_wordAngularRate` guarantee for the `WordAngular` construction; the complete source hypotheses are retained. -/
theorem contDiff_wordAngularRate (g : SpatialPoint → ℍ) (hg : ContDiff ℝ ∞ g) (i : Fin 3) :
    ContDiff ℝ ∞ (wordAngularRate g i) :=
  quaternionImICoordinate.contDiff.comp
    (((starL' ℝ : ℍ ≃L[ℝ] ℍ).toContinuousLinearMap.contDiff.comp hg).mul
      (contDiff_spatialWordPartial g hg [i]))

/-- Original `wordAngularRate_word_bound` guarantee for the `WordAngular` construction; the complete source hypotheses are retained. -/
theorem wordAngularRate_word_bound (g : SpatialPoint → ℍ) (hg : ContDiff ℝ ∞ g)
    (i : Fin 3) (F : ℕ → ℝ) (w : List (Fin 3)) (x : SpatialPoint)
    (hb : ∀ u : List (Fin 3), u.length ≤ w.length+1 →
      ‖spatialWordPartial g u x‖ ≤ F u.length) :
    ‖spatialWordPartial (wordAngularRate g i) w x‖ ≤
      wordProductMajorant F (fun j => F (j+1)) w.length := by
  have hF (j : ℕ) (hj : j ≤ w.length+1) : 0 ≤ F j := by
    have h := hb (List.replicate j 0) (by simpa using hj)
    exact (norm_nonneg _).trans (by simpa only [List.length_replicate] using h)
  have hs : ContDiff ℝ ∞ (fun y => star (g y)) :=
    (starL' ℝ : ℍ ≃L[ℝ] ℍ).toContinuousLinearMap.contDiff.comp hg
  have hd := contDiff_spatialWordPartial g hg [i]
  have hsB : ∀ u : List (Fin 3), u.length ≤ w.length →
      ‖spatialWordPartial (fun y => star (g y)) u x‖ ≤ F u.length := by
    intro u hu
    rw [spatialWordPartial_star g hg,Quaternion.norm_star]
    exact hb u (hu.trans (Nat.le_succ _))
  have hdB : ∀ u : List (Fin 3), u.length ≤ w.length →
      ‖spatialWordPartial (spatialWordPartial g [i]) u x‖ ≤ F (u.length+1) := by
    intro u hu
    rw [← spatialWordPartial_append]
    have hlen : (u++[i]).length=u.length+1 := by simp
    exact (hb (u++[i]) (by simpa using Nat.add_le_add_right hu 1)).trans_eq (congrArg F hlen)
  have hp := spatialWordPartial_mul_norm_le _ _ hs hd F (fun j => F (j+1)) w x
    (fun j hj => hF j (hj.trans (Nat.le_succ _)))
    (fun j hj => hF (j+1) (Nat.add_le_add_right hj 1)) hsB hdB
  change ‖spatialWordPartial (fun y => quaternionImICoordinate
    (star (g y)*spatialWordPartial g [i] y)) w x‖ ≤ _
  rw [spatialWordPartial_clm _ _ (hs.mul hd)]
  exact (quaternion_imI_abs_le_norm _).trans hp

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
