/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.WordAngular
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.UnitSourceWord

set_option backward.isDefEq.respectTransparency false

/-! # True connection derivatives from coordinate-word lift bounds -/
set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Quaternion conjugation commutes with real scalar multiplication. -/
local instance : StarModule ℝ ℍ where
  star_smul r q := by ext <;> simp

/-- Definition of quaternion Re Coordinate in the Hopf Atlas construction. -/
def quaternionReCoordinate : ℍ →L[ℝ] ℝ :=
  (EuclideanSpace.proj (0 : Fin 4)).comp Quaternion.linearIsometryEquivTuple.toContinuousLinearMap

/-- Original `quaternion_re_abs_le_norm` guarantee for the `WordConnection` construction; the complete source hypotheses are retained. -/
theorem quaternion_re_abs_le_norm (q : ℍ) : |q.re| ≤ ‖q‖ := by
  apply (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
  rw [sq_abs,pow_two,pow_two,← Quaternion.normSq_eq_norm_mul_self,Quaternion.normSq_def']
  nlinarith [sq_nonneg q.imI,sq_nonneg q.imJ,sq_nonneg q.imK]

/-- Original `connection_eq_real_product` guarantee for the `WordConnection` construction; the complete source hypotheses are retained. -/
theorem connection_eq_real_product (q : QuaternionField) (i : Fin 3) :
    (fun x => connection q x i)=fun x => quaternionReCoordinate
      ((iAxis*q x)*star (spatialWordPartial q [i] x)) := by
  funext x
  simp only [connection,spatialPartial,connectionValue,Quaternion.inner_def,spatialWordPartial]
  rfl

/-- Original `connection_word_bound` guarantee for the `WordConnection` construction; the complete source hypotheses are retained. -/
theorem connection_word_bound (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (i : Fin 3) (F : ℕ → ℝ) (w : List (Fin 3)) (x : SpatialPoint)
    (hb : ∀ z : List (Fin 3), z.length ≤ w.length+1 → ‖spatialWordPartial q z x‖ ≤ F z.length) :
    ‖spatialWordPartial (fun y => connection q y i) w x‖ ≤
      wordProductMajorant F (fun j => F (j+1)) w.length := by
  let f := fun y => iAxis*q y
  let g := fun y => star (spatialWordPartial q [i] y)
  have hf : ContDiff ℝ ∞ f := contDiff_const.mul hq
  have hg : ContDiff ℝ ∞ g := (starL' ℝ : ℍ ≃L[ℝ] ℍ).toContinuousLinearMap.contDiff.comp
    (contDiff_spatialWordPartial q hq [i])
  have hF (j : ℕ) (hj : j ≤ w.length+1) : 0 ≤ F j := by
    simpa only [List.length_replicate] using (norm_nonneg _).trans (hb (List.replicate j 0) (by simpa))
  have hFB (z : List (Fin 3)) (hz : z.length ≤ w.length) : ‖spatialWordPartial f z x‖ ≤ F z.length := by
    change ‖spatialWordPartial (fun y => iAxis*q y) z x‖ ≤ _
    rw [spatialWordPartial_const_mul q hq,norm_mul,norm_iAxis,one_mul]
    exact hb z (by omega)
  have hGB (z : List (Fin 3)) (hz : z.length ≤ w.length) : ‖spatialWordPartial g z x‖ ≤ F (z.length+1) := by
    change ‖spatialWordPartial (fun y => star (spatialWordPartial q [i] y)) z x‖ ≤ _
    rw [spatialWordPartial_star _ (contDiff_spatialWordPartial q hq [i]),Quaternion.norm_star,
      ← spatialWordPartial_append]
    simpa only [List.length_append,List.length_singleton] using hb (z++[i]) (by simp; omega)
  rw [connection_eq_real_product,spatialWordPartial_clm _ _ (hf.mul hg)]
  exact (quaternion_re_abs_le_norm _).trans
    (spatialWordPartial_mul_norm_le f g hf hg F (fun j => F (j+1)) w x
      (fun j hj => hF j (by omega)) (fun j hj => hF (j+1) (by omega)) hFB hGB)

/-- The normalized connection is L times the physical one, including every
coordinate direction. This factor is used in the normalized Poisson equation. -/
theorem connection_scale (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (L : ℝ) (x : SpatialPoint) (i : Fin 3) :
    connection (fun y => q (L • y)) x i=L*connection q (L • x) i := by
  change connectionValue (q (L • x)) (spatialWordPartial (fun y => q (L • y)) [i] x)=_
  rw [spatialWordPartial_scale q hq]
  simp only [List.length_singleton,pow_one,connectionValue,inner_smul_right]
  rfl

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
