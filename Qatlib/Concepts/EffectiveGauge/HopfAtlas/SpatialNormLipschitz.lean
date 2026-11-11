/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.MeanLipschitz

set_option backward.isDefEq.respectTransparency false

/-!
# Spatial Norm Lipschitz

Hopf Atlas constructions for Effective Gauge.
Proves `spatialAxes_norm_l1_bound`, `spatial_partial_norm_lipschitz`.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Original `spatialAxes_norm_l1_bound` guarantee for the `SpatialNormLipschitz` construction; the complete source hypotheses are retained. -/
theorem spatialAxes_norm_l1_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : SpatialPoint →L[ℝ] E) (D : ℝ) (_hD : 0 ≤ D)
    (hA : ∀ i, ‖A (EuclideanSpace.single i 1)‖ ≤ D) (w : SpatialPoint) :
    ‖A w‖ ≤ D*(|w 0|+|w 1|+|w 2|) := by
  have he : w=w 0 • EuclideanSpace.single 0 (1 : ℝ)+
      w 1 • EuclideanSpace.single 1 (1 : ℝ)+w 2 • EuclideanSpace.single 2 (1 : ℝ) := by
    ext i
    fin_cases i <;> simp
  have hmap : A w=w 0 • A (EuclideanSpace.single 0 1)+
      w 1 • A (EuclideanSpace.single 1 1)+w 2 • A (EuclideanSpace.single 2 1) := by
    conv_lhs => rw [he]
    simp only [map_add,map_smul]
  rw [hmap]
  calc
    _ ≤ |w 0| * ‖A (EuclideanSpace.single 0 1)‖+
        |w 1| * ‖A (EuclideanSpace.single 1 1)‖+
        |w 2| * ‖A (EuclideanSpace.single 2 1)‖ := by
      simpa only [norm_smul,Real.norm_eq_abs] using
        (norm_add_le (w 0 • A (EuclideanSpace.single 0 1)+w 1 • A (EuclideanSpace.single 1 1))
          (w 2 • A (EuclideanSpace.single 2 1))).trans
          (add_le_add (norm_add_le (w 0 • A (EuclideanSpace.single 0 1))
            (w 1 • A (EuclideanSpace.single 1 1))) le_rfl)
    _ ≤ |w 0| * D+|w 1| * D+|w 2| * D := add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left (hA 0) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (hA 1) (abs_nonneg _)))
      (mul_le_mul_of_nonneg_left (hA 2) (abs_nonneg _))
    _ = _ := by ring

/-- A global coordinate derivative bound controls arbitrary addresses,
without making an exact fundamental-domain decision at irrational L. -/
theorem spatial_partial_norm_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SpatialPoint → E) (hf : ContDiff ℝ ∞ f)
    (D : ℝ) (hD : 0 ≤ D)
    (hpartial : ∀ x i, ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ ≤ D)
    (a b : SpatialPoint) :
    ‖f a-f b‖ ≤ D*(|a 0-b 0|+|a 1-b 1|+|a 2-b 2|) := by
  let path := fun t : ℝ => (1-t) • a+t • b
  let g := fun t : ℝ => f (path t)
  have hder (t : ℝ) : HasDerivAt g (fderiv ℝ f (path t) (b-a)) t := by
    have hline := (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).smul_const a).add
      ((hasDerivAt_id t).smul_const b)
    have hd : HasDerivAt path (b-a) t := by
      convert hline using 1 <;> first | rfl | simp [path,sub_eq_add_neg,add_comm]
    exact ((hf.differentiable (by simp) (path t)).hasFDerivAt.comp_hasDerivAt t hd)
  have hbound (t : ℝ) (_ht : t ∈ Ico (0 : ℝ) 1) :
      ‖fderiv ℝ f (path t) (b-a)‖ ≤ D*(|a 0-b 0|+|a 1-b 1|+|a 2-b 2|) := by
    have h := spatialAxes_norm_l1_bound (fderiv ℝ f (path t)) D hD (hpartial (path t)) (b-a)
    change ‖fderiv ℝ f (path t) (b-a)‖ ≤ D*(|b 0-a 0|+|b 1-a 1|+|b 2-a 2|) at h
    simpa only [abs_sub_comm] using h
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hder t).hasDerivWithinAt) hbound
  simpa only [g,path,sub_self,zero_smul,one_smul,zero_add,sub_zero,add_zero,
    norm_sub_rev,abs_sub_comm] using h

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
