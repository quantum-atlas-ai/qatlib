/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.MeanLipschitz
import Mathlib.Analysis.Complex.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Complex Lipschitz

Hopf Atlas constructions for Effective Gauge.
Proves `complex_axes_l1_bound`, `unitCube_complex_partial_lipschitz`.
-/

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Original `complex_axes_l1_bound` guarantee for the `ComplexLipschitz` construction; the complete source hypotheses are retained. -/
private theorem complex_axes_l1_bound (A : SpatialPoint →L[ℝ] ℂ) (D : ℝ) (_hD : 0 ≤ D)
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
    _ ≤ ‖w 0 • A (EuclideanSpace.single 0 1)‖+
        ‖w 1 • A (EuclideanSpace.single 1 1)‖+‖w 2 • A (EuclideanSpace.single 2 1)‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = |w 0| * ‖A (EuclideanSpace.single 0 1)‖+
        |w 1| * ‖A (EuclideanSpace.single 1 1)‖+|w 2| * ‖A (EuclideanSpace.single 2 1)‖ := by
      simp only [norm_smul,Real.norm_eq_abs]
    _ ≤ |w 0| * D+|w 1| * D+|w 2| * D := add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left (hA 0) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (hA 1) (abs_nonneg _)))
      (mul_le_mul_of_nonneg_left (hA 2) (abs_nonneg _))
    _ = _ := by ring

/-- A straight segment and the true derivative give the L1 modulus with the
same constant D. An additional Euclidean dimension factor is unnecessary. -/
theorem unitCube_complex_partial_lipschitz (f : SpatialPoint → ℂ) (hf : ContDiff ℝ ∞ f)
    (D : ℝ) (hD : 0 ≤ D)
    (hpartial : ∀ x, InUnitCube x → ∀ i,
      ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ ≤ D)
    (p q : MeanTensorPoint) (hp : meanTensorInCube p) (hq : meanTensorInCube q) :
    ‖f (meanTensorSpatial p)-f (meanTensorSpatial q)‖ ≤ D*meanTensorDistance p q := by
  let a := meanTensorSpatial p
  let b := meanTensorSpatial q
  let path := fun t : ℝ => (1-t) • a+t • b
  let g := fun t : ℝ => f (path t)
  have ha : InUnitCube a := meanTensorSpatial_inCube p hp
  have hb : InUnitCube b := meanTensorSpatial_inCube q hq
  have hpath (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : InUnitCube (path t) := by
    intro i
    change 0 ≤ (1-t)*a i+t*b i ∧ (1-t)*a i+t*b i ≤ 1
    constructor
    · exact add_nonneg (mul_nonneg (by linarith [ht.2]) (ha i).1) (mul_nonneg ht.1 (hb i).1)
    · nlinarith [mul_nonneg (by linarith [ht.2] : 0 ≤ 1-t) (sub_nonneg.mpr (ha i).2),
        mul_nonneg ht.1 (sub_nonneg.mpr (hb i).2)]
  have hder (t : ℝ) : HasDerivAt g (fderiv ℝ f (path t) (b-a)) t := by
    have hline := (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).smul_const a).add
      ((hasDerivAt_id t).smul_const b)
    have hd : HasDerivAt path (b-a) t := by
      convert hline using 1 <;> first | rfl | simp [path,sub_eq_add_neg,add_comm]
    exact ((hf.differentiable (by simp) (path t)).hasFDerivAt.comp_hasDerivAt t hd)
  have hbound (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      ‖fderiv ℝ f (path t) (b-a)‖ ≤ D*meanTensorDistance p q := by
    have h := complex_axes_l1_bound (fderiv ℝ f (path t)) D hD
      (hpartial _ (hpath t ⟨ht.1,ht.2.le⟩)) (b-a)
    change ‖fderiv ℝ f (path t) (b-a)‖ ≤ D*(|q.1-p.1|+|q.2.1-p.2.1|+|q.2.2-p.2.2|) at h
    simpa only [meanTensorDistance,abs_sub_comm] using h
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hder t).hasDerivWithinAt) hbound
  simpa only [g,path,sub_self,zero_smul,one_smul,zero_add,sub_zero,add_zero,
    norm_sub_rev] using h

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
