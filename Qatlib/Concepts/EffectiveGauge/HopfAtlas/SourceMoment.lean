/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceJetCurvature
import Qatlib.Concepts.EffectiveGauge.RationalFlow.MeanCube

set_option backward.isDefEq.respectTransparency false

/-!
# Actual derivatives of the source-curvature moment

The cubic first-derivative term vanishes because the three exact derivatives
are tangent to the same unit two-sphere. This cancellation is not applied to
the noisy packets. It is the reason the original mean mesh needs only
`M1^2/2 + M1*M2`.
-/

set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- The half scalar triple product is controlled without unit/tangent assumptions. -/
theorem spinCurvatureValue_abs_le (s a b : ℍ) :
    |spinCurvatureValue s a b| ≤ ‖s‖*‖a‖*‖b‖/2 := by
  have hr : |(s*a*b).re| ≤ ‖s*a*b‖ := by
    simpa [Quaternion.inner_def] using abs_real_inner_le_norm (s*a*b) (1 : ℍ)
  rw [spinCurvatureValue,abs_div,abs_neg,abs_of_pos (by norm_num : (0 : ℝ)<2)]
  exact (div_le_div_of_nonneg_right hr (by norm_num)).trans_eq (by rw [norm_mul,norm_mul])

/-- Exact three-dimensional determinant identity before tangent specialization. -/
theorem spinCurvatureValue_normal_identity (s a b c : SpatialPoint) :
    inner ℝ s s*spinCurvatureValue (spinOfVector a) (spinOfVector b) (spinOfVector c)=
      inner ℝ s a*spinCurvatureValue (spinOfVector s) (spinOfVector b) (spinOfVector c)-
      inner ℝ s b*spinCurvatureValue (spinOfVector s) (spinOfVector a) (spinOfVector c)+
      inner ℝ s c*spinCurvatureValue (spinOfVector s) (spinOfVector a) (spinOfVector b) := by
  simp only [spinCurvatureValue_components,PiLp.inner_apply,RCLike.inner_apply,
    starRingEnd_apply,star_trivial,Fin.sum_univ_three]
  ring

/-- Original `spinCurvatureValue_three_tangents` guarantee for the `SourceMoment` construction; the complete source hypotheses are retained. -/
theorem spinCurvatureValue_three_tangents (s a b c : SpatialPoint) (hs : ‖s‖=1)
    (ha : inner ℝ s a=0) (hb : inner ℝ s b=0) (hc : inner ℝ s c=0) :
    spinCurvatureValue (spinOfVector a) (spinOfVector b) (spinOfVector c)=0 := by
  have h := spinCurvatureValue_normal_identity s a b c
  rw [real_inner_self_eq_norm_sq,hs,ha,hb,hc] at h
  simpa using h

/-- Tangency is obtained by differentiating the actual unit-source identity. -/
theorem source_unit_tangent (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ y, ‖v y‖=1) (x h : SpatialPoint) :
    inner ℝ (v x) (fderiv ℝ v x h)=0 := by
  have hd := (hv.differentiable (by simp) x).hasFDerivAt
  have hi := hd.inner ℝ hd
  have heq : (fun y => inner ℝ (v y) (v y))=(fun _ : SpatialPoint => (1 : ℝ)) := by
    funext y
    rw [real_inner_self_eq_norm_sq,hu y]
    norm_num
  rw [heq] at hi
  have he := congrArg (fun f : SpatialPoint →L[ℝ] ℝ => f h)
    (hi.unique (hasFDerivAt_const (1 : ℝ) x))
  have hs : inner ℝ (v x) (fderiv ℝ v x h)+inner ℝ (fderiv ℝ v x h) (v x)=0 := by
    simpa using he
  linarith [real_inner_comm (v x) (fderiv ℝ v x h)]

/-- Original `contDiff_sourceCurvature` guarantee for the `SourceMoment` construction; the complete source hypotheses are retained. -/
theorem contDiff_sourceCurvature (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (i j : Fin 3) : ContDiff ℝ ∞ (fun x => sourceCurvature v x i j) := by
  have hs := spinEmbedding.toContinuousLinearMap.contDiff.comp hv
  have hd (k : Fin 3) := spinEmbedding.toContinuousLinearMap.contDiff.comp
    ((hv.fderiv_right (m := ∞) (by rfl)).clm_apply (g := fun _ => EuclideanSpace.single k 1) contDiff_const)
  have h := ((hs.mul (hd i)).mul (hd j)).inner ℝ (contDiff_const (c := (1 : ℍ)))
  simpa [Quaternion.inner_def,sourceCurvature,spinCurvatureValue,spinEmbedding,Function.comp_def] using h.neg.div_const 2

/-- Differentiate all three factors of the exact curvature, before the unit
constraint removes the first factor's derivative. -/
theorem sourceCurvature_partial (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (x : SpatialPoint) (i j k : Fin 3) :
    fderiv ℝ (fun y => sourceCurvature v y i j) x (EuclideanSpace.single k 1)=
      spinCurvatureValue (spinOfVector (sourcePhysicalPartial v k x))
        (spinOfVector (sourcePhysicalPartial v i x)) (spinOfVector (sourcePhysicalPartial v j x))+
      spinCurvatureValue (spinOfVector (v x))
        (spinOfVector (fderiv ℝ (sourcePhysicalPartial v i) x (EuclideanSpace.single k 1)))
        (spinOfVector (sourcePhysicalPartial v j x))+
      spinCurvatureValue (spinOfVector (v x)) (spinOfVector (sourcePhysicalPartial v i x))
        (spinOfVector (fderiv ℝ (sourcePhysicalPartial v j) x (EuclideanSpace.single k 1))) := by
  have hd := (hv.differentiable (by simp) x).hasFDerivAt
  have hp (l : Fin 3) : HasFDerivAt (sourcePhysicalPartial v l)
      (fderiv ℝ (sourcePhysicalPartial v l) x) x :=
    (((hv.fderiv_right (m := ∞) (by rfl)).clm_apply contDiff_const).differentiable (by simp) x).hasFDerivAt
  have hs := spinEmbedding.toContinuousLinearMap.hasFDerivAt.comp x hd
  have hds (l : Fin 3) := spinEmbedding.toContinuousLinearMap.hasFDerivAt.comp x (hp l)
  have ht := (((hs.mul' (hds i)).mul' (hds j)).inner ℝ
    (hasFDerivAt_const (1 : ℍ) x)).neg.mul_const ((2 : ℝ)⁻¹)
  have hf : (fun y => -(inner ℝ (spinOfVector (v y)*spinOfVector (sourcePhysicalPartial v i y)*
      spinOfVector (sourcePhysicalPartial v j y)) (1 : ℍ))/2)=
      (fun y => sourceCurvature v y i j) := by
    funext y
    simp [sourceCurvature,sourcePhysicalPartial,spinCurvatureValue,Quaternion.inner_def]
  change HasFDerivAt (fun y => -(inner ℝ (spinOfVector (v y)*spinOfVector (sourcePhysicalPartial v i y)*
    spinOfVector (sourcePhysicalPartial v j y)) (1 : ℍ))/2) _ x at ht
  rw [hf] at ht
  rw [ht.fderiv]
  simp [spinCurvatureValue,Quaternion.inner_def,sourcePhysicalPartial,spinEmbedding,spinOfVector,add_mul,mul_add]
  ring

/-- The exact curvature derivative needs only a first times a second
derivative bound; no unproved deletion of a cubic term is used. -/
theorem sourceCurvature_partial_bound (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ y, ‖v y‖=1) (x : SpatialPoint) (i j k : Fin 3) (M1 M2 : ℝ)
    (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (h1 : ∀ l, ‖sourcePhysicalPartial v l x‖ ≤ M1)
    (h2 : ∀ l, ‖fderiv ℝ (sourcePhysicalPartial v l) x (EuclideanSpace.single k 1)‖ ≤ M2) :
    |fderiv ℝ (fun y => sourceCurvature v y i j) x (EuclideanSpace.single k 1)| ≤ M1*M2 := by
  have ht := spinCurvatureValue_three_tangents (v x) (sourcePhysicalPartial v k x)
    (sourcePhysicalPartial v i x) (sourcePhysicalPartial v j x) (hu x)
    (source_unit_tangent v hv hu x _) (source_unit_tangent v hv hu x _)
    (source_unit_tangent v hv hu x _)
  rw [sourceCurvature_partial v hv,ht,zero_add]
  have hb (a b : SpatialPoint) : |spinCurvatureValue (spinOfVector (v x))
      (spinOfVector a) (spinOfVector b)| ≤ ‖a‖*‖b‖/2 := by
    simpa only [spinOfVector_norm,hu,one_mul] using
      spinCurvatureValue_abs_le (spinOfVector (v x)) (spinOfVector a) (spinOfVector b)
  calc
    _ ≤ ‖fderiv ℝ (sourcePhysicalPartial v i) x (EuclideanSpace.single k 1)‖*
          ‖sourcePhysicalPartial v j x‖/2+
        ‖sourcePhysicalPartial v i x‖*
          ‖fderiv ℝ (sourcePhysicalPartial v j) x (EuclideanSpace.single k 1)‖/2 :=
      (abs_add_le _ _).trans (add_le_add (hb _ _) (hb _ _))
    _ ≤ M2*M1/2+M1*M2/2 := add_le_add
      (div_le_div_of_nonneg_right (mul_le_mul (h2 i) (h1 j) (norm_nonneg _) hM2) (by norm_num))
      (div_le_div_of_nonneg_right (mul_le_mul (h1 i) (h2 j) (norm_nonneg _) hM1) (by norm_num))
    _ = M1*M2 := by ring

/-- The coordinate moment integrated by the finite mean producer. -/
def sourceCurvatureMoment (v : SpatialPoint → SpatialPoint) (i j : Fin 3) (x : SpatialPoint) : ℝ :=
  x i*sourceCurvature v x i j

/-- Original `contDiff_sourceCurvatureMoment` guarantee for the `SourceMoment` construction; the complete source hypotheses are retained. -/
theorem contDiff_sourceCurvatureMoment (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (i j : Fin 3) : ContDiff ℝ ∞ (sourceCurvatureMoment v i j) :=
  (EuclideanSpace.proj i : SpatialPoint →L[ℝ] ℝ).contDiff.mul (contDiff_sourceCurvature v hv i j)

/-- Original `sourceCurvatureMoment_partial_bound` guarantee for the `SourceMoment` construction; the complete source hypotheses are retained. -/
theorem sourceCurvatureMoment_partial_bound (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ y, ‖v y‖=1) (x : SpatialPoint) (i j k : Fin 3) (hx : x i ∈ Set.Icc (0 : ℝ) 1)
    (M1 M2 : ℝ) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (h1 : ∀ l, ‖sourcePhysicalPartial v l x‖ ≤ M1)
    (h2 : ∀ l, ‖fderiv ℝ (sourcePhysicalPartial v l) x (EuclideanSpace.single k 1)‖ ≤ M2) :
    |fderiv ℝ (sourceCurvatureMoment v i j) x (EuclideanSpace.single k 1)| ≤ M1^2/2+M1*M2 := by
  have hd := (EuclideanSpace.proj i : SpatialPoint →L[ℝ] ℝ).hasFDerivAt.mul
    ((contDiff_sourceCurvature v hv i j).differentiable (by simp) x).hasFDerivAt
  change HasFDerivAt (sourceCurvatureMoment v i j) _ x at hd
  have hder : fderiv ℝ (sourceCurvatureMoment v i j) x (EuclideanSpace.single k 1)=
      x i*fderiv ℝ (fun y => sourceCurvature v y i j) x (EuclideanSpace.single k 1)+
        (if i=k then 1 else 0)*sourceCurvature v x i j := by
    rw [hd.fderiv]
    simp [add_comm]
  rw [hder]
  have hF : |sourceCurvature v x i j| ≤ M1^2/2 := by
    have h := spinCurvatureValue_abs_le (spinOfVector (v x))
      (spinOfVector (sourcePhysicalPartial v i x)) (spinOfVector (sourcePhysicalPartial v j x))
    simp only [spinOfVector_norm,hu,one_mul] at h
    exact h.trans (by simpa only [pow_two] using
      div_le_div_of_nonneg_right (mul_le_mul (h1 i) (h1 j) (norm_nonneg _) hM1) (by norm_num : (0 : ℝ) ≤ 2))
  have hdF := sourceCurvature_partial_bound v hv hu x i j k M1 M2 hM1 hM2 h1 h2
  have hcoord : |x i| ≤ 1 := by rw [abs_of_nonneg hx.1]; exact hx.2
  calc
    _ ≤ |x i| * |fderiv ℝ (fun y => sourceCurvature v y i j) x (EuclideanSpace.single k 1)|+
        |(if i=k then (1 : ℝ) else 0)| * |sourceCurvature v x i j| := by
      simpa only [abs_mul] using
        abs_add_le (x i*fderiv ℝ (fun y => sourceCurvature v y i j) x (EuclideanSpace.single k 1))
          ((if i=k then 1 else 0)*sourceCurvature v x i j)
    _ ≤ 1*(M1*M2)+1*(M1^2/2) := by
      have hproj : |(if i=k then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
      exact add_le_add (mul_le_mul hcoord hdF (abs_nonneg _) (by norm_num))
        (mul_le_mul hproj hF (abs_nonneg _) (by norm_num))
    _ = M1^2/2+M1*M2 := by ring

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
