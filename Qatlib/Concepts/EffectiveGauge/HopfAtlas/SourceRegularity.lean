/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.CayleySource
import Mathlib.Analysis.Calculus.MeanValue

/-! # Source derivative bounds imply the actual normalized coefficient bounds -/

set_option autoImplicit false
noncomputable section
open scoped Quaternion RealInnerProductSpace ContDiff
open Set
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of source XXDerivative in the Hopf Atlas construction. -/
def sourceXXDerivative (v : SpatialPoint → SpatialPoint) (y : SpatialPoint) : ℍ :=
  fderiv ℝ (sourceXDerivative v) y (EuclideanSpace.single 0 1)

/-- Original `sourceXDerivative_eq_spin` guarantee for the `SourceRegularity` construction; the complete source hypotheses are retained. -/
theorem sourceXDerivative_eq_spin (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v) (y : SpatialPoint) :
    sourceXDerivative v y=spinOfVector (fderiv ℝ v y (EuclideanSpace.single 0 1)) := by
  have h : HasFDerivAt (sourceQuaternion v)
      (spinEmbedding.toContinuousLinearMap.comp (fderiv ℝ v y)) y :=
    spinEmbedding.toContinuousLinearMap.hasFDerivAt.comp y ((hv.differentiable (by simp) y).hasFDerivAt)
  change fderiv ℝ (sourceQuaternion v) y (EuclideanSpace.single 0 1)=_
  rw [h.fderiv]
  rfl

/-- Original `sourceXXDerivative_eq_spin` guarantee for the `SourceRegularity` construction; the complete source hypotheses are retained. -/
theorem sourceXXDerivative_eq_spin (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v) (y : SpatialPoint) :
    sourceXXDerivative v y=spinOfVector
      (fderiv ℝ (fun w => fderiv ℝ v w (EuclideanSpace.single 0 1)) y (EuclideanSpace.single 0 1)) := by
  let dv := fun w => fderiv ℝ v w (EuclideanSpace.single 0 1)
  have hdv : ContDiff ℝ ∞ dv := (hv.fderiv_right (m := ∞) (by rfl)).clm_apply contDiff_const
  have he : sourceXDerivative v=sourceQuaternion dv := funext (sourceXDerivative_eq_spin v hv)
  change fderiv ℝ (sourceXDerivative v) y (EuclideanSpace.single 0 1)=_
  rw [he]
  exact sourceXDerivative_eq_spin dv hdv y

/-- Original `sourceXDerivativeCurve_hasDerivAt` guarantee for the `SourceRegularity` construction; the complete source hypotheses are retained. -/
theorem sourceXDerivativeCurve_hasDerivAt (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (z : TransversePoint) (t : ℝ) :
    HasDerivAt (fun u => sourceXDerivative v (sourcePosition (z,u)))
      (sourceXXDerivative v (sourcePosition (z,t))) t :=
  ((contDiff_sourceXDerivative hv).differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
    (sourcePosition_hasDerivAt z t)

/-- Original `normalizedSourceGenerator_hasDerivAt` guarantee for the `SourceRegularity` construction; the complete source hypotheses are retained. -/
theorem normalizedSourceGenerator_hasDerivAt (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (z : TransversePoint) (x t : ℝ) :
    HasDerivAt (normalizedSourceGenerator v z x)
      (x^2 • ((-1/2 : ℝ) •
        (sourceXDerivative v (sourcePosition (z,x*t))*sourceXDerivative v (sourcePosition (z,x*t))+
          sourceQuaternion v (sourcePosition (z,x*t))*sourceXXDerivative v (sourcePosition (z,x*t))))) t := by
  have hx : HasDerivAt (fun u : ℝ => x*u) x t := by simpa using (hasDerivAt_id t).const_mul x
  have hq := (sourceCurve_hasDerivAt hv z (x*t)).scomp t hx
  have hd := (sourceXDerivativeCurve_hasDerivAt v hv z (x*t)).scomp t hx
  have h := (((hq.mul hd).const_smul (-1/2 : ℝ)).const_smul x)
  apply h.congr_deriv
  simp only [Function.comp_apply,smul_mul_assoc,mul_smul_comm,← smul_add,smul_smul]
  congr 1
  ring

/-- Original `horizontalDerivative_norm_le` guarantee for the `SourceRegularity` construction; the complete source hypotheses are retained. -/
private theorem horizontalDerivative_norm_le (q d dd : ℍ) (hq : ‖q‖=1)
    (m1 m2 : ℝ) (hm1 : 0 ≤ m1) (hd : ‖d‖ ≤ m1) (hdd : ‖dd‖ ≤ m2) :
    ‖(-1/2 : ℝ) • (d*d+q*dd)‖ ≤ (m1^2+m2)/2 := by
  rw [norm_smul]
  norm_num only [Real.norm_eq_abs,abs_of_nonpos (by norm_num : (-1/2 : ℝ) ≤ 0),neg_div,neg_neg]
  have h : ‖d*d+q*dd‖ ≤ m1^2+m2 := by
    calc
      _ ≤ ‖d*d‖+‖q*dd‖ := norm_add_le _ _
      _ = ‖d‖^2+‖dd‖ := by rw [norm_mul,norm_mul,hq,one_mul,pow_two]
      _ ≤ _ := add_le_add (by simpa only [pow_two] using mul_le_mul hd hd (norm_nonneg _) hm1) hdd
  linarith

/-- Bounds are on actual source derivatives, not the unknown lift or its
coefficient oracle. Both physical endpoints are included. -/
theorem normalizedSourceGenerator_bounds (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ y, ‖v y‖=1) (z : TransversePoint) (x : ℝ) (hx : 0 ≤ x)
    (m1 m2 : ℝ) (hm1 : 0 ≤ m1)
    (h1 : ∀ u ∈ Icc 0 x, ‖sourceXDerivative v (sourcePosition (z,u))‖ ≤ m1)
    (h2 : ∀ u ∈ Icc 0 x, ‖sourceXXDerivative v (sourcePosition (z,u))‖ ≤ m2) :
    (∀ t ∈ Icc 0 1, ‖normalizedSourceGenerator v z x t‖ ≤ x*m1/2) ∧
    (∀ s ∈ Icc 0 1, ∀ t ∈ Icc 0 1,
      ‖normalizedSourceGenerator v z x t-normalizedSourceGenerator v z x s‖ ≤ (x^2*(m1^2+m2)/2)*|t-s|) := by
  have hmap : MapsTo (fun t : ℝ => x*t) (Icc 0 1) (Icc 0 x) := by
    intro t ht
    constructor
    · exact mul_nonneg hx ht.1
    · simpa only [mul_one] using mul_le_mul_of_nonneg_left ht.2 hx
  have hq (t : ℝ) : ‖sourceQuaternion v (sourcePosition (z,x*t))‖=1 :=
    (spinOfVector_norm _).trans (hu _)
  constructor
  · intro t ht
    change ‖x • horizontalCoefficient _ _‖ ≤ _
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hx,horizontal_norm _ _ (hq t)]
    have h := mul_le_mul_of_nonneg_left (h1 (x*t) (hmap ht)) hx
    linarith
  · have hb : ∀ t ∈ Icc 0 1,
        ‖x^2 • ((-1/2 : ℝ) •
          (sourceXDerivative v (sourcePosition (z,x*t))*sourceXDerivative v (sourcePosition (z,x*t))+
            sourceQuaternion v (sourcePosition (z,x*t))*sourceXXDerivative v (sourcePosition (z,x*t))))‖ ≤
          x^2*(m1^2+m2)/2 := by
      intro t ht
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg x)]
      have h := mul_le_mul_of_nonneg_left
        (horizontalDerivative_norm_le _ _ _ (hq t) m1 m2 hm1 (h1 _ (hmap ht)) (h2 _ (hmap ht))) (sq_nonneg x)
      linarith
    intro s hs t ht
    simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u _ => (normalizedSourceGenerator_hasDerivAt v hv z x u).hasDerivWithinAt) hb (convex_Icc 0 1) hs ht

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
