/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.HopfFibre
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.Gauge
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Fibre Differential

Hopf Atlas constructions for Effective Gauge.
Proves `connectionValue_iPlane_mul`, `unit_iPlane_tangent`, `unitField_inner_fderiv`.
-/


set_option autoImplicit false
noncomputable section
open scoped Quaternion RealInnerProductSpace ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Product connection law without assuming a chosen real logarithm. -/
theorem connectionValue_iPlane_mul (z dz q dq : ℍ) (hj : z.imJ=0) (hk : z.imK=0) :
    connectionValue (z*q) (dz*q+z*dq)=
      Quaternion.normSq z*connectionValue q dq+Quaternion.normSq q*connectionValue z dz := by
  simp [connectionValue_eq,Quaternion.normSq_def',hj,hk]
  ring

/-- A tangent to the actual unit circle is its connection times i*z. -/
theorem unit_iPlane_tangent (z dz : ℍ) (hz : ‖z‖=1)
    (hj : z.imJ=0) (hk : z.imK=0) (hdj : dz.imJ=0) (hdk : dz.imK=0)
    (ht : inner ℝ z dz=0) : dz=connectionValue z dz • (iAxis*z) := by
  have hn := (normSq_eq_one_iff z).mpr hz
  simp [Quaternion.normSq_def',hj,hk] at hn
  simp [Quaternion.inner_def,hj,hk] at ht
  have ha := congrArg (fun t : ℝ => t*dz.re) hn
  have hb := congrArg (fun t : ℝ => t*dz.imI) hn
  have hc := congrArg (fun t : ℝ => t*z.re) ht
  have hd := congrArg (fun t : ℝ => t*z.imI) ht
  ext <;> simp [connectionValue_eq,iAxis,hj,hk,hdj,hdk] <;> nlinarith

/-- Original `unitField_inner_fderiv` guarantee for the `FibreDifferential` construction; the complete source hypotheses are retained. -/
theorem unitField_inner_fderiv (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hu : ∀ y, ‖q y‖=1) (x h : SpatialPoint) : inner ℝ (q x) (fderiv ℝ q x h)=0 := by
  have hd := (hq.differentiable (by simp) x).hasFDerivAt
  have hi := hd.inner ℝ hd
  have heq : (fun y => inner ℝ (q y) (q y))=(fun _ : SpatialPoint => (1 : ℝ)) := by
    funext y
    rw [real_inner_self_eq_norm_sq,hu y]
    norm_num
  rw [heq] at hi
  have he := congrArg (fun f : SpatialPoint →L[ℝ] ℝ => f h)
    (hi.unique (hasFDerivAt_const (1 : ℝ) x))
  have hs : inner ℝ (q x) (fderiv ℝ q x h)+inner ℝ (fderiv ℝ q x h) (q x)=0 := by
    simpa using he
  have hcomm := real_inner_comm (q x) (fderiv ℝ q x h)
  linarith

/-- Original `iPlaneField_fderiv` guarantee for the `FibreDifferential` construction; the complete source hypotheses are retained. -/
theorem iPlaneField_fderiv (q : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hc : ∀ y, (q y).imJ=0 ∧ (q y).imK=0) (x h : SpatialPoint) :
    (fderiv ℝ q x h).imJ=0 ∧ (fderiv ℝ q x h).imK=0 := by
  let pJ : ℍ →L[ℝ] ℝ := ⟨QuaternionAlgebra.imJₗ (-1 : ℝ) 0 (-1 : ℝ),Quaternion.continuous_imJ⟩
  let pK : ℍ →L[ℝ] ℝ := ⟨QuaternionAlgebra.imKₗ (-1 : ℝ) 0 (-1 : ℝ),Quaternion.continuous_imK⟩
  have heJ : (fun y => pJ (q y))=(fun _ : SpatialPoint => (0 : ℝ)) := funext (fun y => (hc y).1)
  have heK : (fun y => pK (q y))=(fun _ : SpatialPoint => (0 : ℝ)) := funext (fun y => (hc y).2)
  have hd := (hq.differentiable (by simp) x).hasFDerivAt
  have hJ := pJ.hasFDerivAt.comp x hd
  have hK := pK.hasFDerivAt.comp x hd
  change HasFDerivAt (fun y => pJ (q y)) _ x at hJ
  change HasFDerivAt (fun y => pK (q y)) _ x at hK
  rw [heJ] at hJ
  rw [heK] at hK
  exact ⟨congrArg (fun f : SpatialPoint →L[ℝ] ℝ => f h) (hJ.unique (hasFDerivAt_const 0 x)),
    congrArg (fun f : SpatialPoint →L[ℝ] ℝ => f h) (hK.unique (hasFDerivAt_const 0 x))⟩

/-- Quaternion conjugation commutes with real scalar multiplication. -/
local instance : StarModule ℝ ℍ where
  star_smul r q := by ext <;> simp

/-- The actual fibre ratio differentiates by the difference of the true
connections; no real logarithm or winding classification is an input. -/
theorem sameHopf_ratio_partial (q r : QuaternionField) (hq : ContDiff ℝ ∞ q)
    (hr : ContDiff ℝ ∞ r) (huq : ∀ y, ‖q y‖=1) (hur : ∀ y, ‖r y‖=1)
    (hh : ∀ y, hopf (r y)=hopf (q y)) (x : SpatialPoint) (j : Fin 3) :
    spatialPartial (fun y => r y*star (q y)) x j=
      (connection r x j-connection q x j) • (iAxis*(r x*star (q x))) := by
  let z : QuaternionField := fun y => r y*star (q y)
  have hz : ContDiff ℝ ∞ z := hr.mul ((starL' ℝ : ℍ ≃L[ℝ] ℍ).contDiff.comp hq)
  have hzu : ∀ y, ‖z y‖=1 := fun y => sameHopf_ratio_norm _ _ (huq y) (hur y)
  have hzc : ∀ y, (z y).imJ=0 ∧ (z y).imK=0 :=
    fun y => sameHopf_ratio_components _ _ (huq y) (hur y) (hh y)
  have hd := iPlaneField_fderiv z hz hzc x (EuclideanSpace.single j 1)
  have ht := unitField_inner_fderiv z hz hzu x (EuclideanSpace.single j 1)
  have htan := unit_iPlane_tangent (z x) (spatialPartial z x j) (hzu x)
    (hzc x).1 (hzc x).2 hd.1 hd.2 ht
  have heq : (fun y => z y*q y)=r := funext (fun y => sameHopf_ratio_action _ _ (huq y))
  have hprod := ((hz.differentiable (by simp) x).hasFDerivAt).mul'
    ((hq.differentiable (by simp) x).hasFDerivAt)
  change HasFDerivAt (fun y => z y*q y) _ x at hprod
  rw [heq] at hprod
  have hp : spatialPartial r x j=spatialPartial z x j*q x+z x*spatialPartial q x j := by
    rw [spatialPartial,hprod.fderiv]
    simp [spatialPartial,add_comm]
  have hconn : connection r x j=connection q x j+connection z x j := by
    change connectionValue (r x) (spatialPartial r x j)=_
    rw [← congrFun heq x,hp,connectionValue_iPlane_mul _ _ _ _ (hzc x).1 (hzc x).2,
      (normSq_eq_one_iff _).mpr (hzu x),(normSq_eq_one_iff _).mpr (huq x)]
    simp only [one_mul]
    rfl
  have hdiff : connection z x j=connection r x j-connection q x j := by linarith
  change spatialPartial z x j=_
  rw [htan]
  change connection z x j • (iAxis*z x)=_
  rw [hdiff]

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
