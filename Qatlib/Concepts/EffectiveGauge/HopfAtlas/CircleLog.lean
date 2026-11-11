/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.TerminalPhase

/-!
# A real phase primitive from the actual angular derivative

This is an integral on the real covering line, not a principal argument.
The reconstruction formula retains a possibly nontrivial base value at y=0.
-/

set_option autoImplicit false
noncomputable section
open scoped Quaternion RealInnerProductSpace Topology ContDiff
open Set intervalIntegral
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Quaternion conjugation commutes with real scalar multiplication. -/
local instance : StarModule ℝ ℍ where
  star_smul r q := by ext <;> simp

/-- Definition of im ICoord in the Hopf Atlas construction. -/
private def imICoord : ℍ →L[ℝ] ℝ :=
  (EuclideanSpace.proj (1 : Fin 4)).comp Quaternion.linearIsometryEquivTuple.toContinuousLinearMap
/-- Definition of im JCoord in the Hopf Atlas construction. -/
private def imJCoord : ℍ →L[ℝ] ℝ :=
  (EuclideanSpace.proj (2 : Fin 4)).comp Quaternion.linearIsometryEquivTuple.toContinuousLinearMap
/-- Definition of im KCoord in the Hopf Atlas construction. -/
private def imKCoord : ℍ →L[ℝ] ℝ :=
  (EuclideanSpace.proj (3 : Fin 4)).comp Quaternion.linearIsometryEquivTuple.toContinuousLinearMap

/-- Definition of transverse Pair Linear in the Hopf Atlas construction. -/
private def transversePairLinear : ℝ × ℝ →ₗ[ℝ] TransversePoint where
  toFun z := WithLp.toLp 2 ![z.1,z.2]
  map_add' a b := by ext j; fin_cases j <;> rfl
  map_smul' c a := by ext j; fin_cases j <;> rfl

/-- Definition of transverse Pair in the Hopf Atlas construction. -/
def transversePair : ℝ × ℝ →L[ℝ] TransversePoint := transversePairLinear.toContinuousLinearMap

/-- Definition of circle Angular Rate in the Hopf Atlas construction. -/
def circleAngularRate (k : TransversePoint → ℍ) (p : TransversePoint) : ℝ :=
  (star (k p)*fderiv ℝ k p (EuclideanSpace.single 0 1)).imI

/-- Original `contDiff_circleAngularRate` guarantee for the `CircleLog` construction; the complete source hypotheses are retained. -/
theorem contDiff_circleAngularRate {k : TransversePoint → ℍ} (hk : ContDiff ℝ ∞ k) :
    ContDiff ℝ ∞ (circleAngularRate k) := by
  have hs : ContDiff ℝ ∞ (fun p => star (k p)) :=
    (starL' ℝ : ℍ ≃L[ℝ] ℍ).toContinuousLinearMap.contDiff.comp hk
  exact imICoord.contDiff.comp (hs.mul ((hk.fderiv_right (m := ∞) (by rfl)).clm_apply contDiff_const))

/-- Definition of circle Log Primitive in the Hopf Atlas construction. -/
def circleLogPrimitive (k : TransversePoint → ℍ) (p : TransversePoint) : ℝ :=
  ∫ y in (0 : ℝ)..p 0, circleAngularRate k (transversePair (y,p 1))

/-- Original `circle_curve_velocity` guarantee for the `CircleLog` construction; the complete source hypotheses are retained. -/
private theorem circle_curve_velocity {k : ℝ → ℍ} {d : ℍ} {t : ℝ}
    (hk : HasDerivAt k d t) (hc : ∀ u, IsCircleQuaternion (k u)) :
    d=k t*((star (k t)*d).imI • iAxis) := by
  have hjfun : (fun u => (k u).imJ)=fun _ => (0 : ℝ) := funext fun u => (hc u).2.1
  have hkfun : (fun u => (k u).imK)=fun _ => (0 : ℝ) := funext fun u => (hc u).2.2
  have hjd : HasDerivAt (fun u => (k u).imJ) d.imJ t := imJCoord.hasFDerivAt.comp_hasDerivAt t hk
  have hkd : HasDerivAt (fun u => (k u).imK) d.imK t := imKCoord.hasFDerivAt.comp_hasDerivAt t hk
  rw [hjfun] at hjd
  rw [hkfun] at hkd
  have hdj : d.imJ=0 := hjd.unique (hasDerivAt_const t (0 : ℝ))
  have hdk : d.imK=0 := hkd.unique (hasDerivAt_const t (0 : ℝ))
  have hnfun : (fun u => Quaternion.normSq (k u))=fun _ => (1 : ℝ) :=
    funext fun u => (normSq_eq_one_iff _).mpr (hc u).1
  have hnd := normSq_hasDerivAt hk
  rw [hnfun] at hnd
  have hin : inner ℝ (k t) d=0 := by
    have h := hnd.unique (hasDerivAt_const t (1 : ℝ))
    linarith
  have hred : (star (k t)*d).re=0 := by
    have h : (star (k t)*d).re=inner ℝ (k t) d := by
      simp [Quaternion.inner_def, Quaternion.re_mul]
    rw [h,hin]
  have hprod : star (k t)*d=(star (k t)*d).imI • iAxis := by
    simp [Quaternion.re_mul,(hc t).2.1,(hc t).2.2,hdj,hdk] at hred
    ext <;> simp [iAxis,(hc t).2.1,(hc t).2.2,hdj,hdk] <;> nlinarith [hred]
  have hunit : k t*star (k t)=1 := by
    rw [Quaternion.self_mul_star,(normSq_eq_one_iff _).mpr (hc t).1]; rfl
  calc
    d = (k t*star (k t))*d := by rw [hunit,one_mul]
    _ = k t*(star (k t)*d) := mul_assoc _ _ _
    _ = _ := congrArg (fun a : ℍ => k t*a) hprod

/-- Original `transversePair_hasDerivAt` guarantee for the `CircleLog` construction; the complete source hypotheses are retained. -/
theorem transversePair_hasDerivAt (z y : ℝ) :
    HasDerivAt (fun u : ℝ => transversePair (u,z)) (EuclideanSpace.single 0 1) y := by
  apply (transversePair.hasFDerivAt.comp_hasDerivAt y
    ((hasDerivAt_id y).prodMk (hasDerivAt_const y z))).congr_deriv
  ext j; fin_cases j <;> simp [transversePair,transversePairLinear]

/-- Original `circle_curve_hasDerivAt` guarantee for the `CircleLog` construction; the complete source hypotheses are retained. -/
theorem circle_curve_hasDerivAt {k : TransversePoint → ℍ} (hk : ContDiff ℝ ∞ k)
    (hc : ∀ p, IsCircleQuaternion (k p)) (z y : ℝ) :
    HasDerivAt (fun u : ℝ => k (transversePair (u,z)))
      (k (transversePair (y,z))*(circleAngularRate k (transversePair (y,z)) • iAxis)) y := by
  have hd := (hk.differentiable (by simp) (transversePair (y,z))).hasFDerivAt.comp_hasDerivAt y
    (transversePair_hasDerivAt z y)
  exact hd.congr_deriv (circle_curve_velocity hd (fun u => hc _))

/-- Original `circleLogPrimitive_hasDerivAt` guarantee for the `CircleLog` construction; the complete source hypotheses are retained. -/
theorem circleLogPrimitive_hasDerivAt {k : TransversePoint → ℍ} (hk : ContDiff ℝ ∞ k) (z y : ℝ) :
    HasDerivAt (fun u : ℝ => circleLogPrimitive k (transversePair (u,z)))
      (circleAngularRate k (transversePair (y,z))) y := by
  have hcont : Continuous (fun u : ℝ => circleAngularRate k (transversePair (u,z))) :=
    (contDiff_circleAngularRate hk).continuous.comp
      (transversePair.continuous.comp (continuous_id.prodMk continuous_const))
  exact (hcont.integral_hasStrictDerivAt 0 y).hasDerivAt

/-- Definition of integrate Real Path in the Hopf Atlas construction. -/
private def integrateRealPath : C(TransportTime, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ u in (0 : ℝ)..physicalPeriod, extendPath f u
      map_add' := by
        intro f g
        exact integral_add ((continuous_extendPath f).intervalIntegrable _ _)
          ((continuous_extendPath g).intervalIntegrable _ _)
      map_smul' := by intro c f; exact integral_smul c (extendPath f) }
    physicalPeriod (by
      intro f
      calc
        _ ≤ ‖f‖*|physicalPeriod-0| := norm_integral_le_of_norm_le_const
          (fun u _ => f.norm_coe_le_norm _)
        _ = physicalPeriod*‖f‖ := by rw [sub_zero,abs_of_pos physicalPeriod_pos]; ring)

/-- Definition of scaled Angular Source in the Hopf Atlas construction. -/
private def scaledAngularSource (k : TransversePoint → ℍ) (z : TransversePoint × ℝ) : ℝ :=
  (z.1 0/physicalPeriod)*circleAngularRate k (transversePair ((z.1 0/physicalPeriod)*z.2,z.1 1))

/-- Original `contDiff_scaledAngularSource` guarantee for the `CircleLog` construction; the complete source hypotheses are retained. -/
private theorem contDiff_scaledAngularSource {k : TransversePoint → ℍ} (hk : ContDiff ℝ ∞ k) :
    ContDiff ℝ ∞ (scaledAngularSource k) := by
  have hy : ContDiff ℝ ∞ (fun p : TransversePoint => p 0) := by
    change ContDiff ℝ ∞ (EuclideanSpace.proj (0 : Fin 2) : TransversePoint → ℝ)
    exact ContinuousLinearMap.contDiff _
  have hz' : ContDiff ℝ ∞ (fun p : TransversePoint => p 1) := by
    change ContDiff ℝ ∞ (EuclideanSpace.proj (1 : Fin 2) : TransversePoint → ℝ)
    exact ContinuousLinearMap.contDiff _
  have ha : ContDiff ℝ ∞ (fun z : TransversePoint × ℝ => z.1 0/physicalPeriod) :=
    (hy.comp contDiff_fst).div_const _
  have hz : ContDiff ℝ ∞ (fun z : TransversePoint × ℝ => z.1 1) :=
    hz'.comp contDiff_fst
  exact ha.mul ((contDiff_circleAngularRate hk).comp
    (transversePair.contDiff.comp ((ha.mul contDiff_snd).prodMk hz)))

/-- Original `contDiff_circleLogPrimitive` guarantee for the `CircleLog` construction; the complete source hypotheses are retained. -/
theorem contDiff_circleLogPrimitive {k : TransversePoint → ℍ} (hk : ContDiff ℝ ∞ k) :
    ContDiff ℝ ∞ (circleLogPrimitive k) := by
  let G := scaledAngularSource k
  have hg := contDiff_scaledAngularSource hk
  have hi : ContDiff ℝ ∞ (integrateRealPath : C(TransportTime, ℝ) → ℝ) := by
    exact ContinuousLinearMap.contDiff _
  have hc := hi.comp (contDiff_sourcePath hg)
  have heq : (fun p => integrateRealPath (sourcePath G hg.continuous p))=circleLogPrimitive k := by
    funext p
    change (∫ u in (0 : ℝ)..physicalPeriod, extendPath (sourcePath G hg.continuous p) u)=_
    have he : (∫ u in (0 : ℝ)..physicalPeriod, extendPath (sourcePath G hg.continuous p) u)=
        ∫ u in (0 : ℝ)..physicalPeriod, (p 0/physicalPeriod)*circleAngularRate k
          (transversePair ((p 0/physicalPeriod)*u,p 1)) := by
      apply integral_congr
      intro u hu
      rw [uIcc_of_le physicalPeriod_pos.le] at hu
      rw [extendPath_on _ u hu]
      rfl
    rw [he]
    change (∫ u in (0 : ℝ)..physicalPeriod, (p 0/physicalPeriod) •
      circleAngularRate k (transversePair ((p 0/physicalPeriod)*u,p 1)))=_
    rw [integral_smul]
    have hscale := smul_integral_comp_mul_left (a := (0 : ℝ)) (b := physicalPeriod)
      (fun y : ℝ => circleAngularRate k (transversePair (y,p 1))) (p 0/physicalPeriod)
    simpa only [mul_zero,div_mul_cancel₀ _ physicalPeriod_pos.ne',circleLogPrimitive] using hscale
  change ContDiff ℝ ∞ (fun p => integrateRealPath (sourcePath G hg.continuous p)) at hc
  rw [heq] at hc
  exact hc

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
