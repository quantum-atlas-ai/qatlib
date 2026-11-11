/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.HorizontalFamily

/-!
# Smooth time rescaling of the original horizontal family

Variable physical time is transferred to a coefficient path on the fixed
interval [0,2 pi]. Its endpoint is jointly smooth in transverse parameters
and physical time. Identification with the original path is only claimed
on the original physical interval, including both endpoints.
-/

set_option autoImplicit false
noncomputable section
open scoped Quaternion RealInnerProductSpace Topology ContDiff
open Set intervalIntegral
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Definition of transport Finish in the Hopf Atlas construction. -/
def transportFinish : TransportTime := ⟨physicalPeriod, physicalPeriod_pos.le, le_rfl⟩

/-- Definition of scaled Coefficient Source in the Hopf Atlas construction. -/
def scaledCoefficientSource (v : SpatialPoint → SpatialPoint)
    (z : (TransversePoint × ℝ) × ℝ) : SpatialPoint :=
  (z.1.2/physicalPeriod) • horizontalCoefficientSource v (z.1.1, (z.1.2/physicalPeriod)*z.2)

/-- Original `contDiff_scaledCoefficientSource` guarantee for the `MixedTime` construction; the complete source hypotheses are retained. -/
theorem contDiff_scaledCoefficientSource {v : SpatialPoint → SpatialPoint} (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (scaledCoefficientSource v) := by
  have ha : ContDiff ℝ ∞ (fun z : (TransversePoint × ℝ) × ℝ => z.1.2/physicalPeriod) :=
    (contDiff_snd.comp contDiff_fst).div_const _
  exact ha.smul ((contDiff_horizontalCoefficientSource hv).comp
    ((contDiff_fst.comp contDiff_fst).prodMk (ha.mul contDiff_snd)))

/-- Definition of scaled Coefficient Paths in the Hopf Atlas construction. -/
def scaledCoefficientPaths (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v) :
    TransversePoint × ℝ → CoefficientPath :=
  sourcePathOver (scaledCoefficientSource v) (contDiff_scaledCoefficientSource hv).continuous

/-- Original `contDiff_scaledCoefficientPaths` guarantee for the `MixedTime` construction; the complete source hypotheses are retained. -/
theorem contDiff_scaledCoefficientPaths (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (scaledCoefficientPaths v hv) :=
  contDiff_sourcePathOver (contDiff_scaledCoefficientSource hv)

/-- Definition of source Lift Extension in the Hopf Atlas construction. -/
def sourceLiftExtension (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (q₀ : ℍ) (h₀ : ‖q₀‖=1) (z : TransversePoint × ℝ) : ℍ :=
  pathTransport q₀ h₀ (scaledCoefficientPaths v hv z) transportFinish

/-- Original `contDiff_sourceLiftExtension` guarantee for the `MixedTime` construction; the complete source hypotheses are retained. -/
theorem contDiff_sourceLiftExtension (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (q₀ : ℍ) (h₀ : ‖q₀‖=1) : ContDiff ℝ ∞ (sourceLiftExtension v hv q₀ h₀) := by
  have he : ContDiff ℝ ∞ (fun Q : QuaternionPath => Q transportFinish) := by
    change ContDiff ℝ ∞ (ContinuousMap.evalCLM ℝ transportFinish : QuaternionPath → ℍ)
    exact ContinuousLinearMap.contDiff _
  exact he.comp ((contDiff_pathTransport q₀ h₀).comp (contDiff_scaledCoefficientPaths v hv))

/-- Original `scaledCoefficientPaths_embed` guarantee for the `MixedTime` construction; the complete source hypotheses are retained. -/
theorem scaledCoefficientPaths_embed (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (p : TransversePoint) (t : ℝ) (u : TransportTime) :
    spinOfVector (scaledCoefficientPaths v hv (p,t) u) =
      (t/physicalPeriod) • sourceHorizontalQuaternion v (sourcePosition (p,(t/physicalPeriod)*u)) := by
  change spinEmbedding ((t/physicalPeriod) •
    imaginaryVector (sourceHorizontalQuaternion v (sourcePosition (p,(t/physicalPeriod)*u)))) = _
  rw [map_smul]
  congr 1
  apply spinOfVector_imaginaryVector
  apply horizontal_re
  exact source_tangent (sourceCurve_hasDerivAt hv p) (fun _ => rfl)
    (fun r => (spinOfVector_norm (v (sourcePosition (p,r)))).trans (hu _)) _

/-- Original `timeScale_maps` guarantee for the `MixedTime` construction; the complete source hypotheses are retained. -/
private theorem timeScale_maps (t : ℝ) (ht : t ∈ Icc 0 physicalPeriod) :
    MapsTo (fun u : ℝ => (t/physicalPeriod)*u) (Icc 0 physicalPeriod) (Icc 0 physicalPeriod) := by
  have ha : 0 ≤ t/physicalPeriod := div_nonneg ht.1 physicalPeriod_pos.le
  have hb : t/physicalPeriod ≤ 1 := (div_le_one physicalPeriod_pos).mpr ht.2
  intro u hu
  exact ⟨mul_nonneg ha hu.1,
    (mul_le_mul_of_nonneg_right hb hu.1).trans (by simpa using hu.2)⟩

/-- The genuinely jointly smooth endpoint construction equals the original
horizontal path on the entire closed physical interval, including time zero. -/
theorem sourceLiftExtension_eq (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1) (p : TransversePoint) (t : TransportTime) :
    sourceLiftExtension v hv q₀ h₀ (p,t)=sourceLiftPaths v hv q₀ h₀ p t := by
  let a : ℝ := (t : ℝ)/physicalPeriod
  let K := scaledCoefficientPaths v hv (p,(t : ℝ))
  let Q := extendPath (sourceLiftPaths v hv q₀ h₀ p)
  let S := extendPath (pathTransport q₀ h₀ K)
  let r := fun u : ℝ => Q (a*u)
  let k := fun u : ℝ => spinOfVector (extendPath K u)
  have hm : MapsTo (fun u : ℝ => a*u) (Icc 0 physicalPeriod) (Icc 0 physicalPeriod) :=
    timeScale_maps t t.2
  have hk : ContinuousOn k (Icc 0 physicalPeriod) :=
    (spinEmbedding.continuous.comp (continuous_extendPath K)).continuousOn
  have hS : ∀ u ∈ Icc 0 physicalPeriod, HasDerivWithinAt S (S u*k u) (Icc 0 physicalPeriod) u :=
    fun u hu' => pathTransport_hasDerivWithinAt q₀ h₀ K u hu'
  have hr : ∀ u ∈ Icc 0 physicalPeriod, HasDerivWithinAt r (r u*k u) (Icc 0 physicalPeriod) u := by
    intro u hu'
    have hscale : HasDerivWithinAt (fun z : ℝ => a*z) a (Icc 0 physicalPeriod) u := by
      simpa using ((hasDerivAt_id u).const_mul a).hasDerivWithinAt
    have hd := (sourceLiftPaths_hasDerivWithinAt v hv hu q₀ h₀ p (a*u) (hm hu')).scomp u hscale hm
    have he : k u=a • sourceHorizontalQuaternion v (sourcePosition (p,a*u)) := by
      rw [show k u=spinOfVector (extendPath K u) from rfl, extendPath_on K u hu']
      exact scaledCoefficientPaths_embed v hv hu p t ⟨u,hu'⟩
    simpa only [he, mul_smul_comm, r, Q, Function.comp_def] using hd
  have hSn : ∀ u ∈ Icc 0 physicalPeriod, ‖S u‖=1 := by
    intro u hu'
    simpa only [S, extendPath_on _ u hu'] using pathTransport_unit q₀ h₀ K ⟨u,hu'⟩
  have hrn : ∀ u ∈ Icc 0 physicalPeriod, ‖r u‖=1 := by
    intro u hu'
    simpa only [r, Q, sourceLiftPaths, extendPath_on _ (a*u) (hm hu')] using
      pathTransport_unit q₀ h₀ (horizontalCoefficientPaths v hv p) ⟨a*u,hm hu'⟩
  have hi : r 0=S 0 := by
    simp only [r, Q, S, mul_zero, extendPath_on _ 0 ⟨le_rfl,physicalPeriod_pos.le⟩]
    change sourceLiftPaths v hv q₀ h₀ p transportStart=pathTransport q₀ h₀ K transportStart
    exact (pathTransport_start q₀ h₀ _).trans (pathTransport_start q₀ h₀ K).symm
  have hb := unit_transport_stability physicalPeriod_pos.le hk hk hS hr
    (fun _ _ => rfl) hSn hrn hi (E := 0) (by intro u _; simp)
  have heq : r physicalPeriod=S physicalPeriod :=
    sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (by simpa using hb) (norm_nonneg _)))
  have ha : a*physicalPeriod=(t : ℝ) := by
    dsimp [a]
    exact div_mul_cancel₀ _ physicalPeriod_pos.ne'
  have hend : r physicalPeriod=pathTransport q₀ h₀ K transportFinish := by
    rw [heq, show S physicalPeriod=extendPath (pathTransport q₀ h₀ K) physicalPeriod from rfl,
      extendPath_on _ physicalPeriod ⟨physicalPeriod_pos.le,le_rfl⟩]
    rfl
  have hold : r physicalPeriod=sourceLiftPaths v hv q₀ h₀ p t := by
    simp only [r, ha, Q, extendPath_coe]
  exact hend.symm.trans hold

/-- Original `contDiffOn_sourceLiftSpacetime` guarantee for the `MixedTime` construction; the complete source hypotheses are retained. -/
theorem contDiffOn_sourceLiftSpacetime (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1) :
    ContDiffOn ℝ ∞ (fun z : TransversePoint × ℝ => extendPath (sourceLiftPaths v hv q₀ h₀ z.1) z.2)
      (univ ×ˢ Icc 0 physicalPeriod) := by
  apply (contDiff_sourceLiftExtension v hv q₀ h₀).contDiffOn.congr
  intro z hz
  rw [extendPath_on _ z.2 hz.2]
  exact (sourceLiftExtension_eq v hv hu q₀ h₀ z.1 ⟨z.2,hz.2⟩).symm

/-- The usual derivative of the smooth extension agrees with the physical
ODE even at the two endpoints, by unique differentiation within the interval. -/
theorem sourceLiftExtension_timeDerivative (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1) (p : TransversePoint)
    (t : ℝ) (ht : t ∈ Icc 0 physicalPeriod) :
    fderiv ℝ (sourceLiftExtension v hv q₀ h₀) (p,t) (0,1) =
      sourceLiftExtension v hv q₀ h₀ (p,t)*sourceHorizontalQuaternion v (sourcePosition (p,t)) := by
  have hd : HasDerivAt (fun u : ℝ => sourceLiftExtension v hv q₀ h₀ (p,u))
      (fderiv ℝ (sourceLiftExtension v hv q₀ h₀) (p,t) (0,1)) t :=
    ((contDiff_sourceLiftExtension v hv q₀ h₀).differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t p).prodMk (hasDerivAt_id t))
  have he : ∀ u ∈ Icc 0 physicalPeriod,
      sourceLiftExtension v hv q₀ h₀ (p,u)=extendPath (sourceLiftPaths v hv q₀ h₀ p) u := by
    intro u hu'
    rw [extendPath_on _ u hu']
    exact sourceLiftExtension_eq v hv hu q₀ h₀ p ⟨u,hu'⟩
  have hraw := (sourceLiftPaths_hasDerivWithinAt v hv hu q₀ h₀ p t ht).congr_of_mem he ht
  rw [← he t ht] at hraw
  exact UniqueDiffWithinAt.eq_deriv (Icc 0 physicalPeriod)
    (uniqueDiffOn_Icc physicalPeriod_pos t ht) hd.hasDerivWithinAt hraw

/-- Definition of position Inverse Linear in the Hopf Atlas construction. -/
private def positionInverseLinear : SpatialPoint →ₗ[ℝ] TransversePoint × ℝ where
  toFun x := (WithLp.toLp 2 ![x 1,x 2], x 0)
  map_add' a b := by
    apply Prod.ext
    · ext j; fin_cases j <;> rfl
    · rfl
  map_smul' c a := by
    apply Prod.ext
    · ext j; fin_cases j <;> rfl
    · rfl

/-- Definition of source Position Inverse in the Hopf Atlas construction. -/
def sourcePositionInverse : SpatialPoint →L[ℝ] TransversePoint × ℝ :=
  positionInverseLinear.toContinuousLinearMap

/-- Original `sourcePosition_inverse` guarantee for the `MixedTime` construction; the complete source hypotheses are retained. -/
@[simp] theorem sourcePosition_inverse (x : SpatialPoint) :
    sourcePosition (sourcePositionInverse x)=x := by ext j; fin_cases j <;> rfl

/-- Definition of source Lift Spatial Extension in the Hopf Atlas construction. -/
def sourceLiftSpatialExtension (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (q₀ : ℍ) (h₀ : ‖q₀‖=1) (x : SpatialPoint) : ℍ :=
  sourceLiftExtension v hv q₀ h₀ (sourcePositionInverse x)

/-- Original `contDiff_sourceLiftSpatialExtension` guarantee for the `MixedTime` construction; the complete source hypotheses are retained. -/
theorem contDiff_sourceLiftSpatialExtension (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (q₀ : ℍ) (h₀ : ‖q₀‖=1) : ContDiff ℝ ∞ (sourceLiftSpatialExtension v hv q₀ h₀) :=
  (contDiff_sourceLiftExtension v hv q₀ h₀).comp sourcePositionInverse.contDiff

/-- Original `sourceLiftSpatialExtension_unit` guarantee for the `MixedTime` construction; the complete source hypotheses are retained. -/
theorem sourceLiftSpatialExtension_unit (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (q₀ : ℍ) (h₀ : ‖q₀‖=1) (x : SpatialPoint) : ‖sourceLiftSpatialExtension v hv q₀ h₀ x‖=1 :=
  pathTransport_unit q₀ h₀ _ transportFinish

/-- Initial compatibility gives the Hopf image on the physical slab using
the original path. A separate scaled-source argument below proves the global identity. -/
theorem sourceLiftSpatialExtension_hopf (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1)
    (hp : IsPeriodicField (sourceQuaternion v)) (eta : ℝ) (he : 0<eta) (sc : ℍ)
    (hc : HasConstantCollar (sourceQuaternion v) eta sc) (hi : hopf q₀=sc)
    (x : SpatialPoint) (hx : 0 ≤ x 0 ∧ x 0 ≤ physicalPeriod) :
    hopf (sourceLiftSpatialExtension v hv q₀ h₀ x)=sourceQuaternion v x := by
  change hopf (sourceLiftExtension v hv q₀ h₀ ((sourcePositionInverse x).1, x 0))=_
  rw [sourceLiftExtension_eq v hv hu q₀ h₀ (sourcePositionInverse x).1 ⟨x 0,hx⟩]
  have hinit := hi.trans (collar_initial_face _ hp eta he sc hc (sourcePositionInverse x).1).symm
  rw [sourceLiftPaths_hopf v hv hu q₀ h₀ (sourcePositionInverse x).1 hinit]
  exact congrArg (sourceQuaternion v) (sourcePosition_inverse x)

/-- Original `sourceLiftSpatialExtension_timePartial` guarantee for the `MixedTime` construction; the complete source hypotheses are retained. -/
theorem sourceLiftSpatialExtension_timePartial (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1)
    (x : SpatialPoint) (hx : 0 ≤ x 0 ∧ x 0 ≤ physicalPeriod) :
    fderiv ℝ (sourceLiftSpatialExtension v hv q₀ h₀) x (EuclideanSpace.single 0 1) =
      sourceLiftSpatialExtension v hv q₀ h₀ x*sourceHorizontalQuaternion v x := by
  have hd := ((contDiff_sourceLiftExtension v hv q₀ h₀).differentiable (by simp)
    (sourcePositionInverse x)).hasFDerivAt.comp x sourcePositionInverse.hasFDerivAt
  change fderiv ℝ (sourceLiftExtension v hv q₀ h₀ ∘ sourcePositionInverse) x
    (EuclideanSpace.single 0 1)=_
  rw [hd.fderiv]
  have haxis : sourcePositionInverse (EuclideanSpace.single 0 1)=(0,1) := by
    apply Prod.ext
    · ext j; fin_cases j <;> simp [sourcePositionInverse, positionInverseLinear]
    · simp [sourcePositionInverse, positionInverseLinear]
  simp only [ContinuousLinearMap.comp_apply, haxis]
  change fderiv ℝ (sourceLiftExtension v hv q₀ h₀) ((sourcePositionInverse x).1,x 0) (0,1)=_
  rw [sourceLiftExtension_timeDerivative v hv hu q₀ h₀ (sourcePositionInverse x).1 (x 0) hx]
  exact congrArg (fun y => sourceLiftExtension v hv q₀ h₀ (sourcePositionInverse x)*
    sourceHorizontalQuaternion v y) (sourcePosition_inverse x)

/-- Original `horizontal_scaled_derivative` guarantee for the `MixedTime` construction; the complete source hypotheses are retained. -/
private theorem horizontal_scaled_derivative (s d : ℍ) (a : ℝ) :
    horizontalCoefficient s (a • d)=a • horizontalCoefficient s d := by
  simp only [horizontalCoefficient, mul_smul_comm, smul_smul]
  rw [mul_comm]

/-- Global Hopf compatibility follows separately from horizontal transport
along the scaled source curve; it does not rely on extrapolating slab equality. -/
theorem sourceLiftExtension_hopf_global (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1) (p : TransversePoint)
    (hi : hopf q₀=sourceQuaternion v (sourcePosition (p,0))) (t : ℝ) :
    hopf (sourceLiftExtension v hv q₀ h₀ (p,t))=sourceQuaternion v (sourcePosition (p,t)) := by
  let a : ℝ := t/physicalPeriod
  let K := scaledCoefficientPaths v hv (p,t)
  let q := extendPath (pathTransport q₀ h₀ K)
  let s := fun u : ℝ => sourceQuaternion v (sourcePosition (p,a*u))
  let ds := fun u : ℝ => a • sourceXDerivative v (sourcePosition (p,a*u))
  have hs : ∀ u, HasDerivAt s (ds u) u := by
    intro u
    have ha : HasDerivAt (fun r : ℝ => a*r) a u := by
      simpa using (hasDerivAt_id u).const_mul a
    exact (sourceCurve_hasDerivAt hv p (a*u)).scomp u ha
  have hdsc : ContinuousOn ds (Icc 0 physicalPeriod) := by
    have hp : Continuous (fun u : ℝ => sourcePosition (p,a*u)) :=
      sourcePosition.continuous.comp (continuous_const.prodMk (continuous_const.mul continuous_id))
    exact (((contDiff_sourceXDerivative hv).continuous.comp hp).const_smul a).continuousOn
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hdsc
  have hq : ∀ u ∈ Ico 0 physicalPeriod,
      HasDerivWithinAt q (q u*horizontalCoefficient (s u) (ds u)) (Ici u) u := by
    intro u hu'
    have he : spinOfVector (extendPath K u)=horizontalCoefficient (s u) (ds u) := by
      rw [extendPath_on K u ⟨hu'.1,hu'.2.le⟩]
      rw [scaledCoefficientPaths_embed v hv hu p t ⟨u,⟨hu'.1,hu'.2.le⟩⟩]
      exact (horizontal_scaled_derivative _ _ a).symm
    have h := pathTransport_hasDerivWithinAt q₀ h₀ K u ⟨hu'.1,hu'.2.le⟩
    rw [he] at h
    apply h.mono_of_mem_nhdsWithin
    exact Filter.mem_of_superset
      (Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hu'.2)) self_mem_nhdsWithin)
      (by intro y hy; exact ⟨hu'.1.trans hy.2,hy.1.le⟩)
  have hstart : q 0=q₀ := by
    change extendPath (pathTransport q₀ h₀ K) 0=q₀
    rw [extendPath_on _ 0 ⟨le_rfl,physicalPeriod_pos.le⟩]
    exact pathTransport_start q₀ h₀ K
  have hn0 : ‖q 0‖=1 := by rw [hstart]; exact h₀
  have hi0 : hopf (q 0)=s 0 := by rw [hstart]; simpa only [s,mul_zero] using hi
  have h := horizontal_transport (q := q) hs (fun _ => rfl)
    (fun u => (spinOfVector_norm (v (sourcePosition (p,a*u)))).trans (hu _))
    (fun u hu' => hM u ⟨hu'.1,hu'.2.le⟩) (continuous_extendPath _).continuousOn hq hn0 hi0
    physicalPeriod ⟨physicalPeriod_pos.le,le_rfl⟩
  have hEndQ : q physicalPeriod=sourceLiftExtension v hv q₀ h₀ (p,t) := by
    rw [show q physicalPeriod=extendPath (pathTransport q₀ h₀ K) physicalPeriod from rfl,
      extendPath_on _ physicalPeriod ⟨physicalPeriod_pos.le,le_rfl⟩]
    rfl
  have hEndS : s physicalPeriod=sourceQuaternion v (sourcePosition (p,t)) := by
    dsimp [s,a]
    rw [div_mul_cancel₀ _ physicalPeriod_pos.ne']
  simpa only [hEndQ,hEndS] using h.2

/-- Original `sourceLiftSpatialExtension_isSmoothUnitLift` guarantee for the `MixedTime` construction; the complete source hypotheses are retained. -/
theorem sourceLiftSpatialExtension_isSmoothUnitLift (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1)
    (hp : IsPeriodicField (sourceQuaternion v)) (eta : ℝ) (he : 0<eta) (sc : ℍ)
    (hc : HasConstantCollar (sourceQuaternion v) eta sc) (hi : hopf q₀=sc) :
    IsSmoothUnitLift (sourceQuaternion v) (sourceLiftSpatialExtension v hv q₀ h₀) := by
  refine ⟨contDiff_sourceLiftSpatialExtension v hv q₀ h₀, fun x =>
    ⟨sourceLiftSpatialExtension_unit v hv q₀ h₀ x, ?_⟩⟩
  change hopf (sourceLiftExtension v hv q₀ h₀ ((sourcePositionInverse x).1,x 0))=_
  rw [sourceLiftExtension_hopf_global v hv hu q₀ h₀ (sourcePositionInverse x).1
    (hi.trans (collar_initial_face _ hp eta he sc hc (sourcePositionInverse x).1).symm)]
  exact congrArg (sourceQuaternion v) (sourcePosition_inverse x)

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
