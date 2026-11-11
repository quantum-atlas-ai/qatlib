/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourcePath
import Mathlib.Tactic.FinCases

/-!
# Original three-component spin to the horizontal transport family

The source derivative is its actual spatial Frechet derivative along e_0.
The coefficient path is built from that source, not supplied as a smooth
path name. One fixed initial quaternion is used in the transverse family.
-/

set_option autoImplicit false
noncomputable section
open scoped Quaternion RealInnerProductSpace Topology ContDiff
open Set
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Definition of position Linear in the Hopf Atlas construction. -/
private def positionLinear : TransversePoint × ℝ →ₗ[ℝ] SpatialPoint where
  toFun z := WithLp.toLp 2 ![z.2, z.1 0, z.1 1]
  map_add' a b := by ext j; fin_cases j <;> rfl
  map_smul' c a := by ext j; fin_cases j <;> rfl

/-- Definition of source Position in the Hopf Atlas construction. -/
def sourcePosition : TransversePoint × ℝ →L[ℝ] SpatialPoint := positionLinear.toContinuousLinearMap

/-- Definition of imaginary Vector Linear in the Hopf Atlas construction. -/
private def imaginaryVectorLinear : ℍ →ₗ[ℝ] SpatialPoint where
  toFun q := WithLp.toLp 2 ![q.imI, q.imJ, q.imK]
  map_add' a b := by ext j; fin_cases j <;> rfl
  map_smul' c a := by ext j; fin_cases j <;> rfl

/-- Definition of imaginary Vector in the Hopf Atlas construction. -/
def imaginaryVector : ℍ →L[ℝ] SpatialPoint := imaginaryVectorLinear.toContinuousLinearMap

/-- Original `spinOfVector_imaginaryVector` guarantee for the `HorizontalFamily` construction; the complete source hypotheses are retained. -/
theorem spinOfVector_imaginaryVector (q : ℍ) (hq : q.re=0) :
    spinOfVector (imaginaryVector q)=q := by
  change (⟨0, q.imI, q.imJ, q.imK⟩ : ℍ)=q
  ext <;> simp [hq]

/-- Definition of source Quaternion in the Hopf Atlas construction. -/
def sourceQuaternion (v : SpatialPoint → SpatialPoint) (x : SpatialPoint) : ℍ := spinOfVector (v x)

/-- Definition of source XDerivative in the Hopf Atlas construction. -/
def sourceXDerivative (v : SpatialPoint → SpatialPoint) (x : SpatialPoint) : ℍ :=
  fderiv ℝ (sourceQuaternion v) x (EuclideanSpace.single 0 1)

/-- Definition of source Horizontal Quaternion in the Hopf Atlas construction. -/
def sourceHorizontalQuaternion (v : SpatialPoint → SpatialPoint) (x : SpatialPoint) : ℍ :=
  horizontalCoefficient (sourceQuaternion v x) (sourceXDerivative v x)

/-- Original `contDiff_sourceQuaternion` guarantee for the `HorizontalFamily` construction; the complete source hypotheses are retained. -/
theorem contDiff_sourceQuaternion {v : SpatialPoint → SpatialPoint} (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (sourceQuaternion v) := spinEmbedding.toContinuousLinearMap.contDiff.comp hv

/-- Original `contDiff_sourceXDerivative` guarantee for the `HorizontalFamily` construction; the complete source hypotheses are retained. -/
theorem contDiff_sourceXDerivative {v : SpatialPoint → SpatialPoint} (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (sourceXDerivative v) :=
  ((contDiff_sourceQuaternion hv).fderiv_right (m := ∞) (by rfl)).clm_apply contDiff_const

/-- Original `contDiff_sourceHorizontalQuaternion` guarantee for the `HorizontalFamily` construction; the complete source hypotheses are retained. -/
theorem contDiff_sourceHorizontalQuaternion {v : SpatialPoint → SpatialPoint} (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (sourceHorizontalQuaternion v) :=
  ((contDiff_sourceQuaternion hv).mul (contDiff_sourceXDerivative hv)).const_smul _

/-- Definition of horizontal Coefficient Source in the Hopf Atlas construction. -/
def horizontalCoefficientSource (v : SpatialPoint → SpatialPoint) (z : TransversePoint × ℝ) : SpatialPoint :=
  imaginaryVector (sourceHorizontalQuaternion v (sourcePosition z))

/-- Original `contDiff_horizontalCoefficientSource` guarantee for the `HorizontalFamily` construction; the complete source hypotheses are retained. -/
theorem contDiff_horizontalCoefficientSource {v : SpatialPoint → SpatialPoint} (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (horizontalCoefficientSource v) :=
  imaginaryVector.contDiff.comp ((contDiff_sourceHorizontalQuaternion hv).comp sourcePosition.contDiff)

/-- Definition of horizontal Coefficient Paths in the Hopf Atlas construction. -/
def horizontalCoefficientPaths (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v) :
    TransversePoint → CoefficientPath :=
  sourcePath (horizontalCoefficientSource v) (contDiff_horizontalCoefficientSource hv).continuous

/-- Original `contDiff_horizontalCoefficientPaths` guarantee for the `HorizontalFamily` construction; the complete source hypotheses are retained. -/
theorem contDiff_horizontalCoefficientPaths (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (horizontalCoefficientPaths v hv) :=
  contDiff_sourcePath (contDiff_horizontalCoefficientSource hv)

/-- Original `sourcePosition_hasDerivAt` guarantee for the `HorizontalFamily` construction; the complete source hypotheses are retained. -/
theorem sourcePosition_hasDerivAt (p : TransversePoint) (t : ℝ) :
    HasDerivAt (fun u : ℝ => sourcePosition (p, u)) (EuclideanSpace.single 0 1) t := by
  have hi := (hasDerivAt_const t p).prodMk (hasDerivAt_id t)
  apply (sourcePosition.hasFDerivAt.comp_hasDerivAt t hi).congr_deriv
  ext j
  fin_cases j <;> simp [sourcePosition, positionLinear]

/-- Original `sourceCurve_hasDerivAt` guarantee for the `HorizontalFamily` construction; the complete source hypotheses are retained. -/
theorem sourceCurve_hasDerivAt {v : SpatialPoint → SpatialPoint} (hv : ContDiff ℝ ∞ v)
    (p : TransversePoint) (t : ℝ) :
    HasDerivAt (fun u : ℝ => sourceQuaternion v (sourcePosition (p, u)))
      (sourceXDerivative v (sourcePosition (p, t))) t :=
  ((contDiff_sourceQuaternion hv).differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
    (sourcePosition_hasDerivAt p t)

/-- Original `horizontalCoefficientPaths_embed` guarantee for the `HorizontalFamily` construction; the complete source hypotheses are retained. -/
theorem horizontalCoefficientPaths_embed (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (p : TransversePoint) (t : TransportTime) :
    spinOfVector (horizontalCoefficientPaths v hv p t) =
      sourceHorizontalQuaternion v (sourcePosition (p, t)) := by
  apply spinOfVector_imaginaryVector
  apply horizontal_re
  exact source_tangent (sourceCurve_hasDerivAt hv p) (fun _ => rfl)
    (fun u => (spinOfVector_norm (v (sourcePosition (p, u)))).trans (hu _)) t

/-- Definition of source Lift Paths in the Hopf Atlas construction. -/
def sourceLiftPaths (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (q₀ : ℍ) (h₀ : ‖q₀‖=1) (p : TransversePoint) : QuaternionPath :=
  pathTransport q₀ h₀ (horizontalCoefficientPaths v hv p)

/-- Original `contDiff_sourceLiftPaths` guarantee for the `HorizontalFamily` construction; the complete source hypotheses are retained. -/
theorem contDiff_sourceLiftPaths (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (q₀ : ℍ) (h₀ : ‖q₀‖=1) : ContDiff ℝ ∞ (sourceLiftPaths v hv q₀ h₀) :=
  (contDiff_pathTransport q₀ h₀).comp (contDiff_horizontalCoefficientPaths v hv)

/-- Original `sourceLiftPaths_hasDerivWithinAt` guarantee for the `HorizontalFamily` construction; the complete source hypotheses are retained. -/
theorem sourceLiftPaths_hasDerivWithinAt (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1) (p : TransversePoint)
    (t : ℝ) (ht : t ∈ Icc 0 physicalPeriod) :
    HasDerivWithinAt (extendPath (sourceLiftPaths v hv q₀ h₀ p))
      (extendPath (sourceLiftPaths v hv q₀ h₀ p) t*
        sourceHorizontalQuaternion v (sourcePosition (p, t))) (Icc 0 physicalPeriod) t := by
  have h := pathTransport_hasDerivWithinAt q₀ h₀ (horizontalCoefficientPaths v hv p) t ht
  rw [extendPath_on (horizontalCoefficientPaths v hv p) t ht,
    horizontalCoefficientPaths_embed v hv hu p ⟨t, ht⟩] at h
  exact h

/-- The family built from the original spin has the prescribed Hopf image.
Only initial compatibility is assumed; the identity along the interval is proved. -/
theorem sourceLiftPaths_hopf (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1) (p : TransversePoint)
    (hi : hopf q₀=sourceQuaternion v (sourcePosition (p, 0))) (t : TransportTime) :
    hopf (sourceLiftPaths v hv q₀ h₀ p t)=sourceQuaternion v (sourcePosition (p, t)) := by
  let q := extendPath (sourceLiftPaths v hv q₀ h₀ p)
  let s := fun u : ℝ => sourceQuaternion v (sourcePosition (p, u))
  let ds := fun u : ℝ => sourceXDerivative v (sourcePosition (p, u))
  have hsc : Continuous (fun u : ℝ => sourcePosition (p, u)) :=
    sourcePosition.continuous.comp (continuous_const.prodMk continuous_id)
  have hdc : ContinuousOn ds (Icc 0 physicalPeriod) :=
    ((contDiff_sourceXDerivative hv).continuous.comp hsc).continuousOn
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hdc
  have hq : ∀ u ∈ Ico 0 physicalPeriod,
      HasDerivWithinAt q (q u*horizontalCoefficient (s u) (ds u)) (Ici u) u := by
    intro u hu'
    apply (sourceLiftPaths_hasDerivWithinAt v hv hu q₀ h₀ p u ⟨hu'.1, hu'.2.le⟩).mono_of_mem_nhdsWithin
    exact Filter.mem_of_superset
      (Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hu'.2)) self_mem_nhdsWithin)
      (by intro y hy; exact ⟨hu'.1.trans hy.2, hy.1.le⟩)
  have hstart : extendPath (sourceLiftPaths v hv q₀ h₀ p) 0=q₀ := by
    rw [extendPath_on _ 0 ⟨le_rfl, physicalPeriod_pos.le⟩]
    exact pathTransport_start q₀ h₀ _
  have h := horizontal_transport (sourceCurve_hasDerivAt hv p) (fun _ => rfl)
    (fun u => (spinOfVector_norm (v (sourcePosition (p, u)))).trans (hu _))
    (fun u hu' => hM u ⟨hu'.1, hu'.2.le⟩) (continuous_extendPath _).continuousOn hq
    (by simpa only [hstart] using h₀) (by simpa only [hstart] using hi) t t.2
  simpa only [q, s, extendPath_coe] using h.2

/-- Original `wrapped_coordinate_bounds` guarantee for the `HorizontalFamily` construction; the complete source hypotheses are retained. -/
private theorem wrapped_coordinate_bounds (x : ℝ) :
    0 ≤ x+physicalPeriod*(-(⌊x/physicalPeriod⌋ : ℝ)) ∧
      x+physicalPeriod*(-(⌊x/physicalPeriod⌋ : ℝ)) ≤ physicalPeriod := by
  have hlo := (le_div_iff₀ physicalPeriod_pos).mp (Int.floor_le (x/physicalPeriod))
  have hhi := (div_lt_iff₀ physicalPeriod_pos).mp (Int.lt_floor_add_one (x/physicalPeriod))
  constructor <;> nlinarith

/-- Periodicity extends the original fundamental-cube collar to the whole
initial transverse plane. The floor is used only in this exact geometric
proof, not as a computable phase-selection operation. -/
theorem collar_initial_face (s : QuaternionField) (hp : IsPeriodicField s)
    (eta : ℝ) (he : 0 < eta) (sc : ℍ) (hc : HasConstantCollar s eta sc)
    (p : TransversePoint) : s (sourcePosition (p,0))=sc := by
  let n : Fin 3 → ℤ := ![0, -⌊p 0/physicalPeriod⌋, -⌊p 1/physicalPeriod⌋]
  let w := sourcePosition (p,0)+latticeShift n
  have hw : InFundamentalCube w := by
    intro j
    fin_cases j
    · simpa [w, sourcePosition, positionLinear, latticeShift, n] using
        (show 0 ≤ (0 : ℝ) ∧ 0 ≤ physicalPeriod from ⟨le_rfl, physicalPeriod_pos.le⟩)
    · simpa [w, sourcePosition, positionLinear, latticeShift, n] using wrapped_coordinate_bounds (p 0)
    · simpa [w, sourcePosition, positionLinear, latticeShift, n] using wrapped_coordinate_bounds (p 1)
  have hs := hc w hw (by
    refine ⟨0, Or.inl ?_⟩
    simpa [w, sourcePosition, positionLinear, latticeShift, n] using he.le)
  exact (hp (sourcePosition (p,0)) n).symm.trans hs

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
