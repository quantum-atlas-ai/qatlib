/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.WordProduct
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceFrameBounds

set_option backward.isDefEq.respectTransparency false

/-! # Actual all-order horizontal-coefficient bounds from the executed source cache -/
set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
open Finset
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Original `sourceQuaternion_word` guarantee for the `SourceCoefficientWord` construction; the complete source hypotheses are retained. -/
theorem sourceQuaternion_word (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (w : List (Fin 3)) : spatialWordPartial (sourceQuaternion v) w=
      fun x => spinOfVector (spatialWordPartial v w x) :=
  spatialWordPartial_clm spinEmbedding.toContinuousLinearMap v hv w

/-- Original `sourceHorizontalQuaternion_word_bound` guarantee for the `SourceCoefficientWord` construction; the complete source hypotheses are retained. -/
theorem sourceHorizontalQuaternion_word_bound (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (M : ℕ → ℝ) (w : List (Fin 3)) (x : SpatialPoint)
    (hb : ∀ u : List (Fin 3), u.length ≤ w.length+1 →
      ‖spatialWordPartial v u x‖ ≤ M u.length) :
    ‖spatialWordPartial (sourceHorizontalQuaternion v) w x‖ ≤
      wordProductMajorant M (fun j => M (j+1)) w.length/2 := by
  have hM (j : ℕ) (hj : j ≤ w.length+1) : 0 ≤ M j := by
    have h := hb (List.replicate j 0) (by simpa using hj)
    exact (norm_nonneg _).trans (by simpa only [List.length_replicate] using h)
  have hs := contDiff_sourceQuaternion hv
  have hd := contDiff_sourceXDerivative hv
  have hsB : ∀ u : List (Fin 3), u.length ≤ w.length →
      ‖spatialWordPartial (sourceQuaternion v) u x‖ ≤ M u.length := by
    intro u hu
    rw [sourceQuaternion_word v hv,spinOfVector_norm]
    exact hb u (hu.trans (Nat.le_succ _))
  have hdB : ∀ u : List (Fin 3), u.length ≤ w.length →
      ‖spatialWordPartial (sourceXDerivative v) u x‖ ≤ M (u.length+1) := by
    intro u hu
    change ‖spatialWordPartial (spatialWordPartial (sourceQuaternion v) [0]) u x‖ ≤ _
    rw [← spatialWordPartial_append,sourceQuaternion_word v hv,spinOfVector_norm]
    have hlen : (u++[0] : List (Fin 3)).length=u.length+1 := by simp
    exact (hb (u++[0]) (by simpa using Nat.add_le_add_right hu 1)).trans_eq
      (congrArg M hlen)
  have hp := spatialWordPartial_mul_norm_le (sourceQuaternion v) (sourceXDerivative v)
    hs hd M (fun j => M (j+1)) w x
    (fun j hj => hM j (hj.trans (Nat.le_succ _)))
    (fun j hj => hM (j+1) (Nat.add_le_add_right hj 1)) hsB hdB
  change ‖spatialWordPartial (fun y => (-1/2 : ℝ) •
    (sourceQuaternion v y*sourceXDerivative v y)) w x‖ ≤ _
  rw [spatialWordPartial_const_smul _ (hs.mul hd),norm_smul]
  norm_num only [Real.norm_eq_abs,abs_of_neg (by norm_num : (-1/2 : ℝ)<0),neg_div,neg_neg]
  linarith

/-- The normalized source coefficient includes its one chain-rule factor L. -/
theorem sourceHorizontalQuaternion_unit (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (u : SpatialPoint) :
    sourceHorizontalQuaternion (unitCoordinateSpin v) u=
      physicalPeriod • sourceHorizontalQuaternion v (physicalPeriod • u) := by
  have hx := congrFun (spatialWordPartial_scale (sourceQuaternion v)
    (contDiff_sourceQuaternion hv) physicalPeriod [0]) u
  have hdx : sourceXDerivative (unitCoordinateSpin v) u=
      physicalPeriod • sourceXDerivative v (physicalPeriod • u) := by
    change spatialWordPartial (fun x => sourceQuaternion v (physicalPeriod • x)) [0] u =
      physicalPeriod • spatialWordPartial (sourceQuaternion v) [0] (physicalPeriod • u)
    simpa only [List.length_cons,List.length_nil,Nat.zero_add,pow_one] using hx
  change (-1/2 : ℝ) • (sourceQuaternion v (physicalPeriod • u)*
    sourceXDerivative (unitCoordinateSpin v) u)=_
  rw [hdx,mul_smul_comm,smul_smul]
  change ((-1/2 : ℝ)*physicalPeriod) • _=
    physicalPeriod • ((-1/2 : ℝ) • _)
  rw [smul_smul,mul_comm]

/-- It is the same physical raw lift that solves the normalized ODE.
The unit source is not assumed to have physical period L. -/
theorem sourceLiftSpatialExtension_unit_timePartial (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1)
    (u : SpatialPoint) (hu0 : 0 ≤ u 0 ∧ u 0 ≤ 1) :
    spatialWordPartial (fun x => sourceLiftSpatialExtension v hv q₀ h₀ (physicalPeriod • x)) [0] u=
      sourceLiftSpatialExtension v hv q₀ h₀ (physicalPeriod • u)*
        sourceHorizontalQuaternion (unitCoordinateSpin v) u := by
  rw [spatialWordPartial_scale _ (contDiff_sourceLiftSpatialExtension v hv q₀ h₀)]
  simp only [List.length_cons,List.length_nil,Nat.zero_add,pow_one,spatialWordPartial]
  have hscaled : 0 ≤ (physicalPeriod • u) 0 ∧ (physicalPeriod • u) 0 ≤ physicalPeriod := by
    change 0 ≤ physicalPeriod*u 0 ∧ physicalPeriod*u 0 ≤ physicalPeriod
    constructor
    · exact mul_nonneg physicalPeriod_pos.le hu0.1
    · simpa only [mul_one] using mul_le_mul_of_nonneg_left hu0.2 physicalPeriod_pos.le
  rw [sourceLiftSpatialExtension_timePartial v hv hu q₀ h₀ _ hscaled,
    sourceHorizontalQuaternion_unit v hv,mul_smul_comm]

/-- Total extension of the finite cache; the proof only consumes orders ≤9. -/
def sourceFrameUnitMajorant (packet : SourceFrameBoundPacket) (n : ℕ) : ℚ :=
  if hn : n<10 then sourceFrameUnitBound packet ⟨n,hn⟩ else 0

/-- The very same rational binomial formula as the implemented κ_r. -/
def sourceFrameCoefficientMajorant (packet : SourceFrameBoundPacket) (r : Fin 9) : ℚ :=
  ∑ j ∈ range (r.val+1), (r.val.choose j : ℚ)/2 *
    sourceFrameUnitMajorant packet j*sourceFrameUnitMajorant packet (r.val-j+1)

/-- Original `sourceFrameCoefficientMajorant_cast` guarantee for the `SourceCoefficientWord` construction; the complete source hypotheses are retained. -/
theorem sourceFrameCoefficientMajorant_cast (packet : SourceFrameBoundPacket) (r : Fin 9) :
    (sourceFrameCoefficientMajorant packet r : ℝ)=
      wordProductMajorant (fun j => (sourceFrameUnitMajorant packet j : ℝ))
        (fun j => (sourceFrameUnitMajorant packet (j+1) : ℝ)) r.val/2 := by
  simp only [sourceFrameCoefficientMajorant,wordProductMajorant,Rat.cast_sum,
    Rat.cast_mul,Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat,Finset.sum_div]
  apply sum_congr rfl
  intro j hj
  ring

/-- One successful actual bound execution now also supplies κ_0,...,κ_8 for
its actual normalized source coefficient. No reference-lift bound is input. -/
theorem sourceFrameBoundRun_coefficient_correct (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds) :
    ∃ packet labels, sourceFrameBoundRun bounds=some (packet,labels) ∧
      labels.length=(if sourceMeanCompressedBound (bounds 1)=0 then 1 else 9) ∧
      (∀ order ∈ labels, 1 ≤ order ∧ order ≤ 9) ∧
      (∀ (r : Fin 9) (w : List (Fin 3)), w.length=r.val → ∀ u, InUnitCube u →
        ‖spatialWordPartial (sourceHorizontalQuaternion (unitCoordinateSpin v)) w u‖ ≤
          (sourceFrameCoefficientMajorant packet r : ℝ)) := by
  obtain ⟨packet,labels,hrun,hlen,hlabels,hphys,hunit⟩ :=
    sourceFrameBoundRun_correct v hv hu hp bounds hb
  refine ⟨packet,labels,hrun,hlen,hlabels,?_⟩
  intro r w hw u hucube
  rw [sourceFrameCoefficientMajorant_cast,← hw]
  apply sourceHorizontalQuaternion_word_bound _ (contDiff_unitCoordinateSpin v hv)
  intro z hz
  have hlt : z.length<10 := by omega
  simpa only [sourceFrameUnitMajorant,dif_pos hlt] using
    hunit ⟨z.length,hlt⟩ z rfl u hucube

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
