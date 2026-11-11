/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.WordAngular
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourceTransportWord

set_option backward.isDefEq.respectTransparency false

/-! # Same physical terminal ratio and its actual angular-rate majorants -/
set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- The finite rational Γ_r recurrence consumes Q through r+1. -/
def sourceFrameGammaMajorant (packet : SourceFrameBoundPacket) (r : Fin 8) : ℚ :=
  ∑ j ∈ Finset.range (r.val+1), (r.val.choose j : ℚ)*
    transportWordMajorant (sourceFrameCoefficientNat packet) j*
    transportWordMajorant (sourceFrameCoefficientNat packet) (r.val-j+1)

noncomputable section
open scoped Quaternion ContDiff

/-- Definition of source Unit Terminal Ratio in the Hopf Atlas construction. -/
def sourceUnitTerminalRatio (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (q₀ : ℍ) (h₀ : ‖q₀‖=1) (u : SpatialPoint) : ℍ :=
  sourceLiftSpatialExtension v hv q₀ h₀ (physicalPeriod • coordinateFace 0 1 u)*star q₀

/-- Original `contDiff_sourceUnitTerminalRatio` guarantee for the `SourceAngularWord` construction; the complete source hypotheses are retained. -/
theorem contDiff_sourceUnitTerminalRatio (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (q₀ : ℍ) (h₀ : ‖q₀‖=1) : ContDiff ℝ ∞ (sourceUnitTerminalRatio v hv q₀ h₀) :=
  (((contDiff_sourceLiftSpatialExtension v hv q₀ h₀).comp
    (contDiff_id.const_smul physicalPeriod)).comp (contDiff_coordinateFace 0 1)).mul contDiff_const

/-- This is the same terminal ratio used by the real phase construction. -/
theorem sourceUnitTerminalRatio_eq (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1) (u : SpatialPoint) :
    sourceUnitTerminalRatio v hv q₀ h₀ u=
      terminalRatio v hv q₀ h₀ (physicalPeriod • (sourcePositionInverse u).1) := by
  have hi : sourcePositionInverse (physicalPeriod • coordinateFace 0 1 u)=
      (physicalPeriod • (sourcePositionInverse u).1,physicalPeriod) := by
    apply Prod.ext
    · ext j
      fin_cases j <;> change physicalPeriod*(u _+(1-u 0)*(0 : ℝ))=physicalPeriod*u _ <;> ring
    · change physicalPeriod*(u 0+(1-u 0)*1)=physicalPeriod
      ring
  change sourceLiftExtension v hv q₀ h₀
    (sourcePositionInverse (physicalPeriod • coordinateFace 0 1 u))*star q₀=_
  rw [hi]
  exact congrArg (fun q : ℍ => q*star q₀)
    (sourceLiftExtension_eq v hv hu q₀ h₀ (physicalPeriod • (sourcePositionInverse u).1) transportFinish)

/-- Original `coordinateFace_zero_one_unit` guarantee for the `SourceAngularWord` construction; the complete source hypotheses are retained. -/
theorem coordinateFace_zero_one_unit (u : SpatialPoint) (hu : InUnitCube u) :
    InUnitCube (coordinateFace 0 1 u) := by
  intro i
  by_cases hi : i=0
  · subst i
    rw [coordinateFace_same]
    exact ⟨zero_le_one,le_rfl⟩
  · rw [coordinateFace_other _ _ _ _ hi]
    exact hu i

/-- Same word bound, with no derivative in the fixed face coordinate. -/
theorem sourceUnitTerminalRatio_word_bound (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (q₀ : ℍ) (h₀ : ‖q₀‖=1) (F : ℕ → ℝ)
    (w : List (Fin 3)) (u : SpatialPoint) (hF : 0 ≤ F w.length)
    (hb : ‖spatialWordPartial
      (fun y => sourceLiftSpatialExtension v hv q₀ h₀ (physicalPeriod • y)) w
        (coordinateFace 0 1 u)‖ ≤ F w.length) :
    ‖spatialWordPartial (sourceUnitTerminalRatio v hv q₀ h₀) w u‖ ≤ F w.length := by
  let q := fun y => sourceLiftSpatialExtension v hv q₀ h₀ (physicalPeriod • y)
  have hq : ContDiff ℝ ∞ q :=
    (contDiff_sourceLiftSpatialExtension v hv q₀ h₀).comp (contDiff_id.const_smul physicalPeriod)
  change ‖spatialWordPartial (fun y => q (coordinateFace 0 1 y)*star q₀) w u‖ ≤ _
  rw [spatialWordPartial_mul_const (fun y => q (coordinateFace 0 1 y))
      (hq.comp (contDiff_coordinateFace 0 1)) (star q₀) w,
    spatialWordPartial_coordinateFace q hq,norm_mul,Quaternion.norm_star,h₀,mul_one]
  by_cases hw : (0 : Fin 3)∈w
  · simpa only [if_pos hw,norm_zero] using hF
  · simpa only [if_neg hw] using hb

/-- Original `sourceFrameGammaMajorant_cast` guarantee for the `SourceAngularWord` construction; the complete source hypotheses are retained. -/
theorem sourceFrameGammaMajorant_cast (packet : SourceFrameBoundPacket) (r : Fin 8) :
    (sourceFrameGammaMajorant packet r : ℝ)=
      wordProductMajorant (fun j => (transportWordMajorant (sourceFrameCoefficientNat packet) j : ℝ))
        (fun j => (transportWordMajorant (sourceFrameCoefficientNat packet) (j+1) : ℝ)) r.val := by
  simp only [sourceFrameGammaMajorant,wordProductMajorant,Rat.cast_sum,Rat.cast_mul,Rat.cast_natCast]

/-- The original-source execution bounds the actual terminal angular field,
through order seven, using no unprovided phase or reference modulus. -/
theorem sourceFrameBoundRun_angular_correct (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds) :
    ∃ packet labels, sourceFrameBoundRun bounds=some (packet,labels) ∧
      labels.length=(if sourceMeanCompressedBound (bounds 1)=0 then 1 else 9) ∧
      (∀ order ∈ labels, 1 ≤ order ∧ order ≤ 9) ∧
      (∀ (q₀ : ℍ) (h₀ : ‖q₀‖=1) (r : Fin 8) (w : List (Fin 3)), w.length=r.val →
        ∀ u, InUnitCube u →
        ‖spatialWordPartial (wordAngularRate (sourceUnitTerminalRatio v hv q₀ h₀) 1) w u‖ ≤
          (sourceFrameGammaMajorant packet r : ℝ)) := by
  obtain ⟨packet,labels,hrun,hlen,hlabels,hQ⟩ :=
    sourceFrameBoundRun_transport_correct v hv hu hp bounds hb
  refine ⟨packet,labels,hrun,hlen,hlabels,?_⟩
  intro q₀ h₀ r w hw u hucube
  have hface := coordinateFace_zero_one_unit u hucube
  have hbound : ∀ z : List (Fin 3), z.length ≤ w.length+1 →
      ‖spatialWordPartial (sourceUnitTerminalRatio v hv q₀ h₀) z u‖ ≤
        (transportWordMajorant (sourceFrameCoefficientNat packet) z.length : ℝ) := by
    intro z hz
    have hlt : z.length<9 := by omega
    have hraw := hQ q₀ h₀ ⟨z.length,hlt⟩ z rfl _ hface
    have hnonneg : (0 : ℝ) ≤ transportWordMajorant (sourceFrameCoefficientNat packet) z.length :=
      (norm_nonneg _).trans hraw
    exact sourceUnitTerminalRatio_word_bound v hv q₀ h₀
      (fun j => (transportWordMajorant (sourceFrameCoefficientNat packet) j : ℝ)) z u hnonneg hraw
  rw [sourceFrameGammaMajorant_cast,← hw]
  exact wordAngularRate_word_bound _ (contDiff_sourceUnitTerminalRatio v hv q₀ h₀) 1 _ w u hbound

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
