/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.TransportWordBound

set_option backward.isDefEq.respectTransparency false

/-! # Original source cache to actual raw-lift derivative majorants Q0,...,Q8 -/
set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Total extension of the finite κ cache. Its zero tail is never consumed
by a Q_r calculation with r≤8. -/
def sourceFrameCoefficientNat (packet : SourceFrameBoundPacket) (n : ℕ) : ℚ :=
  if hn : n<9 then sourceFrameCoefficientMajorant packet ⟨n,hn⟩ else 0

/-- Definition of source Frame Transport Majorant in the Hopf Atlas construction. -/
def sourceFrameTransportMajorant (packet : SourceFrameBoundPacket) (r : Fin 9) : ℚ :=
  transportWordMajorant (sourceFrameCoefficientNat packet) r.val

noncomputable section
open scoped Quaternion ContDiff

/-- Original `sourceHorizontalQuaternion_pure` guarantee for the `SourceTransportWord` construction; the complete source hypotheses are retained. -/
theorem sourceHorizontalQuaternion_pure (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (x : SpatialPoint) :
    (sourceHorizontalQuaternion v x).re=0 := by
  have h := normalizedSourceGenerator_re v hv hu (sourcePositionInverse x).1 1 (x 0)
  change (1 • sourceHorizontalQuaternion v
    (sourcePosition ((sourcePositionInverse x).1,1*x 0))).re=0 at h
  simp only [one_mul,one_smul] at h
  change (sourceHorizontalQuaternion v (sourcePosition (sourcePositionInverse x))).re=0 at h
  rw [sourcePosition_inverse] at h
  exact h

/-- Every bound is computed from the single executed original-source cache;
no derivative bound for the unknown raw lift is an input assumption. The
unit initial seed is arbitrary, so in particular may be the actual fixed
source-selected seed used by the periodic reference. -/
theorem sourceFrameBoundRun_transport_correct (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds) :
    ∃ packet labels, sourceFrameBoundRun bounds=some (packet,labels) ∧
      labels.length=(if sourceMeanCompressedBound (bounds 1)=0 then 1 else 9) ∧
      (∀ order ∈ labels, 1 ≤ order ∧ order ≤ 9) ∧
      (∀ (q₀ : ℍ) (h₀ : ‖q₀‖=1) (r : Fin 9) (w : List (Fin 3)), w.length=r.val → ∀ u, InUnitCube u →
        ‖spatialWordPartial
          (fun y => sourceLiftSpatialExtension v hv q₀ h₀ (physicalPeriod • y)) w u‖ ≤
          (sourceFrameTransportMajorant packet r : ℝ)) := by
  obtain ⟨packet,labels,hrun,hlen,hlabels,hcoeff⟩ :=
    sourceFrameBoundRun_coefficient_correct v hv hu hp bounds hb
  have hκ : ∀ n, 0 ≤ sourceFrameCoefficientNat packet n := by
    intro n
    by_cases hn : n<9
    · have h := hcoeff ⟨n,hn⟩ (List.replicate n 0) (by simp) 0
        (fun _ => ⟨le_rfl,zero_le_one⟩)
      have hz := (norm_nonneg _).trans h
      exact Rat.cast_nonneg.mp (by simpa only [sourceFrameCoefficientNat,dif_pos hn] using hz)
    · simp only [sourceFrameCoefficientNat,dif_neg hn,le_refl]
  refine ⟨packet,labels,hrun,hlen,hlabels,?_⟩
  intro q₀ h₀ r w hw u hucube
  let q := fun y => sourceLiftSpatialExtension v hv q₀ h₀ (physicalPeriod • y)
  let K := sourceHorizontalQuaternion (unitCoordinateSpin v)
  have hq : ContDiff ℝ ∞ q :=
    (contDiff_sourceLiftSpatialExtension v hv q₀ h₀).comp (contDiff_id.const_smul physicalPeriod)
  have hK : ContDiff ℝ ∞ K := contDiff_sourceHorizontalQuaternion (contDiff_unitCoordinateSpin v hv)
  have huunit : ∀ y, ‖unitCoordinateSpin v y‖=1 := fun y => hu (physicalPeriod • y)
  have hKword : ∀ z : List (Fin 3), z.length ≤ 8 → ∀ y, InUnitCube y →
      ‖spatialWordPartial K z y‖ ≤ (sourceFrameCoefficientNat packet z.length : ℝ) := by
    intro z hz y hy
    have hlt : z.length<9 := by omega
    simpa only [sourceFrameCoefficientNat,dif_pos hlt] using
      hcoeff ⟨z.length,hlt⟩ z rfl y hy
  simpa only [q,hw,sourceFrameTransportMajorant] using transportWordBound_on_cube q K hq hK
    (fun y _ => sourceLiftSpatialExtension_unit v hv q₀ h₀ (physicalPeriod • y))
    (fun y _ => sourceHorizontalQuaternion_pure _ (contDiff_unitCoordinateSpin v hv) huunit y)
    (sourceLiftSpatialExtension_unit_timePartial v hv hu q₀ h₀) q₀
    (sourceLiftSpatialExtension_unit_initial v hv hu q₀ h₀)
    (fun j => (transportWordMajorant (sourceFrameCoefficientNat packet) j : ℝ))
    (fun j => (sourceFrameCoefficientNat packet j : ℝ)) 8
    (transportWordMajorant_spec _ hκ 8) hKword w (by omega) u hucube

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
