/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.CutoffWord
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.ScalarWordProduct
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourcePhaseWord

set_option backward.isDefEq.respectTransparency false

/-! # The actual cutoff-times-real-phase correction has source-computed majorants -/
set_option autoImplicit false
open Finset
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of source Frame Lambda Nat in the Hopf Atlas construction. -/
def sourceFrameLambdaNat (packet : SourceFrameBoundPacket) (n : ℕ) : ℚ :=
  if hn : n<8 then sourceFrameLambdaMajorant packet ⟨n,hn⟩ else 0

/-- Definition of source Frame Correction Majorant in the Hopf Atlas construction. -/
def sourceFrameCorrectionMajorant (packet : SourceFrameBoundPacket) (eta : ℚ) (r : Fin 8) : ℚ :=
  ∑ j ∈ range (r.val+1), (r.val.choose j : ℚ)*cutoffUnitMajorant eta j*
    sourceFrameLambdaNat packet (r.val-j)

noncomputable section
open scoped Quaternion ContDiff

/-- Definition of source Correction Phase in the Hopf Atlas construction. -/
def sourceCorrectionPhase (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (q₀ : ℍ) (h₀ : ‖q₀‖=1) (eta : ℝ) (x : SpatialPoint) : ℝ :=
  -(unitCutoffField eta x*sourceUnitRealPhase v hv q₀ h₀ x)

/-- Original `contDiff_sourceCorrectionPhase` guarantee for the `SourceCorrectionWord` construction; the complete source hypotheses are retained. -/
theorem contDiff_sourceCorrectionPhase (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (q₀ : ℍ) (h₀ : ‖q₀‖=1) (eta : ℝ) : ContDiff ℝ ∞ (sourceCorrectionPhase v hv q₀ h₀ eta) :=
  ((contDiff_unitCutoffField eta).mul (contDiff_sourceUnitRealPhase v hv q₀ h₀)).neg

/-- Original `sourceFrameCorrectionMajorant_cast` guarantee for the `SourceCorrectionWord` construction; the complete source hypotheses are retained. -/
theorem sourceFrameCorrectionMajorant_cast (packet : SourceFrameBoundPacket) (eta : ℚ) (r : Fin 8) :
    (sourceFrameCorrectionMajorant packet eta r : ℝ)=
      wordProductMajorant (fun j => (cutoffUnitMajorant eta j : ℝ))
        (fun j => (sourceFrameLambdaNat packet j : ℝ)) r.val := by
  simp only [sourceFrameCorrectionMajorant,wordProductMajorant,Rat.cast_sum,Rat.cast_mul,Rat.cast_natCast]

/-- The correction phase is the actual negative product, not a supplied
unknown reference phase. Both factors have already source-derived bounds. -/
theorem sourceFrameBoundRun_correction_correct (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds) (eta : ℚ) (he : 0<eta) :
    ∃ packet labels, sourceFrameBoundRun bounds=some (packet,labels) ∧
      labels.length=(if sourceMeanCompressedBound (bounds 1)=0 then 1 else 9) ∧
      (∀ order ∈ labels, 1 ≤ order ∧ order ≤ 9) ∧
      (∀ (q₀ : ℍ) (h₀ : ‖q₀‖=1) (r : Fin 8) (w : List (Fin 3)), w.length=r.val →
        ∀ x, InUnitCube x →
        ‖spatialWordPartial (sourceCorrectionPhase v hv q₀ h₀ (eta : ℝ)) w x‖ ≤
          (sourceFrameCorrectionMajorant packet eta r : ℝ)) := by
  obtain ⟨packet,labels,hrun,hlen,hlabels,hLambda⟩ :=
    sourceFrameBoundRun_phase_correct v hv hu hp bounds hb
  refine ⟨packet,labels,hrun,hlen,hlabels,?_⟩
  intro q₀ h₀ r w hw x hx
  have hD (j : ℕ) : (0 : ℝ) ≤ cutoffUnitMajorant eta j := by
    have h := unitCutoffField_word_bound eta he (List.replicate j 0) (0 : SpatialPoint)
    exact (norm_nonneg _).trans (by simpa only [List.length_replicate] using h)
  have hLambdaNat (j : ℕ) (hj : j ≤ w.length) : (0 : ℝ) ≤ sourceFrameLambdaNat packet j := by
    have hlt : j<8 := by omega
    have h := hLambda q₀ h₀ ⟨j,hlt⟩ (List.replicate j 0) (by simp) 0
      (fun _ => ⟨le_rfl,zero_le_one⟩)
    have hzero := (norm_nonneg _).trans h
    simpa only [sourceFrameLambdaNat,dif_pos hlt] using hzero
  have hprod := spatialWordPartial_real_mul_norm_le (unitCutoffField (eta : ℝ))
    (sourceUnitRealPhase v hv q₀ h₀) (contDiff_unitCutoffField _)
    (contDiff_sourceUnitRealPhase v hv q₀ h₀)
    (fun j => (cutoffUnitMajorant eta j : ℝ)) (fun j => (sourceFrameLambdaNat packet j : ℝ)) w x
    (fun j _ => hD j) hLambdaNat
    (fun z hz => unitCutoffField_word_bound eta he z x)
    (by
      intro z hz
      have hlt : z.length<8 := by omega
      simpa only [sourceFrameLambdaNat,dif_pos hlt] using hLambda q₀ h₀ ⟨z.length,hlt⟩ z rfl x hx)
  have heq : sourceCorrectionPhase v hv q₀ h₀ (eta : ℝ)=
      fun y => (-1 : ℝ) • (unitCutoffField (eta : ℝ) y*sourceUnitRealPhase v hv q₀ h₀ y) := by
    funext y
    simp [sourceCorrectionPhase]
  rw [heq,spatialWordPartial_const_smul
    (fun y => unitCutoffField (eta : ℝ) y*sourceUnitRealPhase v hv q₀ h₀ y)
    ((contDiff_unitCutoffField _).mul (contDiff_sourceUnitRealPhase v hv q₀ h₀)),norm_smul]
  norm_num only [Real.norm_eq_abs,abs_neg,abs_one,one_mul]
  rw [sourceFrameCorrectionMajorant_cast,← hw]
  exact hprod

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
