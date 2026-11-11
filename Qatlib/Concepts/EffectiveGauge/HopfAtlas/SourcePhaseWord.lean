/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.SourcePhasePrimitive

set_option backward.isDefEq.respectTransparency false

/-! # Effective bounds Lambda0,...,Lambda7 for the actual source real phase -/
set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- The original Lambda recurrence, with no phase modulus as an input. -/
def sourceFrameLambdaMajorant (packet : SourceFrameBoundPacket) (r : Fin 8) : ℚ :=
  if hr : r.val=0 then 7*sourceFrameGammaMajorant packet 0 else
    sourceFrameGammaMajorant packet ⟨r.val-1,by omega⟩+7*sourceFrameGammaMajorant packet r

noncomputable section
open scoped Quaternion ContDiff

/-- Original `sourceFrameBoundRun_phase_correct` guarantee for the `SourcePhaseWord` construction; the complete source hypotheses are retained. -/
theorem sourceFrameBoundRun_phase_correct (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (bounds : ℕ → ℚ) (hb : OriginalPositiveJetBounds v bounds) :
    ∃ packet labels, sourceFrameBoundRun bounds=some (packet,labels) ∧
      labels.length=(if sourceMeanCompressedBound (bounds 1)=0 then 1 else 9) ∧
      (∀ order ∈ labels, 1 ≤ order ∧ order ≤ 9) ∧
      (∀ (q₀ : ℍ) (h₀ : ‖q₀‖=1) (r : Fin 8) (w : List (Fin 3)), w.length=r.val →
        ∀ x, InUnitCube x →
        ‖spatialWordPartial (sourceUnitRealPhase v hv q₀ h₀) w x‖ ≤
          (sourceFrameLambdaMajorant packet r : ℝ)) := by
  obtain ⟨packet,labels,hrun,hlen,hlabels,hGamma⟩ :=
    sourceFrameBoundRun_angular_correct v hv hu hp bounds hb
  refine ⟨packet,labels,hrun,hlen,hlabels,?_⟩
  intro q₀ h₀ r w hw x hx
  let gamma := wordAngularRate (sourceUnitTerminalRatio v hv q₀ h₀) 1
  let lambda := sourceUnitRealPhase v hv q₀ h₀
  have hgamma : ContDiff ℝ ∞ gamma :=
    contDiff_wordAngularRate _ (contDiff_sourceUnitTerminalRatio v hv q₀ h₀) 1
  have hlambda : ContDiff ℝ ∞ lambda := contDiff_sourceUnitRealPhase v hv q₀ h₀
  have hGnonneg (s : Fin 8) : (0 : ℝ) ≤ sourceFrameGammaMajorant packet s := by
    have h := hGamma q₀ h₀ s (List.replicate s.val 0) (by simp) 0
      (fun _ => ⟨le_rfl,zero_le_one⟩)
    exact (norm_nonneg _).trans h
  change ‖spatialWordPartial lambda w x‖ ≤ _
  by_cases hwone : (1 : Fin 3)∈w
  · let z := w.erase 1
    have hperm : w.Perm (1::z) := List.perm_cons_erase hwone
    have hzlen : z.length=r.val-1 := by
      have h := hperm.length_eq
      simp only [List.length_cons] at h
      omega
    have hrpos : 0<r.val := by
      have h := hperm.length_eq
      simp only [List.length_cons] at h
      omega
    have hlast : (1::z).Perm (z++[1]) :=
      (List.perm_append_comm : ([1]++z).Perm (z++[1]))
    rw [spatialWordPartial_perm lambda hlambda hperm,
      spatialWordPartial_perm lambda hlambda hlast,spatialWordPartial_append,
      sourceUnitRealPhase_y_partial v hv hu q₀ h₀]
    have hbG := hGamma q₀ h₀ ⟨r.val-1,by omega⟩ z hzlen x hx
    have hG := hGnonneg r
    have hΛ : (sourceFrameLambdaMajorant packet r : ℝ)=
        (sourceFrameGammaMajorant packet ⟨r.val-1,by omega⟩ : ℝ)+
          7*(sourceFrameGammaMajorant packet r : ℝ) := by
      simp only [sourceFrameLambdaMajorant,dif_neg (Nat.ne_of_gt hrpos),Rat.cast_add,
        Rat.cast_mul,Rat.cast_ofNat]
    rw [hΛ]
    exact hbG.trans (by linarith)
  · have hreal : lambda=coordinatePrimitive gamma :=
      sourceUnitRealPhase_coordinatePrimitive v hv hu q₀ h₀
    rw [hreal]
    have hbG : ∀ y, InUnitCube y → ‖spatialWordPartial gamma w y‖ ≤
        (sourceFrameGammaMajorant packet r : ℝ) := hGamma q₀ h₀ r w hw
    have hbound := coordinatePrimitive_transverse_word_bound gamma hgamma w hwone
      (sourceFrameGammaMajorant packet r : ℝ) (hGnonneg r) hbG x hx
    apply hbound.trans
    by_cases hrzero : r.val=0
    · have hr : r=0 := Fin.ext hrzero
      subst r
      have hG := hGnonneg 0
      change (sourceFrameGammaMajorant packet 0 : ℝ) ≤
        ((7*sourceFrameGammaMajorant packet 0 : ℚ) : ℝ)
      push_cast
      linarith
    · have hG := hGnonneg r
      have hGprev := hGnonneg ⟨r.val-1,by omega⟩
      simp only [sourceFrameLambdaMajorant,dif_neg hrzero,Rat.cast_add,Rat.cast_mul,Rat.cast_ofNat]
      linarith

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
