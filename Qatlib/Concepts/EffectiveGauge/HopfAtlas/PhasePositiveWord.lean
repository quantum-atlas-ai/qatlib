/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.PhaseExponentialWord

set_option backward.isDefEq.respectTransparency false

/-!
# Phase Positive Word

Hopf Atlas constructions for Effective Gauge.
Proves `spatialWordPartial_phase_positive_norm_le`.
-/

set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Original `spatialWordPartial_phase_positive_norm_le` guarantee for the `PhasePositiveWord` construction; the complete source hypotheses are retained. -/
theorem spatialWordPartial_phase_positive_norm_le (f : SpatialPoint → ℝ) (hf : ContDiff ℝ ∞ f)
    (Phi : ℕ → ℚ) (N : ℕ) (x : SpatialPoint)
    (hPhi : ∀ z : List (Fin 3), 0<z.length → z.length ≤ N → ‖spatialWordPartial f z x‖ ≤ (Phi z.length : ℝ))
    (w : List (Fin 3)) (hw : w.length ≤ N) :
    ‖spatialWordPartial (fun y => phase (f y)) w x‖ ≤ (phaseWordMajorant Phi w.length : ℝ) := by
  suffices ∀ n ≤ N, ∀ z : List (Fin 3), z.length=n →
      ‖spatialWordPartial (fun y => phase (f y)) z x‖ ≤ (phaseWordMajorant Phi n : ℝ) from
    this w.length hw w rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn z hz
    rcases List.eq_nil_or_concat' z with rfl | ⟨u,i,rfl⟩
    · have hn0 : n=0 := hz.symm
      subst n
      simp [spatialWordPartial,phase_norm,phaseWordMajorant]
    · have hlen : u.length+1=n := by simpa only [List.length_append,List.length_singleton] using hz
      let df := fun y => realQuaternionCLM (spatialWordPartial f [i] y)
      let ep := fun y => iAxis*phase (f y)
      have hdf : ContDiff ℝ ∞ df := realQuaternionCLM.contDiff.comp (contDiff_spatialWordPartial f hf [i])
      have hep : ContDiff ℝ ∞ ep := contDiff_const.mul (contDiff_phase.comp hf)
      have hFB (v : List (Fin 3)) (hv : v.length ≤ u.length) :
          ‖spatialWordPartial df v x‖ ≤ (Phi (v.length+1) : ℝ) := by
        rw [spatialWordPartial_clm realQuaternionCLM _ (contDiff_spatialWordPartial f hf [i]),
          realQuaternionCLM_norm,← spatialWordPartial_append]
        simpa only [List.length_append,List.length_singleton] using hPhi (v++[i]) (by simp) (by simp; omega)
      have hGB (v : List (Fin 3)) (hv : v.length ≤ u.length) :
          ‖spatialWordPartial ep v x‖ ≤ (phaseWordMajorant Phi v.length : ℝ) := by
        change ‖spatialWordPartial (fun y => iAxis*phase (f y)) v x‖ ≤ _
        rw [spatialWordPartial_const_mul (fun y => phase (f y)) (contDiff_phase.comp hf),norm_mul,norm_iAxis,one_mul]
        exact ih v.length (by omega) (by omega) v rfl
      have hF (j : ℕ) (hj : j ≤ u.length) : (0 : ℝ) ≤ Phi (j+1) :=
        by simpa only [List.length_replicate] using (norm_nonneg _).trans (hFB (List.replicate j 0) (by simpa))
      have hG (j : ℕ) (hj : j ≤ u.length) : (0 : ℝ) ≤ phaseWordMajorant Phi j :=
        by simpa only [List.length_replicate] using (norm_nonneg _).trans (hGB (List.replicate j 0) (by simpa))
      rw [spatialWordPartial_append,spatialWordPartial_phase_first f hf i]
      have hprod := spatialWordPartial_mul_norm_le df ep hdf hep
        (fun j => (Phi (j+1) : ℝ)) (fun j => (phaseWordMajorant Phi j : ℝ)) u x hF hG hFB hGB
      rw [← hlen,phaseWordMajorant_succ_cast]
      exact hprod


end Qatlib.Concepts.EffectiveGauge.HopfAtlas
