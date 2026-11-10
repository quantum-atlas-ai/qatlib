/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.AxisRotations.FiniteHistory
import Qatlib.Foundations.MatrixAlgebra.TensorDiff

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators
open Qatlib.Foundations.MatrixGeometry.AxisRotations.History
open Qatlib.Foundations.MatrixAlgebra.TensorDiff

namespace Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Program

def clip (M x : ℝ) : ℝ := max (-M) (min x M)

theorem clip_mem (M : ℝ) (hM : 0 ≤ M) (x : ℝ) : clip M x ∈ Set.Icc (-M) M := by
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

theorem clip_eq (M x : ℝ) (hx : x ∈ Set.Icc (-M) M) : clip M x=x := by
  unfold clip
  rw [min_eq_left hx.2, max_eq_right hx.1]

theorem clip_lipschitz (M : ℝ) : LipschitzWith 1 (clip M) :=
  (LipschitzWith.id.min_const M).const_max (-M)

def fCoord (s : ℕ → ℝ) (t : ℕ) (u : Fin (t+1) → ℝ) : ℝ :=
  phi s t (fun a => u a.succ)

def FCoord (s : ℝ) {t : ℕ} (h : ℝ) (u : Fin (t+1) → ℝ) : ℝ := h+u 0*s^2*(1-s)

def spinReadout {N : ℕ} (s : ℕ → ℝ) (t : ℕ) (U : Fin (t+1) → Fin N → ℝ) : Fin N → ℝ :=
  fun i => fCoord s t (fun a => U a i)

def ampNext {r N : ℕ} (M : ℝ) (J : Fin N → (Fin r → Fin N) → ℝ)
    (s : ℕ → ℝ) (t : ℕ) (U : Fin (t+1) → Fin N → ℝ) : Fin N → ℝ :=
  fun i => clip M (FCoord (s t) (interaction J (spinReadout s t U) i) (fun a => U a i))

def ampHistory {r N : ℕ} (M : ℝ) (J : Fin N → (Fin r → Fin N) → ℝ)
    (seed : Fin N → ℝ) (s : ℕ → ℝ) : (t : ℕ) → Fin (t+1) → Fin N → ℝ
  | 0 => fun _ i => clip M (seed i)
  | t+1 => let U := ampHistory M J seed s t
    Fin.snoc U (ampNext M J s t U)

def ampOutput {r N : ℕ} (M : ℝ) (J : Fin N → (Fin r → Fin N) → ℝ)
    (seed : Fin N → ℝ) (s : ℕ → ℝ) (T : ℕ) : Fin N → ℝ :=
  fun i => clip 1 (ampHistory M J seed s T (Fin.last T) i)

theorem actual_amp_step {r N : ℕ} (M : ℝ) (J : Fin N → (Fin r → Fin N) → ℝ)
    (seed : Fin N → ℝ) (s : ℕ → ℝ) (t : ℕ) (i : Fin N) :
    ampHistory M J seed s (t+1) (Fin.last (t+1)) i =
      clip M (FCoord (s t)
        (∑ k : Fin r → Fin N, J i k * ∏ a, spinReadout s t (ampHistory M J seed s t) (k a))
        (fun a => ampHistory M J seed s t a i)) := by
  simp only [ampHistory, Fin.snoc_last, ampNext, interaction]

theorem ampHistory_bounded {r N : ℕ} (M : ℝ) (hM : 0 ≤ M)
    (J : Fin N → (Fin r → Fin N) → ℝ) (seed : Fin N → ℝ) (s : ℕ → ℝ) (t : ℕ) :
    ∀ (a : Fin (t+1)) (i : Fin N), ampHistory M J seed s t a i ∈ Set.Icc (-M) M := by
  induction t with
  | zero => intro a i; exact clip_mem M hM (seed i)
  | succ t ih =>
    intro a i
    refine Fin.lastCases ?_ (fun j => ?_) a
    · simpa only [ampHistory, Fin.snoc_last, ampNext] using clip_mem M hM
        (FCoord (s t) (interaction J (spinReadout s t (ampHistory M J seed s t)) i)
          (fun a => ampHistory M J seed s t a i))
    · simpa only [ampHistory, Fin.snoc_castSucc] using ih j i

theorem fCoord_zero (s : ℕ → ℝ) (t : ℕ) : fCoord s t (fun _ => 0)=0 := phi_zero s t

theorem continuous_spinReadout {N : ℕ} (s : ℕ → ℝ) (t : ℕ) : Continuous (spinReadout (N:=N) s t) := by
  apply continuous_pi
  intro i
  exact (continuous_phi s t).comp (continuous_pi (fun a =>
    (continuous_apply i).comp (continuous_apply a.succ)))

theorem continuous_ampNext {r N : ℕ} (M : ℝ) (s : ℕ → ℝ) (t : ℕ) :
    Continuous (fun p : (Fin N → (Fin r → Fin N) → ℝ) × (Fin (t+1) → Fin N → ℝ) =>
      ampNext M p.1 s t p.2) := by
  have hs : Continuous (fun p : (Fin N → (Fin r → Fin N) → ℝ) × (Fin (t+1) → Fin N → ℝ) => spinReadout s t p.2) :=
    (continuous_spinReadout (N:=N) s t).comp continuous_snd
  have hi := (continuous_interaction (r:=r) (N:=N)).comp (continuous_fst.prodMk hs)
  apply continuous_pi
  intro i
  exact (clip_lipschitz M).continuous.comp (((continuous_apply i).comp hi).add
    ((((continuous_apply i).comp ((continuous_apply 0).comp continuous_snd)).mul_const _).mul_const _))

theorem continuous_ampHistory {r N : ℕ} (M : ℝ) (s : ℕ → ℝ) (t : ℕ) :
    Continuous (fun p : (Fin N → (Fin r → Fin N) → ℝ) × (Fin N → ℝ) =>
      ampHistory M p.1 p.2 s t) := by
  induction t with
  | zero =>
    apply continuous_pi
    intro a
    apply continuous_pi
    intro i
    exact (clip_lipschitz M).continuous.comp ((continuous_apply i).comp continuous_snd)
  | succ t ih =>
    exact Continuous.finSnoc (A:=fun _ : Fin (t+2) => Fin N → ℝ) ih
      ((continuous_ampNext M s t).comp (continuous_fst.prodMk ih))

theorem continuous_ampOutput {r N : ℕ} (M : ℝ) (s : ℕ → ℝ) (T : ℕ) :
    Continuous (fun p : (Fin N → (Fin r → Fin N) → ℝ) × (Fin N → ℝ) => ampOutput M p.1 p.2 s T) := by
  apply continuous_pi
  intro i
  exact (clip_lipschitz 1).continuous.comp ((continuous_apply i).comp
    ((continuous_apply (Fin.last T)).comp (continuous_ampHistory M s T)))

end Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Program
