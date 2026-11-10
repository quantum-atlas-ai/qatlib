/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.SpinDynamics.Feedback
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
open scoped BigOperators Topology
open Filter
open Qatlib.Papers.OverlapGapGoh26.SpinDynamics.Feedback
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Program
open Qatlib.Foundations.MatrixGeometry.AxisRotations.History
open Qatlib.Foundations.MatrixAlgebra.TensorDiff

namespace Qatlib.Papers.OverlapGapGoh26.SpinDynamics.Clipping

def rawThreshold {r N : ℕ} (J : Fin N → (Fin r → Fin N) → ℝ) (seed : Fin N → ℝ)
    (s : ℕ → ℝ) (T : ℕ) : ℝ :=
  1+∑ t ∈ Finset.range (T+1), ∑ a : Fin (t+1), ∑ i : Fin N, |fieldHistory id J seed s t a i|

theorem rawThreshold_ge_one {r N : ℕ} (J : Fin N → (Fin r → Fin N) → ℝ) (seed : Fin N → ℝ)
    (s : ℕ → ℝ) (T : ℕ) : 1≤rawThreshold J seed s T := by
  unfold rawThreshold
  have hn : 0≤∑ t ∈ Finset.range (T+1), ∑ a : Fin (t+1), ∑ i : Fin N, |fieldHistory id J seed s t a i| :=
    Finset.sum_nonneg (fun t _ => Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun i _ => abs_nonneg _)))
  linarith

theorem raw_entry_bound {r N : ℕ} (J : Fin N → (Fin r → Fin N) → ℝ) (seed : Fin N → ℝ)
    (s : ℕ → ℝ) (T t : ℕ) (ht : t≤T) (a : Fin (t+1)) (i : Fin N) :
    |fieldHistory id J seed s t a i|≤rawThreshold J seed s T := by
  have h1 : |fieldHistory id J seed s t a i|≤∑ j : Fin N, |fieldHistory id J seed s t a j| :=
    Finset.single_le_sum (f:=fun j : Fin N => |fieldHistory id J seed s t a j|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have h2 : (∑ j : Fin N, |fieldHistory id J seed s t a j|)≤
      ∑ b : Fin (t+1), ∑ j : Fin N, |fieldHistory id J seed s t b j| :=
    Finset.single_le_sum (f:=fun b : Fin (t+1) => ∑ j : Fin N, |fieldHistory id J seed s t b j|)
      (fun b _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)) (Finset.mem_univ a)
  have h3 : (∑ b : Fin (t+1), ∑ j : Fin N, |fieldHistory id J seed s t b j|)≤
      ∑ u ∈ Finset.range (T+1), ∑ b : Fin (u+1), ∑ j : Fin N, |fieldHistory id J seed s u b j| :=
    Finset.single_le_sum (f:=fun u : ℕ => ∑ b : Fin (u+1), ∑ j : Fin N, |fieldHistory id J seed s u b j|)
      (fun u _ => Finset.sum_nonneg (fun b _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)))
      (Finset.mem_range.mpr (by omega : t<T+1))
  exact (h1.trans (h2.trans h3)).trans (by unfold rawThreshold; linarith)

theorem clipped_history_exact {r N : ℕ} (J : Fin N → (Fin r → Fin N) → ℝ) (seed : Fin N → ℝ)
    (s : ℕ → ℝ) (T : ℕ) (M : ℝ) (hM : rawThreshold J seed s T≤M) :
    ∀ t≤T, fieldHistory (clip M) J seed s t=fieldHistory id J seed s t := by
  intro t
  induction t with
  | zero =>
    intro _
    funext a i
    change clip M (seed i)=seed i
    apply clip_eq
    exact abs_le.mp ((raw_entry_bound J seed s T 0 (by omega) 0 i).trans hM)
  | succ t ih =>
    intro ht
    simp only [fieldHistory]
    rw [ih (by omega)]
    apply congrArg (fun v : Fin N → ℝ => Fin.snoc (α:=fun _ : Fin (t+2) => Fin N → ℝ)
      (fieldHistory id J seed s t) v)
    funext i
    change clip M (FCoord (s t) (interaction J (spinReadout s t (fieldHistory id J seed s t)) i)
      (fun a => fieldHistory id J seed s t a i))=
      FCoord (s t) (interaction J (spinReadout s t (fieldHistory id J seed s t)) i)
        (fun a => fieldHistory id J seed s t a i)
    apply clip_eq
    apply abs_le.mp
    simpa only [fieldHistory, Fin.snoc_last, historyNext, id_eq] using
      (raw_entry_bound J seed s T (t+1) ht (Fin.last (t+1)) i).trans hM

theorem clipped_feedback_exact {r N : ℕ} (J : Fin N → (Fin r → Fin N) → ℝ) (seed : Fin N → ℝ)
    (s : ℕ → ℝ) (T : ℕ) (M : ℝ) (hM : rawThreshold J seed s T≤M) :
    feedbackState (clip M) J seed s T=feedbackState id J seed s T := by
  rw [feedbackState_eq_product, feedbackState_eq_product,
      clipped_history_exact J seed s T M hM T le_rfl]

theorem clipped_feedback_tendsto_raw {r N : ℕ} (J : Fin N → (Fin r → Fin N) → ℝ) (seed : Fin N → ℝ)
    (s : ℕ → ℝ) (T : ℕ) :
    Tendsto (fun M : ℝ => feedbackState (clip M) J seed s T) atTop (nhds (feedbackState id J seed s T)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (rawThreshold J seed s T)] with M hM
  exact (clipped_feedback_exact J seed s T M hM).symm

end Qatlib.Papers.OverlapGapGoh26.SpinDynamics.Clipping
