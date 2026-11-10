/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.SpinDynamics.Clipping
import Qatlib.Papers.OverlapGapGoh26.UniformGrid.SpinProbability
import Qatlib.Papers.OverlapGapGoh26.OgpBridge.SpinObstruction
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Program
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Regularity
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Assumption21
open Qatlib.Papers.OverlapGapGoh26.SpinDynamics.Feedback
open Qatlib.Papers.OverlapGapGoh26.SpinDynamics.Clipping

namespace Qatlib.Papers.OverlapGapGoh26.MainResults.ActualMF

def sourceSchedule (T : ℕ) (t : ℕ) : ℝ := (t:ℝ)/(T:ℝ)

theorem source_schedule_range (T : ℕ) (hT : 0<T) (t : ℕ) (ht : t≤T) :
    sourceSchedule T t∈Set.Icc (0:ℝ) 1 := by
  have hp : (0:ℝ)<T := by exact_mod_cast hT
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hp.le
  · apply (div_le_one hp).mpr
    exact_mod_cast ht

theorem source_actual_bounded_contract {r N : ℕ} (M : ℝ) (hM : 1≤M) (J : Fin N → (Fin r → Fin N) → ℝ)
    (seed : Fin N → ℝ) (T : ℕ) (hT : 0<T) :
    (∀ t,fieldHistory (clip M) J seed (sourceSchedule T) t=ampHistory M J seed (sourceSchedule T) t) ∧
    (∀ i,feedbackState (clip M) J seed (sourceSchedule T) T i 2=
      spinOutput M J seed (sourceSchedule T) T i) ∧
    (∀ t a i,ampHistory M J seed (sourceSchedule T) t a i∈Set.Icc (-M) M) ∧
    ∃ K : ℝ,0<K ∧
      (∀ t≤T,fCoord (sourceSchedule T) t (fun _ => 0)=0) ∧
      (∀ t≤T,∀ u v : Fin (t+1) → ℝ,
        |fCoord (sourceSchedule T) t u-fCoord (sourceSchedule T) t v|≤
          K*Real.sqrt (∑ a,(u a-v a)^2)) ∧
      (∀ t≤T,∀ (h h' : ℝ) (u v : Fin (t+1) → ℝ),
        |FCoord (sourceSchedule T t) h u-FCoord (sourceSchedule T t) h' v|≤
          K*Real.sqrt ((h-h')^2+∑ a,(u a-v a)^2)) := by
  exact ⟨clipped_history_eq_amp M J seed (sourceSchedule T),
    bounded_feedback_eq_spinOutput M J seed (sourceSchedule T) T,
    (fun t => ampHistory_bounded M (by linarith) J seed (sourceSchedule T) t),
    actual_assumption21 (sourceSchedule T) T (source_schedule_range T hT)⟩

theorem source_computed_cutoff_readout {r N : ℕ} (J : Fin N → (Fin r → Fin N) → ℝ)
    (seed : Fin N → ℝ) (s : ℕ → ℝ) (T : ℕ) (i : Fin N) :
    spinOutput (rawThreshold J seed s T) J seed s T i=
      feedbackState id J seed s T i 2 := by
  rw [← bounded_feedback_eq_spinOutput (rawThreshold J seed s T) J seed s T i,
    clipped_feedback_exact J seed s T (rawThreshold J seed s T) le_rfl]

end Qatlib.Papers.OverlapGapGoh26.MainResults.ActualMF
