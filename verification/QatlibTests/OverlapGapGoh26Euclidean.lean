module

import Qatlib.Papers.OverlapGapGoh26.AmpDynamics.EuclideanRegularity
import Qatlib.Papers.OverlapGapGoh26.MainResults.ActualMFContract

/-! Regression tests for the actual AMP coordinates on the source schedule. -/

open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Program
open Qatlib.Papers.OverlapGapGoh26.MainResults.ActualMF
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics

example : ‖ampUpdateOperator (sourceSchedule 3 2) 2‖ =
    Real.sqrt (1 + (4 / 27 : ℝ) ^ 2) := by
  rw [ampUpdateOperator_norm]
  norm_num [sourceSchedule]

example (u v : EuclideanSpace ℝ (Fin 3)) (x y : EuclideanSpace ℝ (Fin 4)) :
    fCoord (sourceSchedule 3) 2 (fun _ => 0) = 0 ∧
    |fCoord (sourceSchedule 3) 2 u.ofLp - fCoord (sourceSchedule 3) 2 v.ofLp| ≤
      max (2 * Real.sqrt 3) (Real.sqrt (1 + (4 / 27 : ℝ) ^ 2)) * ‖u - v‖ ∧
    |FCoord (sourceSchedule 3 2) (x 0) (fun i => x i.succ) -
      FCoord (sourceSchedule 3 2) (y 0) (fun i => y i.succ)| ≤
        max (2 * Real.sqrt 3) (Real.sqrt (1 + (4 / 27 : ℝ) ^ 2)) * ‖x - y‖ := by
  obtain ⟨_, h⟩ := euclidean_assumption21 (sourceSchedule 3) 3
    (source_schedule_range 3 (by decide))
  obtain ⟨hzero, hf, hF⟩ := h 2 (by decide)
  exact ⟨hzero, hf u v, hF x y⟩
