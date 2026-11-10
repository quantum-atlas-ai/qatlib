/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.WalkSpatial08.MainResults.RunCorrectness
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.WalkSpatial08.MainResults

theorem balanced_model_budget :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
      ModelBudgetWithin n (C * sqrtNLatticeLog n) c := by
  obtain ⟨C, hCpos, N₁, hbound⟩ := controlledWalkTimeSteps_bound
  obtain ⟨c, hcpos, N₂, hrun⟩ := balanced_schedule_bound
  refine ⟨C, hCpos, c, hcpos, max N₁ N₂, ?_⟩
  intro n hn
  have h1 : N₁ ≤ n := le_trans (le_max_left N₁ N₂) hn
  have h2 : N₂ ≤ n := le_trans (le_max_right N₁ N₂) hn
  obtain ⟨alg, hsteps, hsucc⟩ := hrun n h2
  refine ⟨alg, ?_, hsucc⟩
  rw [hsteps]
  exact hbound n h1

theorem sqrtNLatticeLog_le_sqrtNLogLattice {n : ℕ} (hlog : 1 ≤ logLattice n) :
    sqrtNLatticeLog n ≤ sqrtNLogLattice n := by
  rw [sqrtNLogLattice_eq_sqrt_log_mul n]
  have h1 : 1 ≤ Real.sqrt (logLattice n) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hlog
  have hS : 0 ≤ sqrtNLatticeLog n := Real.sqrt_nonneg _
  simpa [one_mul] using mul_le_mul_of_nonneg_right h1 hS

theorem balanced_model_old_budget :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
      ModelBudgetWithin n (C * sqrtNLogLattice n) c := by
  obtain ⟨C, hCpos, c, hcpos, N₀, hrun⟩ := balanced_model_budget
  refine ⟨C, hCpos, c, hcpos, max N₀ 16, ?_⟩
  intro n hn
  have hN₀ : N₀ ≤ n := le_trans (le_max_left N₀ 16) hn
  have h16 : 16 ≤ n := le_trans (le_max_right N₀ 16) hn
  obtain ⟨alg, hsteps, hsucc⟩ := hrun n hN₀
  refine ⟨alg, ?_, hsucc⟩
  have hlog : 1 ≤ logLattice n := logLattice_ge_one_of_ge_16 h16
  have himp := sqrtNLatticeLog_le_sqrtNLogLattice hlog
  have hCnonneg : 0 ≤ C := hCpos.le
  have hle : C * sqrtNLatticeLog n ≤ C * sqrtNLogLattice n :=
    mul_le_mul_of_nonneg_left himp hCnonneg
  linarith

end Qatlib.Papers.WalkSpatial08.MainResults
