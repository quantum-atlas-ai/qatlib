/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NonlinearDE20.Resources.Budgets

theorem discretization_error_eq_steps (E2 Δt t : ℝ) (T : ℕ)
    (hT : (T : ℝ) * Δt = t) :
    E2 * (T : ℝ) * Δt ^ 2 = E2 * t * Δt := by
  calc E2 * (T : ℝ) * Δt ^ 2 = E2 * ((T : ℝ) * Δt) * Δt := by ring
    _ = E2 * t * Δt := by rw [hT]

theorem discretization_error_eq_quadratic_over_steps (E2 Δt t : ℝ) (T : ℕ)
    (hT0 : (T : ℝ) ≠ 0) (hT : (T : ℝ) * Δt = t) :
    E2 * (T : ℝ) * Δt ^ 2 = E2 * t ^ 2 / (T : ℝ) := by
  have hdt : Δt = t / (T : ℝ) := by
    field_simp
    linarith [hT]
  rw [hdt]
  field_simp

theorem step_count_budget_suffices (E2 Δt t ε : ℝ) (T : ℕ)
    (hε : 0 < ε) (hT0 : 0 < (T : ℝ)) (hT : (T : ℝ) * Δt = t)
    (hTge : E2 * t ^ 2 / ε ≤ (T : ℝ)) :
    E2 * (T : ℝ) * Δt ^ 2 ≤ ε := by
  rw [discretization_error_eq_quadratic_over_steps E2 Δt t T hT0.ne' hT]
  rw [div_le_iff₀ hT0]
  have h := (div_le_iff₀ hε).mp hTge
  linarith

theorem copy_denominator_budget (E2 Δt t m n ε : ℝ)
    (hε : 0 < ε) (hn : 0 < n) (hnge : E2 * t * Δt * m ^ 2 / ε ≤ n) :
    E2 * t * Δt * m ^ 2 / n ≤ ε := by
  rw [div_le_iff₀ hn]
  have h := (div_le_iff₀ hε).mp hnge
  linarith

theorem eq19_iff_discretization (E2 Δt t ε : ℝ) (T : ℕ)
    (hT : (T : ℝ) * Δt = t) :
    (E2 * t * Δt ≤ ε) ↔ (E2 * (T : ℝ) * Δt ^ 2 ≤ ε) := by
  rw [discretization_error_eq_steps E2 Δt t T hT]

theorem assigned_steps_quadratic (E2 ε t : ℝ) (hE2 : 0 < E2) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ E2 * t ^ 2 / ε = c * t ^ 2 :=
  ⟨E2 / ε, div_pos hE2 hε, by ring⟩

end Qatlib.Papers.NonlinearDE20.Resources.Budgets
