/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic

/-!
# Scalar step and copy budget estimates

Assuming `T * Δt = t`, this module rewrites the accumulated Euler scale as both `E2 * t * Δt`
and `E2 * t^2 / T`. It proves sufficient scalar step and copy denominator budgets and isolates a
positive quadratic-time coefficient, matching the parameter bookkeeping of [LloydEtAl2020].

## Main statements

* `discretization_error_eq_quadratic_over_steps`: For nonzero `T` and `T * Δt = t`, the
  accumulated scale equals `E2 * t^2 / T`.
* `step_count_budget_suffices`: If the positive step count is at least `E2 * t^2 / ε` and spans
  time `t`, the accumulated scale is at most the positive tolerance `ε`.
* `copy_denominator_budget`: A positive copy denominator at least `E2 * t * Δt * m^2 / ε` makes
  the corresponding ratio at most the positive tolerance `ε`.

## References

* [Lloyd et al., 2020][LloydEtAl2020]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NonlinearDE20.Resources.Budgets

/-- When `T * Δt = t`, the accumulated scale `E2 * T * Δt^2` equals `E2 * t * Δt`. -/
theorem discretization_error_eq_steps (E2 Δt t : ℝ) (T : ℕ)
    (hT : (T : ℝ) * Δt = t) :
    E2 * (T : ℝ) * Δt ^ 2 = E2 * t * Δt := by
  calc E2 * (T : ℝ) * Δt ^ 2 = E2 * ((T : ℝ) * Δt) * Δt := by ring
    _ = E2 * t * Δt := by rw [hT]

/-- For nonzero `T` and `T * Δt = t`, the accumulated scale equals `E2 * t^2 / T`
[LloydEtAl2020]. -/
theorem discretization_error_eq_quadratic_over_steps (E2 Δt t : ℝ) (T : ℕ)
    (hT0 : (T : ℝ) ≠ 0) (hT : (T : ℝ) * Δt = t) :
    E2 * (T : ℝ) * Δt ^ 2 = E2 * t ^ 2 / (T : ℝ) := by
  have hdt : Δt = t / (T : ℝ) := by
    field_simp
    linarith [hT]
  rw [hdt]
  field_simp

/-- If the positive step count is at least `E2 * t^2 / ε` and spans time `t`, the accumulated
scale is at most the positive tolerance `ε` [LloydEtAl2020]. -/
theorem step_count_budget_suffices (E2 Δt t ε : ℝ) (T : ℕ)
    (hε : 0 < ε) (hT0 : 0 < (T : ℝ)) (hT : (T : ℝ) * Δt = t)
    (hTge : E2 * t ^ 2 / ε ≤ (T : ℝ)) :
    E2 * (T : ℝ) * Δt ^ 2 ≤ ε := by
  rw [discretization_error_eq_quadratic_over_steps E2 Δt t T hT0.ne' hT]
  rw [div_le_iff₀ hT0]
  have h := (div_le_iff₀ hε).mp hTge
  linarith

/-- A positive copy denominator at least `E2 * t * Δt * m^2 / ε` makes the corresponding ratio
at most the positive tolerance `ε` [LloydEtAl2020]. -/
theorem copy_denominator_budget (E2 Δt t m n ε : ℝ)
    (hε : 0 < ε) (hn : 0 < n) (hnge : E2 * t * Δt * m ^ 2 / ε ≤ n) :
    E2 * t * Δt * m ^ 2 / n ≤ ε := by
  rw [div_le_iff₀ hn]
  have h := (div_le_iff₀ hε).mp hnge
  linarith

/-- Under `T * Δt = t`, the time-step and accumulated-step forms of the tolerance inequality are
equivalent. -/
theorem eq19_iff_discretization (E2 Δt t ε : ℝ) (T : ℕ)
    (hT : (T : ℝ) * Δt = t) :
    (E2 * t * Δt ≤ ε) ↔ (E2 * (T : ℝ) * Δt ^ 2 ≤ ε) := by
  rw [discretization_error_eq_steps E2 Δt t T hT]

/-- For positive `E2` and `ε`, the assigned step expression is a positive constant times `t^2`. -/
theorem assigned_steps_quadratic (E2 ε t : ℝ) (hE2 : 0 < E2) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ E2 * t ^ 2 / ε = c * t ^ 2 :=
  ⟨E2 / ε, div_pos hE2 hε, by ring⟩

end Qatlib.Papers.NonlinearDE20.Resources.Budgets
