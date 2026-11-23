/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ProdFormSpec21.MainResults.SourceModel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Step size and step count for a scalar phase-error budget

These are the scalar budget manipulations in [YiCrosson2022], Corollary 2,
Eqs. (38) and (39). An upper bound on the allowed step size entails a lower
bound on the number of steps for a fixed evolution time.
[Fixed source](https://arxiv.org/abs/2102.12655v1).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Papers.ProdFormSpec21.MainResults

/-- The Eq (38) step-size scale `(1/N) √(ξ/t0) min{1, lam}`. -/
noncomputable def stepSizeScale (N t0 ξ lam : ℝ) : ℝ :=
  (1 / N) * Real.sqrt (ξ / t0) * min 1 lam

/-- The Eq (39) Trotter-step-count scale `N √(t0³/ξ) max{1, 1/lam}`. -/
noncomputable def stepsScale (N t0 ξ lam : ℝ) : ℝ :=
  N * Real.sqrt (t0 ^ 3 / ξ) * max 1 (1 / lam)

/-- Algebraic identity behind Eq (38)–(39): for positive `t0`, `ξ`,
`t0 / √(ξ/t0) = √(t0³/ξ)`. -/
theorem sqrt_div_t0 (t0 ξ : ℝ) (ht0 : 0 < t0) (hξ : 0 < ξ) :
    t0 / Real.sqrt (ξ / t0) = Real.sqrt (t0 ^ 3 / ξ) := by
  have hsqrt_pos : 0 < Real.sqrt (ξ / t0) := Real.sqrt_pos.mpr (by positivity)
  rw [div_eq_iff hsqrt_pos.ne']
  rw [← Real.sqrt_mul (by positivity)]
  have harg : t0 ^ 3 / ξ * (ξ / t0) = t0 ^ 2 := by
    field_simp [ht0.ne', hξ.ne']
  rw [harg, Real.sqrt_sq ht0.le]

/-- Algebraic identity behind Eq (38)–(39): for `lam > 0`,
`1 / min 1 lam = max 1 (1/lam)`. -/
theorem one_div_min (lam : ℝ) (hlam : 0 < lam) :
    1 / min 1 lam = max 1 (1 / lam) := by
  by_cases h : lam ≤ 1
  · have hmax : max 1 (1 / lam) = 1 / lam := by
      apply max_eq_right
      rwa [one_le_div hlam]
    rw [min_eq_right h, hmax]
  · have hlt : 1 < lam := not_le.mp h
    have hmax : max 1 (1 / lam) = 1 := by
      apply max_eq_left
      rw [div_le_one hlam]
      exact hlt.le
    rw [min_eq_left hlt.le, hmax]
    norm_num

/-- Algebraic identity behind Eq (38): for `lam > 0`,
`(min 1 lam)^2 * max 1 (1/lam^2) = 1`. -/
theorem min_sq_mul_max (lam : ℝ) (hlam : 0 < lam) :
    (min 1 lam) ^ 2 * max 1 (1 / lam ^ 2) = 1 := by
  by_cases h : lam ≤ 1
  · have hmin : min 1 lam = lam := min_eq_right h
    have hmax : max 1 (1 / lam ^ 2) = 1 / lam ^ 2 := by
      apply max_eq_right
      rw [one_le_div (by positivity)]
      nlinarith [hlam, h]
    rw [hmin, hmax]
    field_simp
  · have hlt : 1 < lam := not_le.mp h
    have hmin : min 1 lam = 1 := min_eq_left hlt.le
    have hmax : max 1 (1 / lam ^ 2) = 1 := by
      apply max_eq_left
      rw [div_le_one (by positivity)]
      nlinarith [hlam, hlt]
    rw [hmin, hmax]
    norm_num

/-- A nonnegative step satisfying the scalar phase budget lies below the
step-size scale. -/
theorem step_size_le_of_phase_error_budget
    (N t0 ξ lam : ℝ) (hN : 0 < N) (ht0 : 0 < t0) (hξ : 0 < ξ) (hlam : 0 < lam)
    (δt : ℝ) (hδt : 0 ≤ δt)
    (hle : N ^ 2 * δt ^ 2 * max 1 (1 / lam ^ 2) ≤ ξ / t0) :
    δt ≤ stepSizeScale N t0 ξ lam := by
  rw [stepSizeScale]
  have hmax_eq : (min 1 lam) ^ 2 * max 1 (1 / lam ^ 2) = 1 :=
    min_sq_mul_max lam hlam
  have h1 : δt ^ 2 ≤ (ξ / t0) / (N ^ 2 * max 1 (1 / lam ^ 2)) := by
    rw [le_div_iff₀ (by positivity)]
    calc δt ^ 2 * (N ^ 2 * max 1 (1 / lam ^ 2))
        = N ^ 2 * δt ^ 2 * max 1 (1 / lam ^ 2) := by ring
      _ ≤ ξ / t0 := hle
  have hrhs : ((1 / N) * Real.sqrt (ξ / t0) * min 1 lam) ^ 2
      = (ξ / t0) / (N ^ 2 * max 1 (1 / lam ^ 2)) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hξ.le ht0.le)]
    field_simp [hN.ne', hlam.ne']
    simpa only [one_div] using hmax_eq
  have hsq : δt ^ 2 ≤ ((1 / N) * Real.sqrt (ξ / t0) * min 1 lam) ^ 2 := by
    rw [hrhs]
    exact h1
  have hscale_nonneg : 0 ≤ (1 / N) * Real.sqrt (ξ / t0) * min 1 lam := by positivity
  calc δt = Real.sqrt (δt ^ 2) := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hδt]
    _ ≤ Real.sqrt (((1 / N) * Real.sqrt (ξ / t0) * min 1 lam) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = (1 / N) * Real.sqrt (ξ / t0) * min 1 lam := Real.sqrt_sq hscale_nonneg

/-- For a fixed positive evolution time, a positive step below the step-size
scale requires at least the corresponding step-count scale. -/
theorem step_count_ge_of_step_size_budget
    (N t0 ξ lam δt : ℝ) (hN : 0 < N) (ht0 : 0 < t0) (hξ : 0 < ξ) (hlam : 0 < lam)
    (hδt : 0 < δt) (hstep : δt ≤ stepSizeScale N t0 ξ lam) :
    stepsScale N t0 ξ lam ≤ t0 / δt := by
  have hmin_pos : 0 < min 1 lam := lt_min zero_lt_one hlam
  have hps : stepsScale N t0 ξ lam = t0 / stepSizeScale N t0 ξ lam := by
    rw [stepsScale, stepSizeScale]
    rw [show t0 / ((1 / N) * Real.sqrt (ξ / t0) * min 1 lam)
        = N * (t0 / Real.sqrt (ξ / t0)) * (1 / min 1 lam) by
          field_simp [hN.ne', hmin_pos.ne']]
    rw [sqrt_div_t0 t0 ξ ht0 hξ, one_div_min lam hlam]
  calc stepsScale N t0 ξ lam = t0 / stepSizeScale N t0 ξ lam := hps
    _ ≤ t0 / δt := div_le_div_of_nonneg_left ht0.le hδt hstep


end Qatlib.Papers.ProdFormSpec21.MainResults
