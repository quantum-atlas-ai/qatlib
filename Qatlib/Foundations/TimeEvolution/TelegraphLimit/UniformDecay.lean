/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.TimeEvolution.TelegraphLimit.FourierLimit

/-!
# Uniform exponential decay of telegraph-mode errors

This module absorbs the time factor in the telegraph-to-heat error into a slower exponential
when `a ≥ 2 * b` and `b > 0`. The result `uniform_mode_error` gives a bound with a coefficient
independent of time; `weightedState_norm` bounds the action of uniformly bounded coordinate
weights.

The mathematical background is discussed in [JinLiu2024].

## Main statements

* `time_decay`: absorbs a linear time factor into exponential decay.
* `uniform_mode_error`: gives the telegraph error bound at a slower decay rate.
* `weightedState_norm`: bounds weighted states by a uniform multiplier bound.

## References

* [Jin and Liu, 2024][JinLiu2024]
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Foundations.TimeEvolution.TelegraphLimit

/-- For positive `b`, `a ≥ 2 * b`, and nonnegative time, `t * exp (-a * t) ≤ b⁻¹ * exp (-b *
t)`. -/
theorem time_decay {a b t : ℝ} (hb : 0<b) (ha : 2*b≤a) (ht : 0≤t) :
    t*Real.exp (-a*t)≤b⁻¹*Real.exp (-b*t) := by
  have he := Real.add_one_le_exp (b*t)
  have hp := Real.exp_pos (-b*t)
  have hid : Real.exp (b*t)*Real.exp (-b*t)=1 := by
    rw [← Real.exp_add]
    simp
  have htime : t*Real.exp (-b*t)≤b⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ hb).mpr
    nlinarith [mul_le_mul_of_nonneg_right (show b*t≤Real.exp (b*t) by linarith) hp.le]
  have hcmp : Real.exp (-(a-b)*t)≤Real.exp (-b*t) := Real.exp_le_exp.mpr (by nlinarith)
  have heq : Real.exp (-a*t)=Real.exp (-b*t)*Real.exp (-(a-b)*t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq,← mul_assoc]
  exact (mul_le_mul_of_nonneg_right htime (Real.exp_pos _).le).trans
    (mul_le_mul_of_nonneg_left hcmp (inv_pos.mpr hb).le)

/-- For `2 * b ≤ a ≤ A`, positive `δ` and `b`, nonnegative time, and `4 * δ * a ≤ 3/4`, the
telegraph error is at most `(4 * δ * A + 4 * δ * A ^ 2 / b) * exp (-b * t)`. -/
theorem uniform_mode_error {δ a A b t : ℝ} (hδ : 0<δ) (hb : 0<b)
    (ha : 2*b≤a) (hA : a≤A) (hm : 4*δ*a≤3/4) (ht : 0≤t) :
    |mode δ a t-heatMode a t|≤(4*δ*A+4*δ*A^2/b)*Real.exp (-b*t) := by
  have ha0 : 0≤a := by linarith
  have hA0 : 0≤A := ha0.trans hA
  have he : heatMode a t≤Real.exp (-b*t) := Real.exp_le_exp.mpr (by nlinarith)
  have htime := time_decay hb ha ht
  have hbase := mode_error hδ ha0 hm ht
  have hs : a^2≤A^2 := (sq_le_sq₀ ha0 hA0).mpr hA
  calc
    |mode δ a t-heatMode a t|≤4*δ*a*heatMode a t+4*δ*a^2*(t*Real.exp (-a*t)) := by
      convert hbase using 1
      dsimp [heatMode]
      ring
    _≤4*δ*A*Real.exp (-b*t)+4*δ*A^2*(b⁻¹*Real.exp (-b*t)) := by
      apply add_le_add
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hA (by positivity)) he (Real.exp_pos _).le
          (by positivity)
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hs (by positivity)) htime (by positivity)
          (by positivity)
    _=(4*δ*A+4*δ*A^2/b)*Real.exp (-b*t) := by ring

/-- If every real coordinate weight has absolute value at most a nonnegative `C`, weighting a
finite Euclidean state increases its norm by at most the factor `C`. -/
theorem weightedState_norm {I : Type} [Fintype I] (f : I→ℝ) (x : EuclideanSpace ℂ I)
    {C : ℝ} (hC : 0≤C) (hf : ∀i,|f i|≤C) : ‖weightedState f x‖≤C*‖x‖ := by
  have h := relative_norm (weightedState f x+x) x hC (fun i=>by
    change ‖(f i:ℂ)*x i+x i-x i‖≤C*‖x i‖
    rw [add_sub_cancel_right,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hf i) (norm_nonneg _))
  simpa only [add_sub_cancel_right] using h

end Qatlib.Foundations.TimeEvolution.TelegraphLimit
