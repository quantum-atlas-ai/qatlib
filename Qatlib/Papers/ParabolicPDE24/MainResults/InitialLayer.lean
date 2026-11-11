/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

/-!
# Initial-layer correctors for relaxation

`GoldsteinTaylor` and `SolvesHeat` specify the one-direction relaxation and heat equations. The
explicit exponentially decaying `initialLayerCorrector` becomes quadratically small after a
logarithmic waiting time; an assumed remainder decomposition then gives the conditional
heat-error bound used for [JinLiu2024].

## Main statements

* `initialLayerCorrector_norm_le_exp_neg_two`: the rescaled layer is bounded by a decaying
  multiple of `ε²`.
* `conditional_corrector_bound`: a remainder assumption yields a full signal error estimate.

## References

* [Jin and Liu, 2024][JinLiu2024]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ParabolicPDE24.MainResults

open scoped Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The coupled Goldstein–Taylor derivative equations for signal `u` and flux `v` with linear
operator `D`, scale `ε`, and relaxation parameter `k`. -/
structure GoldsteinTaylor (k ε : ℝ) (D : E →L[ℝ] E) (u v : ℝ → E) : Prop where

  u_deriv : ∀ t, HasDerivAt u (-(1 / ε) • D (v t)) t

  v_deriv : ∀ t, HasDerivAt v (-(1 / ε) • D (u t) - (1 / (k * ε ^ 2)) • v t) t

/-- The condition that `ũ` has derivative `k • D (D (ũ t))` at every real time. -/
def SolvesHeat (k : ℝ) (D : E →L[ℝ] E) (ũ : ℝ → E) : Prop :=
  ∀ t, HasDerivAt ũ (k • D (D (ũ t))) t

/-- The initial-layer corrector `(ε * k * exp (−τ / k)) • v0`. -/
def initialLayerCorrector (k ε : ℝ) (v0 : E) (τ : ℝ) : E :=
  (ε * k * Real.exp (-τ / k)) • v0

/-- For nonzero `k`, the initial-layer corrector has derivative `−(1 / k)` times itself with
respect to the fast time. See [JinLiu2024]. -/
theorem initialLayerCorrector_hasDerivAt (k ε : ℝ) (_hk : k ≠ 0) (v0 : E) (τ : ℝ) :
    HasDerivAt (initialLayerCorrector k ε v0)
      ((-(1 / k)) • initialLayerCorrector k ε v0 τ) τ := by
  have harg : HasDerivAt (fun s : ℝ => -s / k) (-1 / k) τ := by
    have h := (hasDerivAt_id τ).neg.div_const k
    simpa only [id_eq] using! h
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-s / k))
      (Real.exp (-τ / k) * (-1 / k)) τ := by
    have h := (Real.hasDerivAt_exp (-τ / k)).comp τ harg
    simpa [mul_comm] using! h
  have h := hexp.const_mul (ε * k)
  have h2 : HasDerivAt (fun s : ℝ => (ε * k * Real.exp (-s / k)) • v0)
      (((ε * k) * (Real.exp (-τ / k) * (-1 / k))) • v0) τ := h.smul_const v0
  have hder : ((-(1 / k)) • initialLayerCorrector k ε v0 τ) =
      (((ε * k) * (Real.exp (-τ / k) * (-1 / k))) • v0) := by
    rw [initialLayerCorrector, smul_smul]
    congr 1
    ring
  rw [hder]
  exact h2

/-- The corrector norm equals `|ε * k| * exp (−τ / k) * ‖v0‖`. -/
theorem norm_initialLayerCorrector (k ε : ℝ) (v0 : E) (τ : ℝ) :
    ‖initialLayerCorrector k ε v0 τ‖ =
      |ε * k| * Real.exp (-τ / k) * ‖v0‖ := by
  rw [initialLayerCorrector, norm_smul, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_pos (Real.exp_pos _)]

/-- For nonnegative `ε` and `k`, the corrector norm equals `ε * k * exp (−τ / k) * ‖v0‖`. -/
theorem norm_initialLayerCorrector_of_nonneg (k ε : ℝ) (hε : 0 ≤ ε) (hk : 0 ≤ k)
    (v0 : E) (τ : ℝ) :
    ‖initialLayerCorrector k ε v0 τ‖ =
      ε * k * Real.exp (-τ / k) * ‖v0‖ := by
  rw [norm_initialLayerCorrector, abs_of_nonneg (mul_nonneg hε hk)]

/-- For positive `ε` and `k`, the corrector norm is at most `ε² * k * ‖v0‖` once `τ ≥ k * log (1
/ ε)`. -/
theorem initialLayerCorrector_norm_le_sq (k ε : ℝ) (hε : 0 < ε) (hk : 0 < k)
    (v0 : E) {τ : ℝ} (hτ : k * Real.log (1 / ε) ≤ τ) :
    ‖initialLayerCorrector k ε v0 τ‖ ≤ ε ^ 2 * k * ‖v0‖ := by
  rw [norm_initialLayerCorrector_of_nonneg k ε hε.le hk.le]
  have hτk : Real.log (1 / ε) ≤ τ / k := by
    rw [le_div_iff₀ hk]
    simpa [mul_comm] using hτ
  have hexp_le : Real.exp (-τ / k) ≤ ε := by
    have hpos : 0 < Real.exp (τ / k) := Real.exp_pos _
    have hεinv : ε⁻¹ = Real.exp (Real.log (1 / ε)) := by
      rw [← one_div]
      exact (Real.exp_log (by positivity : (0 : ℝ) < 1 / ε)).symm
    have h1 : (Real.exp (τ / k))⁻¹ ≤ ε := by
      rw [inv_le_comm₀ hpos hε, hεinv]
      exact Real.exp_le_exp.mpr hτk
    simpa only [neg_div, Real.exp_neg] using h1
  have hmul : ε * k * Real.exp (-τ / k) ≤ ε * k * ε :=
    mul_le_mul_of_nonneg_left hexp_le (mul_nonneg hε.le hk.le)
  calc ε * k * Real.exp (-τ / k) * ‖v0‖ ≤ ε * k * ε * ‖v0‖ :=
        mul_le_mul_of_nonneg_right hmul (norm_nonneg _)
    _ = ε ^ 2 * k * ‖v0‖ := by ring

/-- For `0 < ε ≤ 1`, positive `k`, and the stated smallness condition, the logarithmic
waiting-time bound implies `exp (−t / (k * ε²)) ≤ ε * exp (−2 * k * t)`. -/
theorem exp_neg_div_le_epsilon_mul_exp (k ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hk : 0 < k) (hsmall : 2 * k ^ 2 * ε ^ 2 ≤ 1 / 2) {t : ℝ}
    (ht : 2 * (ε ^ 2 * k) * Real.log (1 / ε) ≤ t) :
    Real.exp (-((t / ε ^ 2)) / k) ≤ ε * Real.exp (-2 * k * t) := by
  have hlog : Real.log ε = -Real.log (1 / ε) := by
    rw [one_div, Real.log_inv]
    ring
  have ht0 : 0 ≤ t := by
    have hlog1 : 0 ≤ Real.log (1 / ε) := by
      apply Real.log_nonneg
      simpa only [one_div] using (one_le_div hε).mpr hε1
    have hprod : 0 ≤ 2 * (ε ^ 2 * k) * Real.log (1 / ε) :=
      mul_nonneg (by positivity) hlog1
    linarith [ht, hprod]
  conv_rhs => rw [← Real.exp_log hε, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hA : (0 : ℝ) < ε ^ 2 * k := by positivity
  have hmul1 : 2 * k ^ 2 * ε ^ 2 * t ≤ 1 / 2 * t :=
    mul_le_mul_of_nonneg_right hsmall ht0
  have hmul2 : ε ^ 2 * k * Real.log (1 / ε) ≤ t / 2 := by linarith
  have hbound : (2 * k * t + Real.log (1 / ε)) * (ε ^ 2 * k) ≤ t := by
    nlinarith [hmul1, hmul2]
  have hdiv : 2 * k * t + Real.log (1 / ε) ≤ (t / ε ^ 2) / k := by
    rw [show (t / ε ^ 2) / k = t / (ε ^ 2 * k) by ring, le_div_iff₀ hA]
    exact hbound
  rw [hlog]
  calc -((t / ε ^ 2)) / k = -(t / ε ^ 2 / k) := by ring
    _ ≤ -(2 * k * t + Real.log (1 / ε)) := neg_le_neg hdiv
    _ = -Real.log (1 / ε) + -2 * k * t := by ring

/-- Under the stated positivity, smallness, and waiting-time assumptions, the corrector at fast
time `t / ε²` has norm at most `ε² * k * ‖v0‖ * exp (−2 * k * t)`. See [JinLiu2024]. -/
theorem initialLayerCorrector_norm_le_exp_neg_two (k ε : ℝ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hk : 0 < k) (hsmall : 2 * k ^ 2 * ε ^ 2 ≤ 1 / 2)
    (v0 : E) {t : ℝ} (ht : 2 * (ε ^ 2 * k) * Real.log (1 / ε) ≤ t) :
    ‖initialLayerCorrector k ε v0 (t / ε ^ 2)‖ ≤
      ε ^ 2 * k * ‖v0‖ * Real.exp (-2 * k * t) := by
  rw [norm_initialLayerCorrector_of_nonneg k ε hε.le hk.le]
  have hexp_le := exp_neg_div_le_epsilon_mul_exp k ε hε hε1 hk hsmall ht
  have hmul : ε * k * Real.exp (-((t / ε ^ 2)) / k) ≤
      ε ^ 2 * k * Real.exp (-2 * k * t) := by
    have hEk : 0 ≤ ε * k := mul_nonneg hε.le hk.le
    calc ε * k * Real.exp (-((t / ε ^ 2)) / k)
        ≤ ε * k * (ε * Real.exp (-2 * k * t)) :=
          mul_le_mul_of_nonneg_left hexp_le hEk
      _ = ε ^ 2 * k * Real.exp (-2 * k * t) := by ring
  calc ε * k * Real.exp (-((t / ε ^ 2)) / k) * ‖v0‖
      ≤ ε ^ 2 * k * Real.exp (-2 * k * t) * ‖v0‖ :=
        mul_le_mul_of_nonneg_right hmul (norm_nonneg _)
    _ = ε ^ 2 * k * ‖v0‖ * Real.exp (-2 * k * t) := by ring

/-- Given the stated corrector-plus-remainder decomposition, parameter conditions, and waiting
time, the signal error is at most `(C + k * ‖D (v 0)‖) * ε² * exp (−2 * k * t)`. -/
theorem conditional_corrector_bound
    (k ε C : ℝ) (hk : 0 < k) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsmall : 2 * k ^ 2 * ε ^ 2 ≤ 1 / 2) (_hC : 0 ≤ C)
    (D : E →L[ℝ] E) (u v ũ : ℝ → E)
    (h_remainder : ∀ t, 0 ≤ t → ∃ r : E,
      u t = ũ t + initialLayerCorrector k ε (D (v 0)) (t / ε ^ 2) + r ∧
      ‖r‖ ≤ C * ε ^ 2 * Real.exp (-2 * k * t))
    {t : ℝ} (ht : 0 ≤ t) (hthresh : 2 * (ε ^ 2 * k) * Real.log (1 / ε) ≤ t) :
    ‖ũ t - u t‖ ≤ (C + k * ‖D (v 0)‖) * ε ^ 2 * Real.exp (-2 * k * t) := by
  obtain ⟨r, hr, hrb⟩ := h_remainder t ht
  have hlayer :=
    initialLayerCorrector_norm_le_exp_neg_two k ε hε hε1 hk hsmall (D (v 0)) hthresh
  have hsub : ũ t - u t = -(initialLayerCorrector k ε (D (v 0)) (t / ε ^ 2) + r) := by
    rw [hr]
    abel
  rw [hsub, norm_neg]
  calc ‖initialLayerCorrector k ε (D (v 0)) (t / ε ^ 2) + r‖
      ≤ ‖initialLayerCorrector k ε (D (v 0)) (t / ε ^ 2)‖ + ‖r‖ := norm_add_le _ _
    _ ≤ ε ^ 2 * k * ‖D (v 0)‖ * Real.exp (-2 * k * t) +
          C * ε ^ 2 * Real.exp (-2 * k * t) := add_le_add hlayer hrb
    _ = (C + k * ‖D (v 0)‖) * ε ^ 2 * Real.exp (-2 * k * t) := by ring

end Qatlib.Papers.ParabolicPDE24.MainResults
