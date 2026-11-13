/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ParabolicPDE24.MainResults.InitialLayer
import Qatlib.Papers.ParabolicPDE24.MainResults.Normalization

/-!
# Conditional multimode heat-error budgets

`GoldsteinTaylorMultidim` and `SolvesHeatMultidim` specify the coupled relaxation and heat
systems. Given a decomposition with controlled initial layers and remainder, the module derives
an error budget proportional to the number of modes and transfers it to normalized-state
precision, in the setting of [JinLiu2024].

## Main statements

* `conditional_multimode_budget`: a specified layer-and-remainder decomposition gives a decaying
  quadratic error bound.
* `conditional_multimode_precision`: the conditional estimates yield a target normalized-state
  tolerance.

## References

* [Jin and Liu, 2024][JinLiu2024]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ParabolicPDE24.MainResults

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

/-- The coupled multidirectional Goldstein–Taylor derivative equations for a signal `u` and
fluxes `v`, with directional scales, relaxation parameters, and linear operators. -/
structure GoldsteinTaylorMultidim (k ε : ι → ℝ) (D : ι → E →L[ℝ] E)
    (u : ℝ → E) (v : ι → ℝ → E) : Prop where

  u_deriv : ∀ t, HasDerivAt u (-(∑ j, (1 / ε j) • D j (v j t))) t

  v_deriv : ∀ j t,
    HasDerivAt (v j) (-(1 / ε j) • D j (u t) - (1 / (k j * (ε j) ^ 2)) • v j t) t

/-- The condition that `ũ` has derivative `∑ j, k j • D j (D j (ũ t))` at every time. -/
def SolvesHeatMultidim (k : ι → ℝ) (D : ι → E →L[ℝ] E) (ũ : ℝ → E) : Prop :=
  ∀ t, HasDerivAt ũ (∑ j, k j • D j (D j (ũ t))) t

omit [NormedSpace ℝ E] in

/-- If each vector in a finite family has norm at most `b`, the norm of its sum is at most the
family cardinality times `b`. See [JinLiu2024]. -/
theorem norm_sum_le_card_mul (I : ι → E) (b : ℝ) (hI : ∀ j, ‖I j‖ ≤ b) :
    ‖∑ j, I j‖ ≤ (Fintype.card ι : ℝ) * b := by
  calc ‖∑ j, I j‖ ≤ ∑ j, ‖I j‖ := norm_sum_le Finset.univ I
    _ ≤ ∑ _j : ι, b := Finset.sum_le_sum (fun j _ => hI j)
    _ = (Fintype.card ι : ℝ) * b := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

omit [NormedSpace ℝ E] in

/-- Given the stated initial-layer decomposition and remainder estimates, positivity and
smallness conditions, and logarithmic waiting time, the signal error is at most `card ι * (C
+ k * B) * ε² * exp (−2 * k * t)`. -/
theorem conditional_multimode_budget
    (k ε C B : ℝ) (hk : 0 < k) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsmall : 2 * k ^ 2 * ε ^ 2 ≤ 1 / 2) (_hC : 0 ≤ C) (hB : 0 ≤ B)
    (u ũ : ℝ → E)
    {t : ℝ} (ht : 0 ≤ t) (hthresh : 2 * (ε ^ 2 * k) * Real.log (1 / ε) ≤ t)
    (h_remainder : ∀ t, 0 ≤ t → ∃ (I : ι → E) (r : E),
      u t = ũ t + (∑ j, I j) + r ∧
      (∀ j, ‖I j‖ ≤ ε * k * B * Real.exp (-((t / ε ^ 2)) / k)) ∧
      ‖r‖ ≤ (Fintype.card ι : ℝ) * C * ε ^ 2 * Real.exp (-2 * k * t)) :
    ‖ũ t - u t‖ ≤
      ((Fintype.card ι : ℝ) * C + (Fintype.card ι : ℝ) * k * B) *
        ε ^ 2 * Real.exp (-2 * k * t) := by
  obtain ⟨I, r, hu, hI, hr⟩ := h_remainder t ht
  have hexp_le := exp_neg_div_le_epsilon_mul_exp k ε hε hε1 hk hsmall hthresh
  have hEkB : 0 ≤ ε * k * B := mul_nonneg (mul_nonneg hε.le hk.le) hB
  have hIbound : ∀ j, ‖I j‖ ≤ ε ^ 2 * k * B * Real.exp (-2 * k * t) := by
    intro j
    calc ‖I j‖ ≤ ε * k * B * Real.exp (-((t / ε ^ 2)) / k) := hI j
      _ ≤ ε * k * B * (ε * Real.exp (-2 * k * t)) :=
          mul_le_mul_of_nonneg_left hexp_le hEkB
      _ = ε ^ 2 * k * B * Real.exp (-2 * k * t) := by ring
  have hsum : ‖∑ j, I j‖ ≤
      (Fintype.card ι : ℝ) * (ε ^ 2 * k * B * Real.exp (-2 * k * t)) :=
    norm_sum_le_card_mul I _ hIbound
  have hsub : ũ t - u t = -((∑ j, I j) + r) := by
    rw [hu]
    abel
  rw [hsub, norm_neg]
  calc ‖(∑ j, I j) + r‖ ≤ ‖∑ j, I j‖ + ‖r‖ := norm_add_le _ _
    _ ≤ (Fintype.card ι : ℝ) * (ε ^ 2 * k * B * Real.exp (-2 * k * t)) +
          (Fintype.card ι : ℝ) * C * ε ^ 2 * Real.exp (-2 * k * t) :=
        add_le_add hsum hr
    _ = ((Fintype.card ι : ℝ) * C + (Fintype.card ι : ℝ) * k * B) *
          ε ^ 2 * Real.exp (-2 * k * t) := by ring

/-- For nonzero states with the stated error bound and lower bound on the heat-state norm,
normalization gives error at most `2 * card ι * D * ε²`. -/
theorem conditional_multimode_normalization
    (k ε D : ℝ) (hk : 0 < k) (hε : 0 < ε) (hD : 0 ≤ D)
    (u ũ : ℝ → E) {t : ℝ}
    (h_err : ‖ũ t - u t‖ ≤
      (Fintype.card ι : ℝ) * D * ε ^ 2 * Real.exp (-2 * k * t))
    (h_lower : Real.exp (-2 * k * t) ≤ ‖ũ t‖)
    (hu : u t ≠ 0) (hũ : ũ t ≠ 0) :
    ‖normalizedState (ũ t) - normalizedState (u t)‖ ≤
      2 * ((Fintype.card ι : ℝ) * D) * ε ^ 2 :=
  conditional_normalized_budget k ε ((Fintype.card ι : ℝ) * D) hk hε
    (mul_nonneg (by positivity) hD) u ũ h_err h_lower hu hũ

/-- For a nonempty mode family and the stated conditional error and norm bounds, `ε ≤ sqrt (δ /
(2 * card ι * D))` ensures normalized-state error at most the positive tolerance `δ`. -/
theorem conditional_multimode_precision
    (k ε D δ : ℝ) (hk : 0 < k) (hε : 0 < ε) (hD : 0 < D) (hδ : 0 < δ)
    (hd : (0 : ℝ) < Fintype.card ι)
    (u ũ : ℝ → E) {t : ℝ}
    (h_err : ‖ũ t - u t‖ ≤
      (Fintype.card ι : ℝ) * D * ε ^ 2 * Real.exp (-2 * k * t))
    (h_lower : Real.exp (-2 * k * t) ≤ ‖ũ t‖)
    (hu : u t ≠ 0) (hũ : ũ t ≠ 0)
    (hεδ : ε ≤ Real.sqrt (δ / (2 * ((Fintype.card ι : ℝ) * D)))) :
    ‖normalizedState (ũ t) - normalizedState (u t)‖ ≤ δ :=
  conditional_target_precision k ε ((Fintype.card ι : ℝ) * D) δ hk hε
    (mul_pos hd hD) hδ u ũ h_err h_lower hu hũ hεδ

end Qatlib.Papers.ParabolicPDE24.MainResults
