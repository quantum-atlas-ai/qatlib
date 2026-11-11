/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BayesianPDEAn26.LossBounds.LossDefinitions

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 4.2 — deterministic error bound for the physical loss

Fixed source: arXiv:2608.27028v1, Lemma 4.2, pp.13–14, Eq. (4.1).

Statement. With `‖u_T − ũ_T‖ ≤ ε_app`,

`|L_phys − L̃_phys| ≤ 2‖u_T − u_obs‖ ε_app + ε_app²`,

and if the closeness condition `‖u_T − u_obs‖ ≤ δ‖u_obs‖` (with `0 < δ < 1`) holds
then `|L_phys − L̃_phys| ≤ 2δ‖u_obs‖ ε_app + ε_app²`  (Eq. (4.1)).

Proof route (source p.14). Reverse triangle gives
`|‖u_T − u_obs‖ − ‖ũ_T − u_obs‖| ≤ ‖u_T − ũ_T‖ ≤ ε_app`, triangle gives
`‖ũ_T − u_obs‖ ≤ ‖u_T − u_obs‖ + ε_app`, and then
`|a² − b²| = |a − b|(a + b) ≤ ε_app (2a + ε_app)`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BayesianPDEAn26.LossBounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Lemma 4.2** (arXiv:2608.27028v1, pp.13–14). Deterministic error of the
physical loss from the forward-solver error `‖u_T − ũ_T‖ ≤ ε_app`. -/
theorem physicalLoss_error_bound
    (uObs uT uTtilde : E) (εapp : ℝ)
    (happ : ‖uT - uTtilde‖ ≤ εapp) (hε0 : 0 ≤ εapp) :
    |physicalLoss uObs uT - physicalLoss uObs uTtilde| ≤
      2 * ‖uT - uObs‖ * εapp + εapp ^ 2 := by
  set a : ℝ := ‖uT - uObs‖ with ha_def
  set b : ℝ := ‖uTtilde - uObs‖ with hb_def
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  -- Reverse triangle on the shifted differences.
  have hdiff : |a - b| ≤ εapp := by
    have h := abs_norm_sub_norm_le (uT - uObs) (uTtilde - uObs)
    have hsub : (uT - uObs) - (uTtilde - uObs) = uT - uTtilde := by abel
    rw [hsub] at h
    calc |a - b| = |‖uT - uObs‖ - ‖uTtilde - uObs‖| := by rw [ha_def, hb_def]
      _ ≤ ‖uT - uTtilde‖ := h
      _ ≤ εapp := happ
  have hb_le : b ≤ a + εapp := by
    have := (abs_sub_le_iff.mp hdiff).2
    linarith
  have hfactor : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  have hab : 0 ≤ a + b := by linarith
  calc |physicalLoss uObs uT - physicalLoss uObs uTtilde|
      = |a ^ 2 - b ^ 2| := by simp [physicalLoss, ha_def, hb_def]
    _ = |a - b| * (a + b) := by rw [hfactor, abs_mul, abs_of_nonneg hab]
    _ ≤ εapp * (a + b) := by
        exact mul_le_mul_of_nonneg_right hdiff hab
    _ ≤ εapp * (2 * a + εapp) := by
        have hsum : a + b ≤ 2 * a + εapp := by linarith
        exact mul_le_mul_of_nonneg_left hsum hε0
    _ = 2 * ‖uT - uObs‖ * εapp + εapp ^ 2 := by
        rw [← ha_def]
        ring

/-- **Lemma 4.2, Eq. (4.1)** (arXiv:2608.27028v1, p.14). The closeness variant of
the physical-loss error bound. -/
theorem physicalLoss_error_bound_of_close
    (uObs uT uTtilde : E) (εapp δ : ℝ)
    (happ : ‖uT - uTtilde‖ ≤ εapp)
    (hclose : ‖uT - uObs‖ ≤ δ * ‖uObs‖)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hε0 : 0 ≤ εapp) :
    |physicalLoss uObs uT - physicalLoss uObs uTtilde| ≤
      2 * δ * ‖uObs‖ * εapp + εapp ^ 2 := by
  have hmain := physicalLoss_error_bound uObs uT uTtilde εapp happ hε0
  have hmono : 2 * ‖uT - uObs‖ * εapp ≤ 2 * (δ * ‖uObs‖) * εapp := by
    gcongr
  nlinarith

end Qatlib.Papers.BayesianPDEAn26.LossBounds
