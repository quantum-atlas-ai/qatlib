/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BayesianPDEAn26.LossBounds.LossDefinitions

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 4.1 — deterministic error bound for the normalized loss

Fixed source: arXiv:2608.27028v1, Lemma 4.1, p.13.

Statement. For a nonzero observation `u_obs`, a nonzero exact terminal solution
`u_T(m)` and a nonzero approximation `ũ_T(m)` with `‖u_T − ũ_T‖ ≤ ε_app`, and
under the closeness condition `‖u_T − u_obs‖ ≤ δ‖u_obs‖` with `0 < δ < 1`, the
normalized losses of Eq. (3.6) satisfy

`|L_norm − L̃_norm| ≤ 4 ε_app / ((1 − δ)‖u_obs‖)`.

Proof route (source pp.13–14). Reverse triangle gives
`‖u_T‖ ≥ (1 − δ)‖u_obs‖`; then
`‖û_T − û̃_T‖ ≤ ‖u_T − ũ_T‖/‖u_T‖ + |‖ũ_T‖ − ‖u_T‖|/‖u_T‖ ≤ 2ε_app/‖u_T‖`;
finally Cauchy–Schwarz on the unit vectors gives the factor `2` and the claim.
-/

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace RealInnerProductSpace

namespace Qatlib.Papers.BayesianPDEAn26.LossBounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Lemma 4.1** (arXiv:2608.27028v1, p.13). Deterministic error of the
normalized loss under the closeness condition `‖u_T − u_obs‖ ≤ δ‖u_obs‖`,
`0 < δ < 1`, and the solver error `‖u_T − ũ_T‖ ≤ ε_app`. -/
theorem normalizedLoss_error_bound
    (uObs uT uTtilde : E) (εapp δ : ℝ)
    (hObs : uObs ≠ 0) (hT : uT ≠ 0) (hTtilde : uTtilde ≠ 0)
    (happ : ‖uT - uTtilde‖ ≤ εapp)
    (hclose : ‖uT - uObs‖ ≤ δ * ‖uObs‖)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hε0 : 0 ≤ εapp) :
    |normalizedLoss uObs uT - normalizedLoss uObs uTtilde| ≤
      4 * εapp / ((1 - δ) * ‖uObs‖) := by
  have hObsPos : 0 < ‖uObs‖ := norm_pos_iff.mpr hObs
  have hTPos : 0 < ‖uT‖ := norm_pos_iff.mpr hT
  have hTtildePos : 0 < ‖uTtilde‖ := norm_pos_iff.mpr hTtilde
  -- Denominators are positive.
  have hdenPos : 0 < (1 - δ) * ‖uObs‖ := by nlinarith
  -- Reverse triangle: `(1 − δ)‖u_obs‖ ≤ ‖u_T‖`.
  have hTnorm : (1 - δ) * ‖uObs‖ ≤ ‖uT‖ := by
    have h1 : ‖uObs‖ ≤ ‖uObs - uT‖ + ‖uT‖ := by
      have := norm_add_le (uObs - uT) uT
      simpa using this
    have h2 : ‖uObs - uT‖ = ‖uT - uObs‖ := norm_sub_rev _ _
    nlinarith
  -- Difference of normalized vectors.
  have hnormdiff : ‖unitVec uT - unitVec uTtilde‖ ≤
      2 * εapp / ((1 - δ) * ‖uObs‖) := by
    have hdecomp : unitVec uT - unitVec uTtilde =
        (‖uT‖⁻¹ : ℝ) • (uT - uTtilde) +
          ((‖uT‖⁻¹ : ℝ) - (‖uTtilde‖⁻¹ : ℝ)) • uTtilde := by
      simp only [unitVec]
      module
    have hstep1 : ‖unitVec uT - unitVec uTtilde‖ ≤
        ‖(‖uT‖⁻¹ : ℝ) • (uT - uTtilde)‖ +
          ‖((‖uT‖⁻¹ : ℝ) - (‖uTtilde‖⁻¹ : ℝ)) • uTtilde‖ := by
      rw [hdecomp]
      exact norm_add_le _ _
    have hfirst : ‖(‖uT‖⁻¹ : ℝ) • (uT - uTtilde)‖ =
        ‖uT‖⁻¹ * ‖uT - uTtilde‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hTPos)]
    have hsecond : ‖((‖uT‖⁻¹ : ℝ) - (‖uTtilde‖⁻¹ : ℝ)) • uTtilde‖ =
        |(‖uT‖⁻¹ : ℝ) - (‖uTtilde‖⁻¹ : ℝ)| * ‖uTtilde‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    -- The reciprocal difference collapses to `|‖u_T‖ − ‖ũ_T‖| / ‖u_T‖`.
    have hkey : |(‖uT‖⁻¹ : ℝ) - (‖uTtilde‖⁻¹ : ℝ)| * ‖uTtilde‖ =
        ‖uT‖⁻¹ * |‖uT‖ - ‖uTtilde‖| := by
      rw [inv_sub_inv (ne_of_gt hTPos) (ne_of_gt hTtildePos)]
      rw [abs_div, abs_mul, abs_of_pos hTPos, abs_of_pos hTtildePos]
      rw [abs_sub_comm (‖uTtilde‖ : ℝ) (‖uT‖ : ℝ)]
      field_simp
    have hnormclose : |‖uT‖ - ‖uTtilde‖| ≤ εapp := by
      have h := abs_norm_sub_norm_le uT uTtilde
      have h' : ‖uT - uTtilde‖ ≤ εapp := happ
      linarith
    have hsecondBound : ‖uT‖⁻¹ * |‖uT‖ - ‖uTtilde‖| ≤ ‖uT‖⁻¹ * εapp :=
      mul_le_mul_of_nonneg_left hnormclose (inv_nonneg.mpr hTPos.le)
    have hfirstBound : ‖uT‖⁻¹ * ‖uT - uTtilde‖ ≤ ‖uT‖⁻¹ * εapp :=
      mul_le_mul_of_nonneg_left happ (inv_nonneg.mpr hTPos.le)
    have htotal : ‖unitVec uT - unitVec uTtilde‖ ≤
        ‖uT‖⁻¹ * εapp + ‖uT‖⁻¹ * εapp := by
      calc ‖unitVec uT - unitVec uTtilde‖
          ≤ ‖(‖uT‖⁻¹ : ℝ) • (uT - uTtilde)‖ +
              ‖((‖uT‖⁻¹ : ℝ) - (‖uTtilde‖⁻¹ : ℝ)) • uTtilde‖ := hstep1
        _ = ‖uT‖⁻¹ * ‖uT - uTtilde‖ +
              |(‖uT‖⁻¹ : ℝ) - (‖uTtilde‖⁻¹ : ℝ)| * ‖uTtilde‖ := by
              rw [hfirst, hsecond]
        _ = ‖uT‖⁻¹ * ‖uT - uTtilde‖ + ‖uT‖⁻¹ * |‖uT‖ - ‖uTtilde‖| := by
              rw [hkey]
        _ ≤ ‖uT‖⁻¹ * εapp + ‖uT‖⁻¹ * εapp := by linarith
    have hcombine : ‖uT‖⁻¹ * εapp + ‖uT‖⁻¹ * εapp = 2 * εapp / ‖uT‖ := by
      field_simp
      ring
    calc ‖unitVec uT - unitVec uTtilde‖
        ≤ ‖uT‖⁻¹ * εapp + ‖uT‖⁻¹ * εapp := htotal
      _ = 2 * εapp / ‖uT‖ := hcombine
      _ ≤ 2 * εapp / ((1 - δ) * ‖uObs‖) := by
          exact div_le_div_of_nonneg_left (by positivity) hdenPos hTnorm
  -- Rewrite the loss difference and apply Cauchy–Schwarz.
  have hlossdiff : normalizedLoss uObs uT - normalizedLoss uObs uTtilde =
      -2 * ⟪unitVec uObs, unitVec uT - unitVec uTtilde⟫_ℝ := by
    unfold normalizedLoss
    rw [inner_sub_right]
    ring
  have hcs : |⟪unitVec uObs, unitVec uT - unitVec uTtilde⟫_ℝ| ≤
      ‖unitVec uObs‖ * ‖unitVec uT - unitVec uTtilde‖ := by
    simpa [Real.norm_eq_abs] using
      norm_inner_le_norm (𝕜 := ℝ) (unitVec uObs) (unitVec uT - unitVec uTtilde)
  have hobsUnit : ‖unitVec uObs‖ = 1 := norm_unitVec hObs
  have hfinal : |normalizedLoss uObs uT - normalizedLoss uObs uTtilde| ≤
      2 * ‖unitVec uT - unitVec uTtilde‖ := by
    rw [hlossdiff, abs_mul]
    norm_num
    have h := mul_le_mul_of_nonneg_left hcs (by norm_num : (0 : ℝ) ≤ 2)
    simpa [hobsUnit] using h
  calc |normalizedLoss uObs uT - normalizedLoss uObs uTtilde|
      ≤ 2 * ‖unitVec uT - unitVec uTtilde‖ := hfinal
    _ ≤ 2 * (2 * εapp / ((1 - δ) * ‖uObs‖)) := by linarith
    _ = 4 * εapp / ((1 - δ) * ‖uObs‖) := by
        field_simp
        ring

end Qatlib.Papers.BayesianPDEAn26.LossBounds
