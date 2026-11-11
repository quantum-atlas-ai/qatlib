/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Qatlib.Papers.Recommender18.MainResults.SourceDefinitions

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 4.1 — closeness in ℓ₂ implies closeness of ℓ₂-sampling laws

Fixed arXiv:1807.04271, Lemma 4.1 (p. 11).  For `x, y ∈ ℝⁿ` with
`‖x − y‖ ≤ ε`, the ℓ₂-sampling distributions satisfy
`‖D_x − D_y‖_TV ≤ 2ε / ‖x‖`.

The proof follows the paper exactly: write `x̂ = x/‖x‖`, `ŷ = y/‖y‖`;
then
`TV = ½ Σ |x̂_i² − ŷ_i²| = ½ Σ |x̂_i−ŷ_i|·|x̂_i+ŷ_i|`
`   ≤ ½ ‖x̂−ŷ‖·‖x̂+ŷ‖ ≤ ‖x̂−ŷ‖ ≤ 2ε/‖x‖`,
using Cauchy–Schwarz, the triangle inequality and `|‖x‖−‖y‖| ≤ ‖x−y‖`.
-/

open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.Recommender18.MainResults.Sampling

noncomputable section

/-- `|a² − b²| = |a − b| · |a + b|`. -/
theorem abs_sq_sub_sq (a b : ℝ) : |a ^ 2 - b ^ 2| = |a - b| * |a + b| := by
  rw [sq_sub_sq, abs_mul, mul_comm]

/-- Fixed arXiv:1807.04271, Lemma 4.1 (p. 11): if `‖x − y‖ ≤ ε` then
`‖D_x − D_y‖_TV ≤ 2ε/‖x‖`.  Both vectors must be nonzero for `D_x`, `D_y`
to be defined (the paper's standing assumption for sampling access). -/
theorem lemma_4_1 {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) (hy : y ≠ 0)
    {ε : ℝ} (h : ‖x - y‖ ≤ ε) :
    tvDist (l2Dist x hx) (l2Dist y hy) ≤ 2 * ε / ‖x‖ := by
  have hS : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hT : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hε : 0 ≤ ε := (norm_nonneg (x - y)).trans h
  set xh : EuclideanSpace ℝ (Fin n) := (‖x‖)⁻¹ • x with hxh_def
  set yh : EuclideanSpace ℝ (Fin n) := (‖y‖)⁻¹ • y with hyh_def
  have hxh : ‖xh‖ = 1 := by
    rw [hxh_def, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hS),
      inv_mul_cancel₀ hS.ne']
  have hyh : ‖yh‖ = 1 := by
    rw [hyh_def, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hT),
      inv_mul_cancel₀ hT.ne']
  have hpx : ∀ i, (l2Dist x hx).prob i = (xh i) ^ 2 := by
    intro i
    rw [l2Dist_prob_normalized]
    simp only [hxh_def, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
  have hpy : ∀ i, (l2Dist y hy).prob i = (yh i) ^ 2 := by
    intro i
    rw [l2Dist_prob_normalized]
    simp only [hyh_def, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
  have htv : tvDist (l2Dist x hx) (l2Dist y hy)
      = (1 / 2) * ∑ i, |xh i - yh i| * |xh i + yh i| := by
    unfold tvDist
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [hpx i, hpy i]
    exact abs_sq_sub_sq (xh i) (yh i)
  have hCS : (∑ i, |xh i - yh i| * |xh i + yh i|) ≤ ‖xh - yh‖ * ‖xh + yh‖ := by
    have hsq := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ)
      (fun i => |xh i - yh i|) (fun i => |xh i + yh i|)
    have hf : (∑ i, |xh i - yh i| ^ 2) = ‖xh - yh‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      apply Finset.sum_congr rfl
      intro i _
      simp [sq_abs]
    have hg : (∑ i, |xh i + yh i| ^ 2) = ‖xh + yh‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      apply Finset.sum_congr rfl
      intro i _
      simp [sq_abs]
    have hnn : 0 ≤ ∑ i, |xh i - yh i| * |xh i + yh i| :=
      Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hsq' : (∑ i, |xh i - yh i| * |xh i + yh i|) ^ 2 ≤ (‖xh - yh‖ * ‖xh + yh‖) ^ 2 := by
      calc (∑ i, |xh i - yh i| * |xh i + yh i|) ^ 2
          ≤ (∑ i, |xh i - yh i| ^ 2) * (∑ i, |xh i + yh i| ^ 2) := hsq
        _ = (‖xh - yh‖ * ‖xh + yh‖) ^ 2 := by rw [hf, hg, mul_pow]
    have habs := sq_le_sq.mp hsq'
    rwa [abs_of_nonneg hnn,
      abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))] at habs
  have hdnorm : ‖xh - yh‖ ≤ 2 * ε / ‖x‖ := by
    have hdecomp : xh - yh = (‖x‖)⁻¹ • (x - y) - ((‖x‖ - ‖y‖) / ‖x‖) • yh := by
      ext i
      simp only [hxh_def, hyh_def, WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
    have hcoef : |(‖x‖ - ‖y‖) / ‖x‖| ≤ ε / ‖x‖ := by
      rw [abs_div, abs_of_pos hS]
      exact div_le_div_of_nonneg_right ((abs_norm_sub_norm_le x y).trans h) hS.le
    calc ‖xh - yh‖
        = ‖(‖x‖)⁻¹ • (x - y) - ((‖x‖ - ‖y‖) / ‖x‖) • yh‖ := by rw [hdecomp]
      _ ≤ ‖(‖x‖)⁻¹ • (x - y)‖ + ‖((‖x‖ - ‖y‖) / ‖x‖) • yh‖ := norm_sub_le _ _
      _ = ‖x‖⁻¹ * ‖x - y‖ + |(‖x‖ - ‖y‖) / ‖x‖| * ‖yh‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hS)]
      _ ≤ ‖x‖⁻¹ * ε + (ε / ‖x‖) * 1 := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left h (by positivity)
          · rw [hyh]
            simpa using hcoef
      _ = 2 * ε / ‖x‖ := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
  have hsnorm : ‖xh + yh‖ ≤ 2 := by
    calc ‖xh + yh‖ ≤ ‖xh‖ + ‖yh‖ := norm_add_le _ _
      _ = 2 := by rw [hxh, hyh]; norm_num
  calc tvDist (l2Dist x hx) (l2Dist y hy)
      = (1 / 2) * ∑ i, |xh i - yh i| * |xh i + yh i| := htv
    _ ≤ (1 / 2) * (‖xh - yh‖ * ‖xh + yh‖) := by
        exact mul_le_mul_of_nonneg_left hCS (by norm_num)
    _ ≤ (1 / 2) * ((2 * ε / ‖x‖) * 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul hdnorm hsnorm (norm_nonneg _)
          (div_nonneg (by linarith) hS.le)
    _ = 2 * ε / ‖x‖ := by
        field_simp

end

end Qatlib.Papers.Recommender18.MainResults.Sampling
