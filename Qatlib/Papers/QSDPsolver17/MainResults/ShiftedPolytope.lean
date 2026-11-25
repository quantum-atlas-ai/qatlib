/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QSDPsolver17.MainResults.PaperInterface.PaperDefs

@[expose] public section

/-!
# Shifted thresholds in Lemma 6

The linear approximate oracle in arXiv:1705.01843v4 uses the threshold
`c̃ - (r+1)θ`. This accommodates the full error in the normalized trace
estimates, including the estimate of the objective matrix.
-/

set_option autoImplicit false

open scoped BigOperators
open Matrix
open Qatlib.Papers.QSDPsolver17.MainResults

namespace Qatlib.Papers.QSDPsolver17.MainResults

variable {n m : ℕ}

/-- The normalized trace slack equals the unnormalized slack after
multiplication by the positive trace of `X`. -/
theorem trace_slack_normalized (P : SdpData n m) (X : Matrix (Fin n) (Fin n) ℂ)
    (hTr : 0 < X.trace.re) (y : Fin m → ℝ) :
    (Matrix.trace ((∑ j, (y j : ℂ) • P.A j - P.C) * X)).re =
      X.trace.re * ((∑ j, ((P.A j * X).trace.re / X.trace.re) * y j) -
        (P.C * X).trace.re / X.trace.re) := by
  have hm : X.trace.re * ∑ j, ((P.A j * X).trace.re / X.trace.re) * y j =
      ∑ j, y j * (P.A j * X).trace.re := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  rw [mul_sub, hm, mul_div_cancel₀ _ hTr.ne']
  simp [Matrix.sub_mul, Matrix.sum_mul, Matrix.trace_sum, Matrix.trace_smul,
    Complex.re_sum, Complex.mul_re]

/-- The absolute slack error in the constraint sum is at most `θr`
for nonnegative coefficients of total mass at most `r`. -/
private theorem weighted_trace_error (a b y : Fin m → ℝ) (r θ : ℝ)
    (hθ : 0 ≤ θ) (h : ∀ j, |a j - b j| ≤ θ) (hy : ∀ j, 0 ≤ y j) (hr : ∑ j, y j ≤ r) :
    |(∑ j, a j * y j) - ∑ j, b j * y j| ≤ θ * r := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  calc
    _ ≤ ∑ j, |(a j - b j) * y j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, θ * y j := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (hy j)]
      exact mul_le_mul_of_nonneg_right (h j) (hy j)
    _ ≤ _ := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hr hθ

/-- The two inclusions of Lemma 6 use the shifted threshold
`c̃ - (r+1)θ`; the final slack is measured against the unnormalized `X`. -/
theorem lemma6_shifted_polytope (P : SdpData n m) (X : Matrix (Fin n) (Fin n) ℂ)
    (aTilde : Fin m → ℝ) (ctilde α R r θ : ℝ)
    (hTrpos : 0 < X.trace.re) (hTr : X.trace.re ≤ R) (hr : 1 ≤ r) (hθ : 0 ≤ θ)
    (ha : ∀ j, |aTilde j - (P.A j * X).trace.re / X.trace.re| ≤ θ)
    (hc : |ctilde - (P.C * X).trace.re / X.trace.re| ≤ θ) :
    (∀ y, y ∈ Polytope P X α 0 → (∑ j, y j) ≤ r →
      y ∈ PTilde P aTilde (ctilde - (r + 1) * θ) α r) ∧
    (∀ y, y ∈ PTilde P aTilde (ctilde - (r + 1) * θ) α r →
      y ∈ Polytope P X α (4 * R * r * θ)) := by
  let a (j : Fin m) := (P.A j * X).trace.re / X.trace.re
  let c := (P.C * X).trace.re / X.trace.re
  have htrace (y : Fin m → ℝ) := trace_slack_normalized P X hTrpos y
  have hc' : -θ ≤ ctilde - c ∧ ctilde - c ≤ θ := abs_le.mp hc
  constructor
  · intro y hy hyR
    have hy0 : 0 ≤ X.trace.re * ((∑ j, a j * y j) - c) := by
      have := hy.2.1
      simpa only [neg_zero, htrace] using this
    have hslack := (mul_nonneg_iff_of_pos_left hTrpos).mp hy0
    have he := (abs_le.mp (weighted_trace_error aTilde a y r θ hθ ha hy.2.2 hyR)).1
    exact ⟨hy.1, hyR, by linarith only [hslack, he, hc'.2], hy.2.2⟩
  · intro y hy
    have he := (abs_le.mp (weighted_trace_error aTilde a y r θ hθ ha hy.2.2.2 hy.2.1)).2
    have hslack : -4 * r * θ ≤ (∑ j, a j * y j) - c := by
      have hrθ := mul_le_mul_of_nonneg_right hr hθ
      linarith only [he, hc'.1, hy.2.2.1, hrθ]
    have hscale := mul_le_mul_of_nonneg_left hslack hTrpos.le
    have hTrscale := mul_le_mul_of_nonneg_right hTr
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (zero_le_one.trans hr)) hθ)
    refine ⟨hy.1, ?_, hy.2.2.2⟩
    rw [htrace]
    linarith only [hscale, hTrscale]

end Qatlib.Papers.QSDPsolver17.MainResults
