/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SpanProgram07.MainResults

def subComplexity (σ s : ℝ) : ℝ := max σ⁻¹ s

theorem inv_le_subComplexity (σ s : ℝ) : σ⁻¹ ≤ subComplexity σ s := le_max_left _ _

theorem le_subComplexity (σ s : ℝ) : s ≤ subComplexity σ s := le_max_right _ _

theorem notGate_ratio {lam aO bi bO : ℂ} (hbO : bO ≠ 0)
    (h : lam * bO = bi + aO) : aO / bO = lam - bi / bO := by
  have h' : aO = lam * bO - bi := by linear_combination -h
  rw [h']
  field_simp

theorem notGate_ratio_real {lam ri rO : ℝ} (h : lam = ri⁻¹ + rO) : rO = lam - ri⁻¹ := by
  linarith

theorem notGate_sigma_false {σi σO : ℝ} (hσ : 0 < σi) (h : σO⁻¹ = σi⁻¹ + 1) :
    σO = σi / (1 + σi) := by
  have hpos : 0 < σO⁻¹ := by rw [h]; positivity
  have hO : 0 < σO := inv_pos.mp hpos
  field_simp at h ⊢
  linarith

theorem notGate_invSigma_false_le {σi : ℝ} (h0 : 0 < σi) (h1 : σi ≤ 1) :
    (σi / (1 + σi))⁻¹ ≤ 2 * σi⁻¹ := by
  have h1' : 0 < 1 + σi := by linarith
  rw [inv_div]
  have hne : σi ≠ 0 := ne_of_gt h0
  rw [div_le_iff₀ h0]
  have hmul : σi⁻¹ * σi = 1 := inv_mul_cancel₀ hne
  nlinarith [mul_le_mul_of_nonneg_left h1 (le_of_lt h0)]

theorem notGate_sO_false {lam si rO sO : ℝ} (hlam : 0 < lam) (hsi : si ≠ 0)
    (hRo : rO = lam - (lam * si)⁻¹) (hsO : sO = -(lam * rO)⁻¹) :
    sO = si / (1 - lam ^ 2 * si) := by
  subst hRo; subst hsO
  have hlamne : lam ≠ 0 := ne_of_gt hlam
  have hprod : lam * si ≠ 0 := mul_ne_zero hlamne hsi
  have key : -(lam * (lam - (lam * si)⁻¹)) = (1 - lam ^ 2 * si) / si := by
    field_simp
    ring
  rw [← inv_neg, key, inv_div]

theorem notGate_sO_true {lam si rO sO : ℝ} (hlam : 0 < lam)
    (hRo : rO = lam - (-(lam * si)⁻¹)⁻¹) (hsO : sO = rO / lam) : sO = si + 1 := by
  subst hRo; subst hsO
  have hlamne : lam ≠ 0 := ne_of_gt hlam
  rw [inv_neg, inv_inv]
  field_simp
  ring

theorem notGate_sO_false_bounds {lam si : ℝ} (_hlam : 0 < lam) (hs : 0 ≤ si)
    (hls : lam ^ 2 * si ≤ 1 / 2) :
    si ≤ si / (1 - lam ^ 2 * si) ∧ si / (1 - lam ^ 2 * si) ≤ 2 * si := by
  have hden : 0 < 1 - lam ^ 2 * si := by linarith
  have hsq : 0 ≤ si * (lam ^ 2 * si) :=
    mul_nonneg hs (mul_nonneg (sq_nonneg lam) hs)
  constructor
  · rw [le_div_iff₀ hden]; nlinarith
  · rw [div_le_iff₀ hden]; nlinarith

theorem notGate_subComplexity_le {σi si lam : ℝ} (hσ : 0 < σi) (hσ1 : σi ≤ 1) (hs : 0 ≤ si)
    (hlam : 0 < lam) (hls : lam ^ 2 * si ≤ 1 / 2) :
    subComplexity (σi / (1 + σi)) (si / (1 - lam ^ 2 * si)) ≤
      2 * subComplexity σi si + 2 := by
  have h1 : (σi / (1 + σi))⁻¹ ≤ 2 * σi⁻¹ := notGate_invSigma_false_le hσ hσ1
  have h2 : si / (1 - lam ^ 2 * si) ≤ 2 * si := (notGate_sO_false_bounds hlam hs hls).2
  have hσi : σi⁻¹ ≤ subComplexity σi si := inv_le_subComplexity σi si
  have hsi : si ≤ subComplexity σi si := le_subComplexity σi si
  have hz : 0 ≤ subComplexity σi si := by
    have : 0 < σi⁻¹ := by positivity
    linarith [inv_le_subComplexity σi si]
  unfold subComplexity
  refine max_le ?_ ?_
  · calc (σi / (1 + σi))⁻¹ ≤ 2 * σi⁻¹ := h1
      _ ≤ 2 * subComplexity σi si := by linarith
      _ ≤ 2 * subComplexity σi si + 2 := by linarith
  · calc si / (1 - lam ^ 2 * si) ≤ 2 * si := h2
      _ ≤ 2 * subComplexity σi si := by linarith
      _ ≤ 2 * subComplexity σi si + 2 := by linarith

theorem notGate_subComplexity_le_true {σi si : ℝ} (_hσ : 0 < σi) (_hs : 0 ≤ si) :
    subComplexity σi (si + 1) ≤ subComplexity σi si + 1 := by
  unfold subComplexity
  refine max_le ?_ ?_
  · linarith [le_max_left σi⁻¹ si]
  · linarith [le_max_right σi⁻¹ si]

end Qatlib.Papers.SpanProgram07.MainResults
