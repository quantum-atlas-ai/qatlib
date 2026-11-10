/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.Normed.Group.Basic

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace Qatlib.Papers.LatentPQCTran26.MainResults.GradientPreservation

theorem grad_lower_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (grad : E → E) (Λ g γ : ℝ) (hΛ : 0 ≤ Λ) (hγ : 0 ≤ γ)
    (hLip : ∀ x y, ‖grad x - grad y‖ ≤ Λ * ‖x - y‖)
    (θstar : E) (hg : g ≤ ‖grad θstar‖)
    (s : E) (hs : ‖s‖ ≤ 1) :
    g - Λ * γ ≤ ‖grad (θstar + γ • s)‖ := by

  have htri : ‖grad θstar‖ - ‖grad (θstar + γ • s)‖ ≤
      ‖grad θstar - grad (θstar + γ • s)‖ := norm_sub_norm_le _ _

  have hlip := hLip θstar (θstar + γ • s)
  have hdist : ‖θstar - (θstar + γ • s)‖ = γ * ‖s‖ := by
    have hsub : θstar - (θstar + γ • s) = -(γ • s) := by abel
    rw [hsub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ]
  have hbound : ‖grad θstar - grad (θstar + γ • s)‖ ≤ Λ * (γ * ‖s‖) := by
    rw [← hdist]; exact hlip
  have hsγ : γ * ‖s‖ ≤ γ := by
    have h := mul_le_mul_of_nonneg_left hs hγ
    simpa using h
  have hΛγ : Λ * (γ * ‖s‖) ≤ Λ * γ := mul_le_mul_of_nonneg_left hsγ hΛ
  have key : ‖grad θstar‖ - ‖grad (θstar + γ • s)‖ ≤ Λ * γ := by linarith
  linarith [hg, key]

theorem image_manifold_lower_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (grad : E → E) (Λ g γ : ℝ) (hΛpos : 0 < Λ) (hγ : 0 ≤ γ)
    (hLip : ∀ x y, ‖grad x - grad y‖ ≤ Λ * ‖x - y‖)
    (θstar : E) (hg : g ≤ ‖grad θstar‖)
    (s : E) (hs : ‖s‖ ≤ 1) (hγbound : γ ≤ g / (2 * Λ)) :
    g / 2 ≤ ‖grad (θstar + γ • s)‖ := by
  have hbase := grad_lower_bound grad Λ g γ (le_of_lt hΛpos) hγ hLip θstar hg s hs
  have hkey : g / 2 ≤ g - Λ * γ := by
    have hmul : Λ * γ ≤ Λ * (g / (2 * Λ)) := mul_le_mul_of_nonneg_left hγbound (le_of_lt hΛpos)
    have hsimp : Λ * (g / (2 * Λ)) = g / 2 := by
      field_simp
    linarith [hmul, hsimp.le, hsimp.ge]
  linarith [hbase, hkey]

theorem expected_grad_sq_lower_bound
    {Z : Type*} [MeasurableSpace Z] (r : Measure Z) [IsProbabilityMeasure r]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (grad : E → E) (f : Z → E) (c : ℝ) (hc : 0 ≤ c)
    (hpoint : ∀ z, c ≤ ‖grad (f z)‖)
    (hint : Integrable (fun z => (‖grad (f z)‖) ^ 2) r) :
    c ^ 2 ≤ ∫ z, (‖grad (f z)‖) ^ 2 ∂r := by
  have hsq : ∀ z, c ^ 2 ≤ (‖grad (f z)‖) ^ 2 := by
    intro z
    have h1 : c ≤ ‖grad (f z)‖ := hpoint z
    have h2 : 0 ≤ ‖grad (f z)‖ := norm_nonneg _
    nlinarith [hc, h1, h2]
  have hconst_int : Integrable (fun _ : Z => c ^ 2) r := integrable_const _
  have hmono : ∫ z, c ^ 2 ∂r ≤ ∫ z, (‖grad (f z)‖) ^ 2 ∂r :=
    integral_mono hconst_int hint (fun z => hsq z)
  have hconst : ∫ z, c ^ 2 ∂r = c ^ 2 := by
    rw [integral_const, probReal_univ, one_smul]
  rwa [hconst] at hmono

theorem proposition7_expectation
    {Z : Type*} [MeasurableSpace Z] (r : Measure Z) [IsProbabilityMeasure r]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (grad : E → E) (f : Z → E) (Λ g γ : ℝ) (hΛpos : 0 < Λ) (_hγ : 0 ≤ γ)
    (hg : 0 ≤ g) (hγbound : γ ≤ g / (2 * Λ))
    (hpoint : ∀ z, g / 2 ≤ ‖grad (f z)‖)
    (hint : Integrable (fun z => (‖grad (f z)‖) ^ 2) r) :
    (g / 2) ^ 2 ≤ ∫ z, (‖grad (f z)‖) ^ 2 ∂r := by
  have hcval : (g - Λ * γ) ^ 2 ≥ (g / 2) ^ 2 := by
    have hmul : Λ * γ ≤ Λ * (g / (2 * Λ)) := mul_le_mul_of_nonneg_left hγbound (le_of_lt hΛpos)
    have hsimp : Λ * (g / (2 * Λ)) = g / 2 := by field_simp
    have hge : g / 2 ≤ g - Λ * γ := by linarith [hmul, hsimp.le]
    have hcnonneg : 0 ≤ g - Λ * γ := by linarith
    nlinarith [hge, hcnonneg, hg]
  have hmain := expected_grad_sq_lower_bound r grad f (g / 2) (by positivity) hpoint hint
  linarith [hmain, hcval]

end Qatlib.Papers.LatentPQCTran26.MainResults.GradientPreservation
