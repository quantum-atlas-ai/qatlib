/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LatentPQCTran26.MainResults.GradientPreservation
import Mathlib.MeasureTheory.Integral.Average
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace Qatlib.Papers.LatentPQCTran26.MainResults.BarrenFreeInit

theorem exists_grad_rich_point
    {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) [IsProbabilityMeasure ν]
    (F : Θ → ℝ) (hint : Integrable F ν) (c : ℝ) (hc : c ≤ ∫ θ, F θ ∂ν) :
    ∃ θ, c ≤ F θ := by
  obtain ⟨θ, hθ⟩ := exists_integral_le hint
  exact ⟨θ, le_trans hc hθ⟩

theorem radius_keeps_lower_bound (g Λ γ : ℝ) (hΛ : 0 < Λ) (hγ : γ ≤ g / (2 * Λ)) :
    g / 2 ≤ g - Λ * γ := by
  have hmul : Λ * γ ≤ Λ * (g / (2 * Λ)) :=
    mul_le_mul_of_nonneg_left hγ (le_of_lt hΛ)
  have hsimp : Λ * (g / (2 * Λ)) = g / 2 := by field_simp
  linarith [hmul, hsimp.le]

theorem trainability_from_grad_rich_point
    {Z : Type*} [MeasurableSpace Z] (r : Measure Z) [IsProbabilityMeasure r]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (grad : E → E) (Λ g γ : ℝ) (hΛpos : 0 < Λ) (hγ : 0 ≤ γ)
    (hg0 : 0 ≤ g) (hγbound : γ ≤ g / (2 * Λ))
    (hLip : ∀ x y, ‖grad x - grad y‖ ≤ Λ * ‖x - y‖)
    (θstar : E) (hg : g ≤ ‖grad θstar‖)
    (s : Z → E) (hs : ∀ z, ‖s z‖ ≤ 1)
    (hint : Integrable (fun z => (‖grad (θstar + γ • s z)‖) ^ 2) r) :
    (g / 2) ^ 2 ≤ ∫ z, (‖grad (θstar + γ • s z)‖) ^ 2 ∂r := by
  apply Qatlib.Papers.LatentPQCTran26.MainResults.GradientPreservation.proposition7_expectation
    r grad (fun z => θstar + γ • s z) Λ g γ hΛpos hγ hg0 hγbound _ hint
  intro z
  exact Qatlib.Papers.LatentPQCTran26.MainResults.GradientPreservation.image_manifold_lower_bound
    grad Λ g γ hΛpos hγ hLip θstar hg (s z) (hs z) hγbound

theorem corollary8_trainability
    {Z : Type*} [MeasurableSpace Z] (r : Measure Z) [IsProbabilityMeasure r]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (grad : E → E) (Λ : ℝ) (hΛpos : 0 < Λ)
    (hLip : ∀ x y, ‖grad x - grad y‖ ≤ Λ * ‖x - y‖)
    (c : ℝ) (_hc0 : 0 ≤ c)
    (θstar : E) (g : ℝ) (hg0 : 0 ≤ g)
    (hg2 : c ≤ g ^ 2) (hgval : g ≤ ‖grad θstar‖)
    (hγ0 : 0 ≤ g / (2 * Λ))
    (s : Z → E) (hs : ∀ z, ‖s z‖ ≤ 1)
    (hint : Integrable (fun z => (‖grad (θstar + (g / (2 * Λ)) • s z)‖) ^ 2) r) :
    c / 4 ≤ ∫ z, (‖grad (θstar + (g / (2 * Λ)) • s z)‖) ^ 2 ∂r := by
  have hmain := trainability_from_grad_rich_point r grad Λ g (g / (2 * Λ)) hΛpos hγ0
    hg0 (le_refl _) hLip θstar hgval s hs hint
  have hsq : c / 4 ≤ (g / 2) ^ 2 := by nlinarith [hg2]
  linarith [hmain, hsq]

end Qatlib.Papers.LatentPQCTran26.MainResults.BarrenFreeInit
