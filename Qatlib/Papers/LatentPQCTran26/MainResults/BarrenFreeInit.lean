/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LatentPQCTran26.MainResults.GradientPreservation
import Mathlib.MeasureTheory.Integral.Average

/-!
# Initialization near a point with a large gradient

`exists_grad_rich_point` extracts a point whose value is at least a lower bound on a probability
mean. A Lipschitz gradient remains large on perturbations of radius at most `g / (2 * Λ)`, and
`trainability_from_grad_rich_point` and `corollary8_trainability` convert this pointwise
estimate into an expected squared-gradient bound. See [TranEtAl2026] for the paper context.

## Main statements

* `exists_grad_rich_point`: An integrable real function on a probability space attains a value
  at least any given lower bound on its integral.
* `trainability_from_grad_rich_point`: A `Λ`-Lipschitz gradient with norm at least nonnegative
  `g` at the center has expected squared norm at least `(g / 2) ^ 2` under bounded perturbations
  of radius `0 ≤ γ ≤ g / (2 * Λ)`, assuming integrability and `Λ > 0`.
* `corollary8_trainability`: With `Λ > 0`, nonnegative `g`, `c ≤ g ^ 2`, and the stated
  Lipschitz and integrability hypotheses, perturbing a point of gradient norm at least `g` by
  radius `g / (2 * Λ)` gives expected squared-gradient norm at least `c / 4`.

## References

* [Tran et al., 2026][TranEtAl2026]
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace Qatlib.Papers.LatentPQCTran26.MainResults.BarrenFreeInit

/-- An integrable real function on a probability space attains a value at least any given lower
bound on its integral. -/
theorem exists_grad_rich_point
    {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) [IsProbabilityMeasure ν]
    (F : Θ → ℝ) (hint : Integrable F ν) (c : ℝ) (hc : c ≤ ∫ θ, F θ ∂ν) :
    ∃ θ, c ≤ F θ := by
  obtain ⟨θ, hθ⟩ := exists_integral_le hint
  exact ⟨θ, le_trans hc hθ⟩

/-- If `Λ > 0` and `γ ≤ g / (2 * Λ)`, then `g - Λ * γ ≥ g / 2`. -/
theorem radius_keeps_lower_bound (g Λ γ : ℝ) (hΛ : 0 < Λ) (hγ : γ ≤ g / (2 * Λ)) :
    g / 2 ≤ g - Λ * γ := by
  have hmul : Λ * γ ≤ Λ * (g / (2 * Λ)) :=
    mul_le_mul_of_nonneg_left hγ (le_of_lt hΛ)
  have hsimp : Λ * (g / (2 * Λ)) = g / 2 := by field_simp
  linarith [hmul, hsimp.le]

/-- A `Λ`-Lipschitz gradient with norm at least nonnegative `g` at the center has expected
squared norm at least `(g / 2) ^ 2` under bounded perturbations of radius `0 ≤ γ ≤ g / (2 *
Λ)`, assuming integrability and `Λ > 0`. -/
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

/-- With `Λ > 0`, nonnegative `g`, `c ≤ g ^ 2`, and the stated Lipschitz and integrability
hypotheses, perturbing a point of gradient norm at least `g` by radius `g / (2 * Λ)` gives
expected squared-gradient norm at least `c / 4` [TranEtAl2026]. -/
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
