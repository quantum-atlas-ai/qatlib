/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.AmplifyCore.Theorem2QuadraticSpeedupQuan

/-!
# Two-dimensional reflection rotations

This module computes the rotation induced by two complex-Hilbert-space reflections and relates
it to normalized good and bad components in amplitude amplification. It gives two explicit
basis-action formulas for Lemma 4 of [Itakura2005], with the signs determined by the chosen
reflection order.

## Main statements

* `lemma4_rotation_two_dimensional`: Computes the product of line reflections on an orthonormal
  pair.
* `lemma4_amplification_step_normalized_rotation`: Computes the amplification step on normalized
  projected components.

## References

* [Itakura, 2005][Itakura2005]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommuteTest05.MainResults.Lemma4Rotation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The map `x ↦ (2 * inner ℂ a x) • a - x`, which is reflection through the span of `a` when
`a` is a unit vector. -/
def reflection (a : E) (x : E) : E := (2 * inner ℂ a x) • a - x

/-- The composition of reflection through `α` followed by reflection through `ψ`. -/
def amplificationStep (α ψ : E) (x : E) : E := reflection ψ (reflection α x)

/-- For orthonormal `α` and `β` and `ψ = cos θ • α + sin θ • β`, `amplificationStep α ψ` acts on
their span by the rotation of angle `2 * θ` displayed in the conclusion. See [Itakura, Lemma
4][Itakura2005]. -/
theorem lemma4_rotation_two_dimensional {α β : E} {θ : ℝ}
    (hα : inner ℂ α α = 1) (hβ : inner ℂ β β = 1) (hαβ : inner ℂ α β = 0) :
    let ψ : E := (Real.cos θ : ℂ) • α + (Real.sin θ : ℂ) • β
    amplificationStep α ψ α =
        (Real.cos (2 * θ) : ℂ) • α + (Real.sin (2 * θ) : ℂ) • β ∧
      amplificationStep α ψ β =
        -((Real.sin (2 * θ) : ℂ) • α) + (Real.cos (2 * θ) : ℂ) • β := by
  intro ψ
  have hβα : inner ℂ β α = 0 := by
    rw [← inner_conj_symm, hαβ, map_zero]
  have hψα : inner ℂ ψ α = (Real.cos θ : ℂ) := by
    simp only [ψ, inner_add_left, inner_smul_left, hα, hβα,
      Complex.conj_ofReal]
    ring
  have hψβ : inner ℂ ψ β = (Real.sin θ : ℂ) := by
    simp only [ψ, inner_add_left, inner_smul_left, hβ, hαβ,
      Complex.conj_ofReal]
    ring
  have hRαα : reflection α α = α := by
    show (2 * inner ℂ α α) • α - α = α
    rw [hα]
    module
  have hRαβ : reflection α β = -β := by
    show (2 * inner ℂ α β) • α - β = -β
    rw [hαβ]
    simp
  have hψnegβ : inner ℂ ψ (-β) = -(Real.sin θ : ℂ) := by
    rw [inner_neg_right, hψβ]
  constructor
  · show reflection ψ (reflection α α) =
        (Real.cos (2 * θ) : ℂ) • α + (Real.sin (2 * θ) : ℂ) • β
    rw [hRαα]
    show (2 * inner ℂ ψ α) • ψ - α =
        (Real.cos (2 * θ) : ℂ) • α + (Real.sin (2 * θ) : ℂ) • β
    rw [hψα]
    simp only [ψ, smul_add, smul_smul]
    have hc_real : 2 * Real.cos θ * Real.cos θ = 1 + Real.cos (2 * θ) := by
      rw [Real.cos_two_mul]
      nlinarith [Real.sin_sq_add_cos_sq θ]
    have hc : (2 * (Real.cos θ : ℂ)) * (Real.cos θ : ℂ) =
        1 + (Real.cos (2 * θ) : ℂ) := by
      exact_mod_cast hc_real
    have hs_real : 2 * Real.cos θ * Real.sin θ = Real.sin (2 * θ) := by
      rw [Real.sin_two_mul]
      ring
    have hs : (2 * (Real.cos θ : ℂ)) * (Real.sin θ : ℂ) =
        (Real.sin (2 * θ) : ℂ) := by
      exact_mod_cast hs_real
    rw [hc, hs]
    module
  · show reflection ψ (reflection α β) =
        -((Real.sin (2 * θ) : ℂ) • α) + (Real.cos (2 * θ) : ℂ) • β
    rw [hRαβ]
    show (2 * inner ℂ ψ (-β)) • ψ - (-β) =
        -((Real.sin (2 * θ) : ℂ) • α) + (Real.cos (2 * θ) : ℂ) • β
    rw [hψnegβ]
    simp only [ψ, smul_add, smul_smul]
    have hc_real : 2 * (-Real.sin θ) * Real.cos θ = -Real.sin (2 * θ) := by
      rw [Real.sin_two_mul]
      ring
    have hc : (2 * (-(Real.sin θ : ℂ))) * (Real.cos θ : ℂ) =
        -(Real.sin (2 * θ) : ℂ) := by
      exact_mod_cast hc_real
    have hs_real : 2 * (-Real.sin θ) * Real.sin θ = Real.cos (2 * θ) - 1 := by
      rw [Real.cos_two_mul]
      nlinarith [Real.sin_sq_add_cos_sq θ]
    have hs : (2 * (-(Real.sin θ : ℂ))) * (Real.sin θ : ℂ) =
        (Real.cos (2 * θ) : ℂ) - 1 := by
      exact_mod_cast hs_real
    rw [hc, hs]
    module

section Bridge

open Qatlib.Concepts.AmplitudeCore.AmplifyCore
open Qatlib.Concepts.AmplitudeCore.AmplifyCore.AmplitudeAmplificationCore

variable [CompleteSpace E] {S : Set ℤ}

/-- If the good-projection squared norm equals `sin θ ^ 2` with `0 < θ < π / 2`, the
amplification step acts on the normalized good and bad components by the stated sine-cosine
rotation formulas. See [Itakura, Lemma 4][Itakura2005]. -/
theorem lemma4_amplification_step_normalized_rotation
    (hzero : (0 : ℤ) ∈ S) (basis : HilbertBasis S ℂ E)
    (A : E ≃ₗᵢ[ℂ] E) (χ : ℤ → Bool) (θ : ℝ)
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi / 2)
    (ha : Real.sin θ ^ 2 = ‖goodProjection basis χ (A (basis ⟨0, hzero⟩))‖ ^ 2) :
    let e₀ := basis ⟨0, hzero⟩
    let P := goodProjection basis χ
    let ψ := A e₀
    let u := (↑(1 / Real.sin θ) : ℂ) • P ψ
    let w := (↑(1 / Real.cos θ) : ℂ) • (ψ - P ψ)
    step A e₀ P u = (↑(Real.cos (2 * θ)) : ℂ) • u -
        (↑(Real.sin (2 * θ)) : ℂ) • w ∧
      step A e₀ P w = (↑(Real.sin (2 * θ)) : ℂ) • u +
        (↑(Real.cos (2 * θ)) : ℂ) • w :=
  quantum_amplitude_amplification_theorem2_normalized_actions
    hzero basis A χ θ hθ0 hθπ ha

end Bridge

end Qatlib.Papers.CommuteTest05.MainResults.Lemma4Rotation
