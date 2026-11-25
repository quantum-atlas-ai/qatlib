/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.FastHermitian06.MainResults.SpinFlip
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-!
# Large Hamiltonian parameters at fixed gap and small passage time

Choose the angle close enough to minus pi over two to meet the time budget and
both parameter lower bounds. The fixed gap determines the off-diagonal parameter.
The sine relation then determines the magnitude of the second parameter.
-/

set_option autoImplicit false

open Qatlib.Papers.FastHermitian06.MainResults.Defs

namespace Qatlib.Papers.FastHermitian06.MainResults

/-- The fixed-gap small-time family in Eqs. (12)–(13) may be chosen with both
matrix parameters exceeding any given magnitude threshold. -/
theorem fixed_gap_large_parameters (ħ ω₀ : ℝ) (hħ : 0 < ħ) (hω₀ : 0 < ω₀) :
    ∀ ε M : ℝ, 0 < ε → ∃ (r s θ α : ℝ),
      unbrokenPT r s θ ∧ omega r s θ = ω₀ ∧ Real.sin α = (r / s) * Real.sin θ ∧
      0 < (2 * α + Real.pi) * ħ / omega r s θ ∧
      (2 * α + Real.pi) * ħ / omega r s θ < ε ∧ M < s ∧ M < |r| := by
  intro ε M hε
  let B := max M 0 + 1
  have hM : M < B := by dsimp [B]; linarith [le_max_left M 0]
  have hB : 0 < B := by dsimp [B]; linarith [le_max_right M 0]
  let δ := min (Real.pi / 4) (min (ε * ω₀ / (4 * ħ)) (ω₀ / (8 * B)))
  have hδ : 0 < δ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hδπ : δ ≤ Real.pi / 4 := min_le_left _ _
  have hδt : δ ≤ ε * ω₀ / (4 * ħ) := (min_le_right _ _).trans (min_le_left _ _)
  have hδB : δ ≤ ω₀ / (8 * B) := (min_le_right _ _).trans (min_le_right _ _)
  have hsin : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  have hcos : 1 / 2 ≤ Real.cos δ := by
    rw [← Real.cos_pi_div_three]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hδ.le (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])
  let s := ω₀ / (2 * Real.sin δ)
  let α := δ - Real.pi / 2
  let r := s * Real.sin α
  have hs : 0 < s := by dsimp [s]; positivity
  have hαcos : Real.cos α = Real.sin δ := Real.cos_sub_pi_div_two δ
  have hαsin : Real.sin α = -Real.cos δ := Real.sin_sub_pi_div_two δ
  have hscale : 2 * s * Real.sin δ = ω₀ := by dsimp [s]; field_simp
  have hsq : omegaSq r s (Real.pi / 2) = ω₀ ^ 2 := by
    rw [← hscale]
    unfold omegaSq
    rw [Real.sin_pi_div_two, ← hαcos]
    dsimp [r]
    linear_combination -4 * s ^ 2 * Real.sin_sq_add_cos_sq α
  have hgap : omega r s (Real.pi / 2) = ω₀ := by
    rw [omega, hsq, Real.sqrt_sq hω₀.le]
  have hangle : 2 * α + Real.pi = 2 * δ := by dsimp [α]; ring
  have hfour : 4 * B ≤ s := by
    dsimp [s]
    rw [le_div_iff₀ (by positivity)]
    have h1 := (le_div_iff₀ (show 0 < 8 * B by positivity)).mp hδB
    have h2 := mul_le_mul_of_nonneg_right (Real.sin_le hδ.le)
      (show 0 ≤ 8 * B by positivity)
    nlinarith
  have hr : |r| = s * Real.cos δ := by
    dsimp [r]
    rw [hαsin, abs_mul, abs_of_pos hs, abs_neg, abs_of_nonneg (by linarith)]
  refine ⟨r, s, Real.pi / 2, α, ?_, hgap, ?_, ?_, ?_, ?_, ?_⟩
  · change 0 < omegaSq r s (Real.pi / 2)
    rw [hsq]
    positivity
  · change Real.sin α = (s * Real.sin α / s) * Real.sin (Real.pi / 2)
    rw [Real.sin_pi_div_two, mul_one, mul_div_cancel_left₀ _ hs.ne']
  · rw [hgap, hangle]
    positivity
  · rw [hgap, hangle, div_lt_iff₀ hω₀]
    have h1 := (le_div_iff₀ (show 0 < 4 * ħ by positivity)).mp hδt
    nlinarith [mul_pos hε hω₀]
  · linarith
  · rw [hr]
    linarith [mul_le_mul_of_nonneg_left hcos hs.le]

end Qatlib.Papers.FastHermitian06.MainResults
