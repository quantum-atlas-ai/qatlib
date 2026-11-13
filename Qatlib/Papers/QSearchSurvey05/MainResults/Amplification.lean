/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.AmplifyCore.Theorem2QuadraticSpeedupQuan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Amplitude amplification in a Hilbert space

This module formalizes the amplitude amplification bound presented as Theorem 2.2 in
[Ambainis2005]. Starting from a positive lower bound ε on the good projection probability,
`theorem22_amplitude_amplification` bounds the two attempt success expression and the total
iteration count.

## Main statements

* `theorem22_amplitude_amplification`: Gives success at least 2/3 for two attempts within
  π/(2√ε) iterations.

## References

* [Ambainis, 2005][Ambainis2005]
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.AmplitudeCore.AmplifyCore
open Qatlib.Concepts.AmplitudeCore.AmplifyCore.AmplitudeAmplificationCore

namespace Qatlib.Papers.QSearchSurvey05.MainResults

/-- For initial good probability at least ε > 0 and angle θ ∈ (0, π/2], two attempts using
⌊π/(4θ)⌋ amplification steps each have combined success expression at least 2/3 and total
iteration count at most π/(2√ε). See [Ambainis2005]. -/
theorem theorem22_amplitude_amplification
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (S : Set ℤ) (hzero : (0 : ℤ) ∈ S)
    (basis : HilbertBasis S ℂ E) (U : E ≃ₗᵢ[ℂ] E) (χ : ℤ → Bool)
    (ε : ℝ) (hε : 0 < ε)
    (θ : ℝ) (hθ0 : 0 < θ) (hθπ : θ ≤ Real.pi / 2)
    (hsin : Real.sin θ ^ 2 = ‖goodProjection basis χ (U (basis ⟨0, hzero⟩))‖ ^ 2)
    (haε : ε ≤ ‖goodProjection basis χ (U (basis ⟨0, hzero⟩))‖ ^ 2) :
    let P : E →L[ℂ] E := goodProjection basis χ
    let e₀ : E := basis ⟨0, hzero⟩
    let ψ : E := U e₀
    let m : ℕ := Nat.floor (Real.pi / (4 * θ))
    (2 / 3 : ℝ) ≤ 1 - (1 - ‖P (((step U e₀ P)^[m]) ψ)‖ ^ 2) ^ 2 ∧
      (2 * (m : ℝ)) ≤ Real.pi / (2 * Real.sqrt ε) := by
  (try dsimp only)
  have ha0 : 0 < ‖goodProjection basis χ (U (basis ⟨0, hzero⟩))‖ ^ 2 :=
    lt_of_lt_of_le hε haε
  have hmain := quantum_amplitude_amplification_theorem2 E S hzero basis U χ θ
    ha0 hθ0 hθπ hsin

  set X : ℝ := ‖goodProjection basis χ (U (basis ⟨0, hzero⟩))‖ ^ 2 with hX
  set Y : ℝ := ‖goodProjection basis χ
      (((step U (basis ⟨0, hzero⟩) (goodProjection basis χ))^[Nat.floor (Real.pi / (4 * θ))])
        (U (basis ⟨0, hzero⟩)))‖ ^ 2 with hY

  have hp : (1 / 2 : ℝ) ≤ Y := by
    have hmax : (1 / 2 : ℝ) ≤ max (1 - X) X := by
      have h1 := le_max_left (1 - X) X
      have h2 := le_max_right (1 - X) X
      linarith
    simpa [hX, hY] using le_trans hmax hmain

  have hpost : Y ≤ 1 := by
    by_cases hsmall : θ ≤ Real.pi / 4
    · have hsq := quantum_amplitude_amplification_theorem2_success_sq hzero basis U χ θ
        hθ0 (by linarith [Real.pi_pos]) hsin (Nat.floor (Real.pi / (4 * θ)))
      have hval : Y =
          Real.sin ((2 * (Nat.floor (Real.pi / (4 * θ)) : ℝ) + 1) * θ) ^ 2 := by
        rw [hY]
        exact hsq
      rw [hval]
      exact Real.sin_sq_le_one _
    · have hm0 : Nat.floor (Real.pi / (4 * θ)) = 0 := by
        rw [Nat.floor_eq_zero]
        rw [div_lt_one (by linarith : (0 : ℝ) < 4 * θ)]
        linarith
      have hYexpr : Y = ‖goodProjection basis χ (U (basis ⟨0, hzero⟩))‖ ^ 2 := by
        rw [hY, hm0, Function.iterate_zero_apply]
      rw [hYexpr, ← hX, ← hsin]
      exact Real.sin_sq_le_one _
  constructor
  · have hprod : (0 : ℝ) ≤ (Y - 1 / 2) * (1 - Y) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [hp, hpost, hprod]
  · have hsq : Real.sqrt (‖goodProjection basis χ (U (basis ⟨0, hzero⟩))‖ ^ 2) =
        ‖goodProjection basis χ (U (basis ⟨0, hzero⟩))‖ := Real.sqrt_sq (norm_nonneg _)
    have hsin_nonneg : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_nonneg_of_le_pi hθ0.le (by linarith [hθπ, Real.pi_pos])
    have hnorm : ‖goodProjection basis χ (U (basis ⟨0, hzero⟩))‖ = Real.sin θ := by
      have h1 : ‖goodProjection basis χ (U (basis ⟨0, hzero⟩))‖ =
          Real.sqrt (‖goodProjection basis χ (U (basis ⟨0, hzero⟩))‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      rw [h1, ← hX, ← hsin, Real.sqrt_sq hsin_nonneg]
    have hsinle : ‖goodProjection basis χ (U (basis ⟨0, hzero⟩))‖ ≤ θ := by
      rw [hnorm]
      exact le_of_lt (Real.sin_lt hθ0)
    have hs : Real.sqrt ε ≤ Real.sqrt (‖goodProjection basis χ (U (basis ⟨0, hzero⟩))‖ ^ 2) :=
      Real.sqrt_le_sqrt haε
    rw [hsq] at hs
    have hfloor : ((Nat.floor (Real.pi / (4 * θ)) : ℕ) : ℝ) ≤ Real.pi / (4 * θ) :=
      Nat.floor_le (le_of_lt (div_pos Real.pi_pos (mul_pos (by norm_num) hθ0)))
    have hle : Real.pi / (4 * θ) ≤ Real.pi / (4 * Real.sqrt ε) :=
      div_le_div_of_nonneg_left Real.pi_pos.le
        (mul_pos (by norm_num) (Real.sqrt_pos.mpr hε)) (by linarith)
    calc (2 * (Nat.floor (Real.pi / (4 * θ)) : ℝ))
        ≤ 2 * (Real.pi / (4 * Real.sqrt ε)) := by linarith
      _ = Real.pi / (2 * Real.sqrt ε) := by ring

end Qatlib.Papers.QSearchSurvey05.MainResults
