/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCryptanal15.MainResults.Complexity.Core
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Qatlib.Concepts.AmplitudeCore.AmplifyCore.Theorem2QuadraticSpeedupQuan
set_option warningAsError false

set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace Qatlib.Papers.QCryptanal15.MainResults.Complexity

open Qatlib.Concepts.AmplitudeCore.AmplifyCore.AmplitudeAmplificationCore

theorem amplification_iterations_le_inv_sqrt {a θ : ℝ}
    (hθ0 : 0 < θ) (hθπ : θ ≤ Real.pi / 2)
    (hsin : Real.sin θ ^ 2 = a) :
    ((Nat.floor (Real.pi / (4 * θ)) : ℕ) : ℝ) ≤
      Real.pi / (4 * Real.sqrt a) + 1 := by
  have hsin_nonneg : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ0.le (by linarith [Real.pi_pos])
  have hsqrt : Real.sqrt a = Real.sin θ := by
    rw [← hsin, Real.sqrt_sq_eq_abs, abs_of_nonneg hsin_nonneg]
  have hsin_le_θ : Real.sin θ ≤ θ := Real.sin_le hθ0.le
  have hfloor : ((Nat.floor (Real.pi / (4 * θ)) : ℕ) : ℝ) ≤
      Real.pi / (4 * θ) := Nat.floor_le (div_nonneg Real.pi_pos.le (by positivity))
  have hden : 4 * Real.sin θ ≤ 4 * θ := by linarith
  have hsinpos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have hquot : Real.pi / (4 * θ) ≤ Real.pi / (4 * Real.sqrt a) := by
    rw [hsqrt]
    exact div_le_div_of_nonneg_left Real.pi_pos.le
      (mul_pos (by norm_num) hsinpos) hden
  linarith

theorem amplification_budget_pow2 (h : ℝ) :
    Real.pi / (4 * Real.sqrt (pow2 (-h))) + 1 = Real.pi / 4 * pow2 (h / 2) + 1 := by
  have hsqrt : Real.sqrt (pow2 (-h)) = pow2 (-(h / 2)) := by
    rw [sqrt_pow2]
    congr 1
    ring
  rw [hsqrt, pow2_neg]
  have hpos : pow2 (h / 2) ≠ 0 := pow2_ne_zero (h / 2)
  field_simp

theorem amplification_half_success_budget
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (S : Set ℤ) (hzero : (0 : ℤ) ∈ S) (basis : HilbertBasis S ℂ E)
    (A : E ≃ₗᵢ[ℂ] E) (χ : ℤ → Bool) (θ : ℝ)
    (ha0 : 0 < ‖goodProjection basis χ (A (basis ⟨0, hzero⟩))‖ ^ 2)
    (hθ0 : 0 < θ) (hθπ : θ ≤ Real.pi / 2)
    (hsin : Real.sin θ ^ 2 = ‖goodProjection basis χ (A (basis ⟨0, hzero⟩))‖ ^ 2) :
    ∃ m : ℕ,
      (m : ℝ) ≤
          Real.pi / (4 * Real.sqrt (‖goodProjection basis χ (A (basis ⟨0, hzero⟩))‖ ^ 2)) + 1 ∧
      max (1 - ‖goodProjection basis χ (A (basis ⟨0, hzero⟩))‖ ^ 2)
          (‖goodProjection basis χ (A (basis ⟨0, hzero⟩))‖ ^ 2) ≤
        ‖goodProjection basis χ
          (((step A (basis ⟨0, hzero⟩) (goodProjection basis χ))^[m])
            (A (basis ⟨0, hzero⟩)))‖ ^ 2 := by
  have hmain :=
    Qatlib.Concepts.AmplitudeCore.AmplifyCore.quantum_amplitude_amplification_theorem2
      E S hzero basis A χ θ ha0 hθ0 hθπ hsin
  exact ⟨Nat.floor (Real.pi / (4 * θ)),
    amplification_iterations_le_inv_sqrt hθ0 hθπ hsin, hmain⟩

end Qatlib.Papers.QCryptanal15.MainResults.Complexity
