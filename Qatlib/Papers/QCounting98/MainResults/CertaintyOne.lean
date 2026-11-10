/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Floor.Ring

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QCounting98.MainResults

def certaintyM0 (θ : ℝ) : ℕ := Nat.ceil (Real.pi / (4 * θ) - 1 / 2)

def certaintyTheta0 (θ : ℝ) : ℝ := Real.pi / (4 * (certaintyM0 θ : ℝ) + 2)

def certaintyA0 (θ : ℝ) : ℝ := Real.sin (certaintyTheta0 θ) ^ 2

theorem certainty_m0_lower (θ : ℝ) :
    Real.pi / (4 * θ) - 1 / 2 ≤ (certaintyM0 θ : ℝ) :=
  Nat.le_ceil _

theorem certainty_theta0_pos {θ : ℝ} (_hθ : 0 < θ) : 0 < certaintyTheta0 θ := by
  unfold certaintyTheta0
  have hden : (0 : ℝ) < 4 * (certaintyM0 θ : ℝ) + 2 := by positivity
  exact div_pos Real.pi_pos hden

theorem certainty_theta0_le {θ : ℝ} (hθ : 0 < θ) : certaintyTheta0 θ ≤ θ := by
  have hm := certainty_m0_lower θ
  have h4θ : (0 : ℝ) < 4 * θ := by positivity
  have hden : (0 : ℝ) < 4 * (certaintyM0 θ : ℝ) + 2 := by positivity
  have hmul : Real.pi ≤ (4 * (certaintyM0 θ : ℝ) + 2) * θ := by
    have h := hm
    rw [sub_le_iff_le_add] at h
    rw [div_le_iff₀ h4θ] at h
    nlinarith [h]
  unfold certaintyTheta0
  rw [div_le_iff₀ hden]
  nlinarith [hmul]

theorem certainty_a0_le {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ ≤ Real.pi / 2) :
    certaintyA0 θ ≤ Real.sin θ ^ 2 := by
  unfold certaintyA0
  have h0pos := certainty_theta0_pos hθ0
  have hle := certainty_theta0_le hθ0
  have hsinle : Real.sin (certaintyTheta0 θ) ≤ Real.sin θ :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos, h0pos])
      hθπ hle
  have hsinnn : 0 ≤ Real.sin (certaintyTheta0 θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (le_of_lt h0pos)
      (by linarith [hθπ, Real.pi_pos])
  exact pow_le_pow_left₀ hsinnn hsinle 2

theorem certainty_success_one (θ : ℝ) :
    Real.sin ((2 * (certaintyM0 θ : ℝ) + 1) * certaintyTheta0 θ) ^ 2 = 1 := by
  unfold certaintyTheta0
  have hden : (4 : ℝ) * (certaintyM0 θ : ℝ) + 2 ≠ 0 := by positivity
  have hangle : (2 * (certaintyM0 θ : ℝ) + 1) *
      (Real.pi / (4 * (certaintyM0 θ : ℝ) + 2)) = Real.pi / 2 := by
    field_simp
    ring
  rw [hangle, Real.sin_pi_div_two]
  norm_num

theorem source_certainty_one_success {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ ≤ Real.pi / 2) :
    certaintyA0 θ ≤ Real.sin θ ^ 2 ∧
      Real.sin ((2 * (certaintyM0 θ : ℝ) + 1) * certaintyTheta0 θ) ^ 2 = 1 :=
  ⟨certainty_a0_le hθ0 hθπ, certainty_success_one θ⟩

end Qatlib.Papers.QCounting98.MainResults
