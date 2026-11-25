/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-!
# The own-edge term in the weight derivative

The first case in Lemma 3 differentiates the weight multiplied by
its sine phase. The phase argument includes the angle factor in
both terms. The two trigonometric bounds give a global estimate
and a sharper estimate near zero.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QAOAWeighted24.MainResults

/-- Bound the differentiated sine factor using the magnitude of its
sine and the magnitude of its argument. -/
theorem own_edge_core_le (x : ℝ) :
    |Real.sin x + x * Real.cos x| ≤ |Real.sin x| + |x| := by
  calc
    _ ≤ |Real.sin x| + |x * Real.cos x| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul]
      have h := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one x) (abs_nonneg x)
      rw [mul_one] at h
      exact add_le_add le_rfl h

/-- The own-edge trigonometric derivative factor has a uniform additive
bound for nonnegative angle. -/
theorem own_edge_deriv_bound (w γ : ℝ) (hγ : 0 ≤ γ) :
    |Real.sin (w * γ) + w * γ * Real.cos (w * γ)| ≤ 1 + γ * |w| := by
  refine (own_edge_core_le (w * γ)).trans ?_
  rw [abs_mul, abs_of_nonneg hγ, mul_comm γ]
  exact add_le_add (Real.abs_sin_le_one _) le_rfl

/-- For angles between zero and one, the sharper sine bound implies
the linear coefficient used for the own-edge part of Lemma 3. -/
theorem own_edge_deriv_unit_angle (w γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    |Real.sin (w * γ) + w * γ * Real.cos (w * γ)| ≤ (1 + γ) * |w| := by
  calc
    _ ≤ |Real.sin (w * γ)| + |w * γ| := own_edge_core_le _
    _ ≤ |w * γ| + |w * γ| := add_le_add Real.abs_sin_le_abs le_rfl
    _ ≤ _ := by
      rw [abs_mul, abs_of_nonneg hγ0]
      nlinarith [mul_le_mul_of_nonneg_right hγ1 (abs_nonneg w)]

end Qatlib.Papers.QAOAWeighted24.MainResults
