/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BoolEvalTree11.MainResults.Models

@[expose] public section


/-! # The genuine old equal-marginal arithmetic

This preserves the entire old closed result. It does not derive the source's
l<k conditional equal marginals from its actual hard-tree distribution.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.BoolEvalTree11.MainResults.EqualBias
open Models
/-- Equal half-vote marginals have bias one and cannot trigger the old TypeIII threshold. -/
theorem halfVote (β : ℕ) (hβ : 2 ≤ β)
    (pb₀ pb₁ : ℝ) (hpb : 0 < pb₀ + pb₁) :
    ¬ IsTypeIII β (pb₀ * (1 / 2) + pb₁ * (1 / 2)) ((pb₀ + pb₁) / 2) := by
  intro h
  unfold IsTypeIII biasRatio at h
  have hne : pb₀ + pb₁ ≠ 0 := ne_of_gt hpb
  have hratio : (pb₀ * (1 / 2) + pb₁ * (1 / 2)) / ((pb₀ + pb₁) / 2) = 1 := by
    have hnum : pb₀ * (1 / 2) + pb₁ * (1 / 2) = (pb₀ + pb₁) / 2 := by ring
    rw [hnum, div_self]
    exact div_ne_zero hne (by norm_num)
  rw [hratio] at h
  have hβ2 : (2 : ℝ) ≤ (β : ℝ) := by exact_mod_cast hβ
  have hβpos : (0 : ℝ) < (β : ℝ) := by linarith
  have hcube : (8 : ℝ) ≤ (β : ℝ) ^ 3 := by
    have h2 : (2 : ℝ) ^ 3 ≤ (β : ℝ) ^ 3 :=
      pow_le_pow_left₀ (by norm_num) hβ2 3
    norm_num at h2
    exact h2
  have hpowle : (β : ℝ) ^ (-(3 : ℝ)) ≤ (1 / 8 : ℝ) := by
    have h1 : (β : ℝ) ^ (-(3 : ℝ)) = ((β : ℝ) ^ 3)⁻¹ := by
      rw [Real.rpow_neg (le_of_lt hβpos) (3 : ℝ)]
      congr 1
      exact Real.rpow_natCast (β : ℝ) 3
    rw [h1]
    have h8 : (1 : ℝ) / (β : ℝ) ^ 3 ≤ 1 / 8 :=
      one_div_le_one_div_of_le (by norm_num) hcube
    simpa [one_div] using h8
  have hle : 2 * (β : ℝ) ^ (-(3 : ℝ)) ≤ 2 * (1 / 8 : ℝ) := by linarith
  norm_num at hle
  linarith
end Qatlib.Papers.BoolEvalTree11.MainResults.EqualBias
