/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BoolEvalTree11.MainResults.Models
public import Mathlib.Tactic.FieldSimp

@[expose] public section


/-! # Pointwise constants cannot certify a uniform asymptotic bound

The entire literal legacy predicate is used. Its constants may be chosen after
N, so it can bound the growing function N by the constant one at every N.
No single admissible triple of constants supplies that bound uniformly.
This is a model diagnostic, not a proof of a paper probability estimate.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.BoolEvalTree11.MainResults.AsymptAudit
open Models

/-- Every point satisfies the old predicate with a separately chosen constant. -/
theorem pointwise (N : ℝ) (hN : 1≤N) : AsymptLess 1 N N 1 := by
  refine ⟨N^2,1,-1,by norm_num,by norm_num,?_⟩
  have hn : N≠0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hN)
  simp only [Nat.cast_one,Real.one_rpow,Real.rpow_neg_one,one_mul,mul_one]
  have he : N^2*N⁻¹=N := by field_simp
  rw [he]
  linarith

/-- The same bound fails for every fixed triple of admissible source constants. -/
theorem notUniform :
    ¬(∃ C α γ : ℝ, 0<α ∧ γ<0 ∧
      ∀ N : ℝ, 1≤N → N≤1*(1+C*(1:ℝ)^α*N^γ)) := by
  rintro ⟨C,α,γ,_hα,hγ,h⟩
  have hn : 1≤|C| +2 := by linarith [abs_nonneg C]
  have hp := Real.rpow_nonneg (by positivity : (0:ℝ)≤|C| +2) γ
  have hb := Real.rpow_le_one_of_one_le_of_nonpos hn (le_of_lt hγ)
  have hc : C*(|C| +2)^γ≤|C| := by
    calc
      _ ≤ |C| *(|C| +2)^γ := mul_le_mul_of_nonneg_right (le_abs_self C) hp
      _ ≤ |C| *1 := mul_le_mul_of_nonneg_left hb (abs_nonneg C)
      _ = _ := mul_one _
  have hh := h (|C| +2) hn
  simp only [Real.one_rpow,one_mul,mul_one] at hh
  linarith

/-- The literal upper predicate can fit every point with a positive comparison value. -/
theorem fitPoint (β : ℕ) (hβ : 1≤β) (N p q : ℝ) (hN : 1≤N) (hq : 0<q) :
    AsymptLess β N p q := by
  have hb : (0:ℝ)<β := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hβ)
  have hn : 0<N := lt_of_lt_of_le (by norm_num) hN
  refine ⟨(|p|/q+1)*N/(β:ℝ),1,-1,by norm_num,by norm_num,?_⟩
  simp only [Real.rpow_one,Real.rpow_neg_one]
  have he : ((|p|/q+1)*N/(β:ℝ))*(β:ℝ)*N⁻¹=|p|/q+1 := by
    field_simp
  rw [he]
  have heq : q*(1+(|p|/q+1))=2*q+|p| := by field_simp; ring
  rw [heq]
  linarith [le_abs_self p]

/-- The literal lower predicate fits every nonnegative point by making its bracket zero. -/
theorem fitLower (β : ℕ) (hβ : 1≤β) (N p q : ℝ) (hN : 1≤N) (hp : 0≤p) :
    AsymptGreater β N p q := by
  have hb : (0:ℝ)<β := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hβ)
  have hn : 0<N := lt_of_lt_of_le (by norm_num) hN
  refine ⟨N/(β:ℝ),1,-1,by norm_num,by norm_num,?_⟩
  simp only [Real.rpow_one,Real.rpow_neg_one]
  have he : (N/(β:ℝ))*(β:ℝ)*N⁻¹=1 := by field_simp
  simpa only [he,sub_self,mul_zero] using hp

/-- Every finite real quantity admits a positive pointwise factorial-style budget. -/
theorem finiteBudget (z t : ℝ) (ht : 0<t) : ∃ C : ℝ, 0<C ∧ z≤C/t := by
  refine ⟨(|z|+1)*t,mul_pos (by positivity) ht,?_⟩
  rw [mul_div_cancel_right₀ _ (ne_of_gt ht)]
  linarith [le_abs_self z]

end Qatlib.Papers.BoolEvalTree11.MainResults.AsymptAudit
