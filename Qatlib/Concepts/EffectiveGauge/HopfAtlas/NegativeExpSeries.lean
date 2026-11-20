/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.EffectiveGauge.RationalFlow.ArctanProgram
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

/-! # The actual alternating prefix used by exp_negative -/

set_option autoImplicit false
open scoped BigOperators
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of negative Exp Partial in the Hopf Atlas construction. -/
def negativeExpPartial (x : ℚ) (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n, (-x)^j/(j.factorial : ℚ)

/-- Definition of negative Exp Magnitude in the Hopf Atlas construction. -/
def negativeExpMagnitude (x : ℚ) (n : ℕ) : ℚ := |x|^n/(n.factorial : ℚ)

/-- The rational partial exponential sum with zero terms is zero. -/
@[simp] theorem negativeExpPartial_zero (x : ℚ) : negativeExpPartial x 0=0 := rfl

/-- Extending the rational partial sum by one term adds `(-x)^n / n!` to its order-`n` value. -/
theorem negativeExpPartial_succ (x : ℚ) (n : ℕ) :
    negativeExpPartial x (n+1)=negativeExpPartial x n+(-x)^n/(n.factorial : ℚ) := Finset.sum_range_succ _ _

/-- When `|x| ≤ 1/2`, the magnitude of the order-`n` rational exponential term is at most `2⁻ⁿ`. -/
theorem negativeExpMagnitude_dyadic (x : ℚ) (hx : |x| ≤ (1/2 : ℚ)) (n : ℕ) :
    negativeExpMagnitude x n ≤ (2^n : ℚ)⁻¹ := by
  calc
    _ ≤ |x|^n := div_le_self (by positivity) (by exact_mod_cast Nat.factorial_pos n)
    _ ≤ (1/2 : ℚ)^n := pow_le_pow_left₀ (abs_nonneg _) hx n
    _ = _ := by rw [one_div,inv_pow]

noncomputable section

/-- For `0 ≤ x ≤ 1`, the error of the first `n` terms of the alternating series for `exp (-x)` is
at most `x^n / n!`. -/
private theorem negativeExpSeries_error (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    |Real.exp (-x)-(∑ j ∈ Finset.range n, (-x)^j/(j.factorial : ℝ))| ≤ x^n/(n.factorial : ℝ) := by
  let f := fun j : ℕ => x^j/(j.factorial : ℝ)
  have hterm (j : ℕ) : (-x)^j/(j.factorial : ℝ)=(-1 : ℝ)^j*f j := by
    dsimp only [f]
    rw [show -x=(-1 : ℝ)*x by ring,mul_pow]
    ring
  have hs : HasSum (fun j => (-1 : ℝ)^j*f j) (Real.exp (-x)) := by
    have h : HasSum (fun j : ℕ => (-x)^j/(j.factorial : ℝ)) (Real.exp (-x)) := by
      simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (-x)
    have hf : (fun j : ℕ => (-x)^j/(j.factorial : ℝ))=(fun j => (-1 : ℝ)^j*f j) := funext hterm
    rw [hf] at h
    exact h
  have hsum : Summable f := by
    have h := hs.summable.norm
    simpa [f,norm_mul,norm_pow,norm_div,Real.norm_eq_abs,abs_of_nonneg hx] using h
  have hanti : Antitone f := by
    apply antitone_nat_of_succ_le
    intro j
    change x^(j+1)/((j+1).factorial : ℝ) ≤ x^j/(j.factorial : ℝ)
    calc
      _ ≤ x^j/((j+1).factorial : ℝ) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        rw [pow_succ]
        exact mul_le_of_le_one_right (pow_nonneg hx _) hx1
      _ ≤ _ := div_le_div_of_nonneg_left (pow_nonneg hx _) (by positivity)
        (by exact_mod_cast Nat.factorial_le (Nat.le_succ j))
  have h := alternating_series_error_bound f hanti hsum n
  rw [hs.tsum_eq] at h
  have hsum_eq : (∑ j ∈ Finset.range n, (-x)^j/(j.factorial : ℝ))=
      ∑ j ∈ Finset.range n, (-1 : ℝ)^j*f j := Finset.sum_congr rfl (fun j _ => hterm j)
  rw [hsum_eq]
  exact h

/-- For rational `x ∈ [0, 1/2]`, the real error of the rational partial sum for `exp (-x)` is at
most the magnitude of the first omitted term. -/
theorem negativeExpPartial_error (x : ℚ) (hx : 0 ≤ x) (hx1 : x ≤ 1/2) (n : ℕ) :
    |(negativeExpPartial x n : ℝ)-Real.exp (-(x : ℝ))| ≤ (negativeExpMagnitude x n : ℝ) := by
  have hxR : (0 : ℝ) ≤ x := by exact_mod_cast hx
  have hx1R : (x : ℝ) ≤ 1 := by exact_mod_cast (show x ≤ 1 by linarith)
  have h := negativeExpSeries_error (x : ℝ) hxR hx1R n
  rw [abs_sub_comm] at h
  simpa [negativeExpPartial,negativeExpMagnitude,abs_of_nonneg hx] using h

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
