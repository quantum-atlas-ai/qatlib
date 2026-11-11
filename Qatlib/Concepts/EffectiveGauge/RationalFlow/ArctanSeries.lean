/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! # Exact rational arctan sums and their true real error -/

set_option autoImplicit false
open scoped BigOperators
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of arctan Partial in the Rational Flow construction. -/
def arctanPartial (x : ℚ) (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n, (-1 : ℚ)^j*x^(2*j+1)/((2*j+1 : ℕ) : ℚ)

/-- Definition of arctan Term Magnitude in the Rational Flow construction. -/
def arctanTermMagnitude (x : ℚ) (n : ℕ) : ℚ := |x|^(2*n+1)/((2*n+1 : ℕ) : ℚ)

/-- Original `arctanPartial_zero` guarantee for the `ArctanSeries` construction; the complete source hypotheses are retained. -/
@[simp] theorem arctanPartial_zero (x : ℚ) : arctanPartial x 0=0 := rfl

/-- Original `arctanPartial_succ` guarantee for the `ArctanSeries` construction; the complete source hypotheses are retained. -/
theorem arctanPartial_succ (x : ℚ) (n : ℕ) : arctanPartial x (n+1)=
    arctanPartial x n+(-1 : ℚ)^n*x^(2*n+1)/((2*n+1 : ℕ) : ℚ) := Finset.sum_range_succ _ _

/-- Original `arctanPartial_neg` guarantee for the `ArctanSeries` construction; the complete source hypotheses are retained. -/
theorem arctanPartial_neg (x : ℚ) (n : ℕ) : arctanPartial (-x) n= -arctanPartial x n := by
  rw [arctanPartial,arctanPartial,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [(show Odd (2*j+1) from ⟨j,by omega⟩).neg_pow]
  ring

noncomputable section

/-- Original `arctanSeries_error_nonneg` guarantee for the `ArctanSeries` construction; the complete source hypotheses are retained. -/
private theorem arctanSeries_error_nonneg (x : ℝ) (hx : 0 ≤ x) (hx1 : x<1) (n : ℕ) :
    |Real.arctan x-(∑ j ∈ Finset.range n, (-1 : ℝ)^j*x^(2*j+1)/((2*j+1 : ℕ) : ℝ))| ≤
      x^(2*n+1)/((2*n+1 : ℕ) : ℝ) := by
  let f := fun j : ℕ => x^(2*j+1)/((2*j+1 : ℕ) : ℝ)
  have hs : HasSum (fun j : ℕ => (-1 : ℝ)^j*f j) (Real.arctan x) := by
    simpa only [f,mul_div_assoc] using Real.hasSum_arctan (by simpa only [Real.norm_eq_abs,abs_of_nonneg hx] using hx1)
  have hden (j : ℕ) : |(2 : ℝ)*j+1|=2*j+1 := abs_of_nonneg (by positivity)
  have hsum : Summable f := by
    simpa [f,norm_mul,norm_pow,norm_div,Real.norm_eq_abs,abs_of_nonneg hx,hden] using hs.summable.norm
  have hanti : Antitone f := by
    apply antitone_nat_of_succ_le
    intro j
    have hp : x^(2*(j+1)+1) ≤ x^(2*j+1) := by
      rw [show 2*(j+1)+1=(2*j+1)+2 by omega,pow_add]
      nlinarith [mul_nonneg (pow_nonneg hx (2*j+1)) (show 0 ≤ 1-x^2 by nlinarith)]
    calc
      _ ≤ x^(2*j+1)/((2*(j+1)+1 : ℕ) : ℝ) := div_le_div_of_nonneg_right hp (by positivity)
      _ ≤ x^(2*j+1)/((2*j+1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_left (pow_nonneg hx _) (by positivity) (by exact_mod_cast (by omega : 2*j+1 ≤ 2*(j+1)+1))
  have he := alternating_series_error_bound f hanti hsum n
  rw [hs.tsum_eq] at he
  simpa only [f,mul_div_assoc] using he

/-- Original `arctanPartial_error` guarantee for the `ArctanSeries` construction; the complete source hypotheses are retained. -/
theorem arctanPartial_error (x : ℚ) (hx : |x| ≤ (1/2 : ℚ)) (n : ℕ) :
    |(arctanPartial x n : ℝ)-Real.arctan (x : ℝ)| ≤ (arctanTermMagnitude x n : ℝ) := by
  by_cases hpos : 0 ≤ x
  · have hp : (0 : ℝ) ≤ x := by exact_mod_cast hpos
    have hhalf : |(x : ℝ)| ≤ (1/2 : ℝ) := by
      have h : ((|x| : ℚ) : ℝ) ≤ (((1/2 : ℚ) : ℝ)) := Rat.cast_le.mpr hx
      push_cast at h
      exact h
    have he := arctanSeries_error_nonneg (x : ℝ) hp (by rw [abs_of_nonneg hp] at hhalf; linarith) n
    rw [abs_sub_comm] at he
    simpa [arctanPartial,arctanTermMagnitude,abs_of_nonneg hpos,abs_of_nonneg hp] using he
  · have hn : 0 ≤ -x := neg_nonneg.mpr (le_of_not_ge hpos)
    have hhalf : |((-x : ℚ) : ℝ)| ≤ (1/2 : ℝ) := by
      have h : ((|-x| : ℚ) : ℝ) ≤ (((1/2 : ℚ) : ℝ)) := Rat.cast_le.mpr (by simpa only [abs_neg] using hx)
      push_cast at h
      simpa only [Rat.cast_neg] using h
    have hp : (0 : ℝ) ≤ (-x : ℚ) := by exact_mod_cast hn
    have he := arctanSeries_error_nonneg ((-x : ℚ) : ℝ) hp (by rw [abs_of_nonneg hp] at hhalf; linarith) n
    have hsneg : ((arctanPartial (-x) n : ℚ) : ℝ)= -(arctanPartial x n : ℝ) := by rw [arctanPartial_neg,Rat.cast_neg]
    have hsum : (∑ j ∈ Finset.range n, (-1 : ℝ)^j*((-x : ℚ) : ℝ)^(2*j+1)/((2*j+1 : ℕ) : ℝ))=
        (arctanPartial (-x) n : ℝ) := by simp [arctanPartial]
    rw [hsum,hsneg,Rat.cast_neg,Real.arctan_neg] at he
    simpa [arctanTermMagnitude,abs_of_nonpos (le_of_not_ge hpos),sub_eq_add_neg,add_comm] using he

end
end Qatlib.Concepts.EffectiveGauge.RationalFlow
