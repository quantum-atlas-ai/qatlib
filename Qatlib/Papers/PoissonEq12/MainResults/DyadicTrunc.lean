/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Order.Floor.Ring
public import Qatlib.Papers.PoissonEq12.MainResults.RepeatedSquaring

@[expose] public section

/-!
# Coordinatewise fixed-precision truncation

The arithmetic after Eq. (42) in Appendix 2 discards fractional digits
from each coordinate of a complex number. Rounding toward zero places
each coordinate on the dyadic grid, bounds its absolute error by one
grid spacing, and cannot increase the modulus.
-/

set_option autoImplicit false

noncomputable section

open Qatlib.Papers.PoissonEq12.MainResults

namespace Qatlib.Papers.PoissonEq12.MainResults

/-- The signed integer encoding of the coordinate truncated at s fractional bits. -/
def dyadicNumerator (s : ℕ) (x : ℝ) : ℤ :=
  if x < 0 then -⌊(2 : ℝ) ^ s * |x|⌋ else ⌊(2 : ℝ) ^ s * |x|⌋

/-- The real value of the signed dyadic encoding. -/
def dyadicCoord (s : ℕ) (x : ℝ) : ℝ :=
  (dyadicNumerator s x : ℝ) / (2 : ℝ) ^ s

/-- The grid projection does not increase absolute value and moves a
coordinate by at most a single grid spacing. -/
theorem dyadic_coord_bounds (s : ℕ) (x : ℝ) :
    |dyadicCoord s x| ≤ |x| ∧ |dyadicCoord s x - x| ≤ 1 / (2 : ℝ) ^ s := by
  let D : ℝ := 2 ^ s
  let q : ℝ := (⌊D * |x|⌋ : ℝ) / D
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hq : 0 ≤ q := by
    refine div_nonneg ?_ hD.le
    exact_mod_cast Int.floor_nonneg.2 (mul_nonneg hD.le (abs_nonneg x))
  have hupper : q ≤ |x| := by
    apply (div_le_iff₀ hD).2
    simpa only [mul_comm] using Int.floor_le (D * |x|)
  have hqD : q * D = (⌊D * |x|⌋ : ℝ) := div_mul_cancel₀ _ hD.ne'
  have hgap : |x| - q ≤ 1 / D := by
    apply (le_div_iff₀ hD).2
    calc
      _ = D * |x| - (⌊D * |x|⌋ : ℝ) := by nlinarith only [hqD]
      _ ≤ 1 := by linarith [Int.lt_floor_add_one (D * |x|)]
  by_cases hx : x < 0
  · have ht : dyadicCoord s x = -q := by simp [dyadicCoord, dyadicNumerator, hx, q, D, neg_div]
    rw [ht, abs_neg, abs_of_nonneg hq]
    refine ⟨hupper, ?_⟩
    have hd : -q - x = |x| - q := by
      rw [abs_of_neg hx]
      ring
    rw [hd, abs_of_nonneg (sub_nonneg.2 hupper)]
    exact hgap
  · have ht : dyadicCoord s x = q := by simp [dyadicCoord, dyadicNumerator, hx, q, D]
    rw [ht, abs_of_nonneg hq]
    refine ⟨hupper, ?_⟩
    have hd : q - x = -(|x| - q) := by
      rw [abs_of_nonneg (le_of_not_gt hx)]
      ring
    rw [hd, abs_neg, abs_of_nonneg (sub_nonneg.2 hupper)]
    exact hgap

/-- Truncate both complex coordinates toward zero with s fractional bits. -/
def towardZeroDyadicTruncation (s : ℕ) : BitTruncation s where
  trunc z := ⟨dyadicCoord s z.re, dyadicCoord s z.im⟩
  trunc_close z := by
    have hre := pow_le_pow_left₀ (abs_nonneg _) (dyadic_coord_bounds s z.re).2 2
    have him := pow_le_pow_left₀ (abs_nonneg _) (dyadic_coord_bounds s z.im).2 2
    rw [sq_abs, div_pow, one_pow] at hre him
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [Complex.sq_norm, Complex.normSq_apply, div_pow, Real.sq_sqrt (by norm_num)]
    simp only [Complex.sub_re, Complex.sub_im]
    rw [← pow_two, ← pow_two]
    calc
      _ ≤ 1 / ((2 : ℝ) ^ s) ^ 2 + 1 / ((2 : ℝ) ^ s) ^ 2 := add_le_add hre him
      _ = _ := by rw [← add_div, one_add_one_eq_two]
  trunc_contract z := by
    have hre := pow_le_pow_left₀ (abs_nonneg _) (dyadic_coord_bounds s z.re).1 2
    have him := pow_le_pow_left₀ (abs_nonneg _) (dyadic_coord_bounds s z.im).1 2
    rw [sq_abs, sq_abs] at hre him
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [Complex.sq_norm, Complex.normSq_apply, ← pow_two]
    linarith

/-- Instantiate the repeated-squaring error bound with actual signed
dyadic truncation at each step of the existing recurrence. -/
theorem dyadic_repeated_squaring_error {ν s : ℕ} {y : ℝ}
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ‖wQuad y ^ 2 ^ (ν + 7) -
      repeatedSquaring (towardZeroDyadicTruncation s) (wQuad y) (ν + 7)‖
      ≤ (2 : ℝ) ^ (ν + 9) / 2 ^ s :=
  prop1 (towardZeroDyadicTruncation s) hy0 hy1

end Qatlib.Papers.PoissonEq12.MainResults
