/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false

namespace CBMD

open scoped BigOperators

def kernelSquareProduct : ℕ → ℝ → ℝ
  | 0, x => x ^ 2 + 1
  | m + 1, x => kernelSquareProduct m x *
      (((x + (m + 1 : ℕ)) ^ 2 + 1) * ((x - (m + 1 : ℕ)) ^ 2 + 1))

theorem kernelSquareProduct_pos (m : ℕ) (x : ℝ) : 0 < kernelSquareProduct m x := by
  induction m with
  | zero => dsimp [kernelSquareProduct]; positivity
  | succ m ih => dsimp only [kernelSquareProduct]; positivity

theorem kernelSquareProduct_even (m : ℕ) (x : ℝ) :
    kernelSquareProduct m (-x) = kernelSquareProduct m x := by
  induction m with
  | zero => simp [kernelSquareProduct]
  | succ m ih =>
    simp only [kernelSquareProduct, ih]
    congr 1
    ring

theorem kernelSquareProduct_shift (m : ℕ) (x : ℝ) :
    kernelSquareProduct m (x + 1) * ((x - m) ^ 2 + 1) =
      kernelSquareProduct m x * ((x + m + 1) ^ 2 + 1) := by
  induction m with
  | zero => simp only [kernelSquareProduct, Nat.cast_zero]; ring
  | succ m ih =>
    simp only [kernelSquareProduct, Nat.cast_add, Nat.cast_one]
    calc
      _ = (kernelSquareProduct m (x + 1) * ((x - m) ^ 2 + 1)) *
          (((x + m + 2) ^ 2 + 1) * ((x - (m + 1)) ^ 2 + 1)) := by ring
      _ = (kernelSquareProduct m x * ((x + m + 1) ^ 2 + 1)) *
          (((x + m + 2) ^ 2 + 1) * ((x - (m + 1)) ^ 2 + 1)) := by rw [ih]
      _ = _ := by ring

theorem kernelSquareProduct_le_shift (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    kernelSquareProduct m x ≤ kernelSquareProduct m (x + 1) := by
  have hd : 0 < (x - m) ^ 2 + 1 := by positivity
  apply (mul_le_mul_iff_left₀ hd).mp
  rw [kernelSquareProduct_shift]
  apply mul_le_mul_of_nonneg_left _ (kernelSquareProduct_pos m x).le
  nlinarith [mul_nonneg hx (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

theorem kernelSquareProduct_le_nat_shift (m n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    kernelSquareProduct m x ≤ kernelSquareProduct m (x + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := kernelSquareProduct_le_shift m (x := x + n) (by positivity)
    exact ih.trans (by simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using h)

private theorem kernel_pair_lower {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (r : ℝ) :
    r ^ 4 ≤ ((x + r) ^ 2 + 1) * ((x - r) ^ 2 + 1) := by
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [mul_nonneg hx (sub_nonneg.mpr hx1)]
  nlinarith [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hx2), sq_nonneg (1 + x ^ 2)]

theorem kernelSquareProduct_lower_unit (m : ℕ) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    (m.factorial : ℝ) ^ 4 ≤ kernelSquareProduct m x := by
  induction m with
  | zero =>
    simp only [Nat.factorial_zero, Nat.cast_one, one_pow, kernelSquareProduct]
    nlinarith [sq_nonneg x]
  | succ m ih =>
    have hp := kernel_pair_lower hx hx1 ((m + 1 : ℕ) : ℝ)
    have hmul := mul_le_mul ih hp (by positivity) (kernelSquareProduct_pos m x).le
    simpa only [kernelSquareProduct, Nat.factorial_succ, Nat.cast_mul, mul_pow, mul_comm]
      using hmul

theorem kernelSquareProduct_lower (m : ℕ) (x : ℝ) :
    (m.factorial : ℝ) ^ 4 ≤ kernelSquareProduct m x := by
  have hnonneg (y : ℝ) (hy : 0 ≤ y) :
      (m.factorial : ℝ) ^ 4 ≤ kernelSquareProduct m y := by
    have hfloor := Nat.floor_le hy
    have hlt := Nat.lt_floor_add_one y
    have hy0 : 0 ≤ y - (Nat.floor y : ℝ) := by linarith
    have hy1 : y - (Nat.floor y : ℝ) ≤ 1 := by linarith
    have hb := kernelSquareProduct_lower_unit m hy0 hy1
    have hs := kernelSquareProduct_le_nat_shift m (Nat.floor y) hy0
    simpa only [sub_add_cancel] using hb.trans hs
  by_cases hx : 0 ≤ x
  · exact hnonneg x hx
  · simpa only [kernelSquareProduct_even] using hnonneg (-x) (by linarith)

theorem kernelSquareProduct_eq_int_product (m : ℕ) (x : ℝ) :
    kernelSquareProduct m x = ∏ r ∈ Finset.Icc (-(m : ℤ)) m, ((x - (r : ℝ)) ^ 2 + 1) := by
  induction m with
  | zero => simp [kernelSquareProduct]
  | succ m ih =>
    rw [Nat.cast_add, Nat.cast_one, Finset.Icc_succ_succ, Finset.prod_union (by simp)]
    rw [Finset.prod_pair (by omega), ← ih]
    simp only [kernelSquareProduct, Int.cast_neg, Int.cast_add, Int.cast_natCast,
      Int.cast_one, sub_neg_eq_add, Nat.cast_add, Nat.cast_one]

theorem integer_regulator_product_lower (m : ℕ) (x : ℝ) :
    (m.factorial : ℝ) ^ 2 ≤
      ∏ r ∈ Finset.Icc (-(m : ℤ)) m, ‖(x : ℂ) - (r : ℂ) - Complex.I‖ := by
  have hn (r : ℤ) : ‖(x : ℂ) - (r : ℂ) - Complex.I‖ ^ 2 = (x - (r : ℝ)) ^ 2 + 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.intCast_re, Complex.I_re,
      sub_zero, Complex.sub_im, Complex.ofReal_im, Complex.intCast_im, Complex.I_im]
    ring
  have he : (∏ r ∈ Finset.Icc (-(m : ℤ)) m, ‖(x : ℂ) - (r : ℂ) - Complex.I‖) ^ 2 =
      kernelSquareProduct m x := by
    rw [kernelSquareProduct_eq_int_product, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun r _ => hn r
  have hb := kernelSquareProduct_lower m x
  have hp : 0 ≤ ∏ r ∈ Finset.Icc (-(m : ℤ)) m, ‖(x : ℂ) - (r : ℂ) - Complex.I‖ :=
    Finset.prod_nonneg fun r _ => norm_nonneg _
  nlinarith [sq_nonneg ((m.factorial : ℝ) ^ 2)]

end CBMD

end Qatlib.Foundations.CbmdAnalysis.Core
