/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section


/-! # The concrete binomial ratio in the bosonic birthday count

The ratio is expanded as actual falling factorials. Each denominator is
at least the positive mode count; Bernoulli's inequality then gives a
strictly stronger lower bound than one minus n squared over m.
-/

set_option autoImplicit false
open scoped BigOperators
namespace Qatlib.Concepts.BosonFock.BosonOperators.ChooseRatio

/-- The actual stars-and-bars ratio exceeds one minus the squared particle-to-mode budget. -/
theorem lowerBound (m n : ℕ) (hm : 0 < m) (hn1 : 1 ≤ n) (hn : n ≤ m) :
    1 - (n : ℝ)^2/(m : ℝ) < (m.choose n : ℝ)/((m+n-1).choose n : ℝ) := by
  let L := m+n-1
  let x : ℝ := (n-1 : ℕ)/(m : ℝ)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hx0 : 0 ≤ x := div_nonneg (Nat.cast_nonneg _) hmR.le
  have hx1 : x ≤ 1 := by
    apply (div_le_one hmR).mpr
    exact_mod_cast (show n-1 ≤ m by omega)
  have hL : (L : ℝ) = (m : ℝ)+(n : ℝ)-1 := by
    dsimp [L]
    rw [Nat.cast_sub (by omega : 1 ≤ m+n)]
    push_cast
    ring
  have hxm : x * (m : ℝ) = (n-1 : ℕ) := by
    dsimp [x]
    exact div_mul_cancel₀ _ hmR.ne'
  have he : (m.choose n : ℝ)/(L.choose n : ℝ) =
      ∏ i ∈ Finset.range n, ((m-i : ℕ) : ℝ)/((L-i : ℕ) : ℝ) := by
    have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    calc
      _ = ((n.factorial : ℝ)*(m.choose n : ℝ))/
          ((n.factorial : ℝ)*(L.choose n : ℝ)) := (mul_div_mul_left _ _ hf).symm
      _ = (m.descFactorial n : ℝ)/(L.descFactorial n : ℝ) := by
        simp only [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
      _ = _ := by
        simp only [Nat.descFactorial_eq_prod_range, Nat.cast_prod, Finset.prod_div_distrib]
  have hp : (1-x)^n ≤ ∏ i ∈ Finset.range n, ((m-i : ℕ) : ℝ)/((L-i : ℕ) : ℝ) := by
    have hc : (1-x)^n = ∏ _i ∈ Finset.range n, (1-x) := by simp
    rw [hc]
    apply Finset.prod_le_prod₀
    · intro i _
      exact sub_nonneg.mpr hx1
    · intro i hi
      have hin := Finset.mem_range.mp hi
      have hmi : i ≤ m := by omega
      have hLi : i ≤ L := by dsimp [L]; omega
      have hdm : m ≤ L-i := by dsimp [L]; omega
      have hdR : (m : ℝ) ≤ ((L-i : ℕ) : ℝ) := by exact_mod_cast hdm
      have hdpos : (0 : ℝ) < ((L-i : ℕ) : ℝ) := hmR.trans_le hdR
      apply (le_div_iff₀ hdpos).mpr
      have hxden := mul_le_mul_of_nonneg_left hdR hx0
      rw [hxm] at hxden
      have hdiff : (((L-i : ℕ) : ℝ))-(((m-i : ℕ) : ℝ)) = ((n-1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hLi, Nat.cast_sub hmi, hL, Nat.cast_sub hn1]
        norm_num
        ring
      nlinarith
  have hb : 1 - (n : ℝ)*x ≤ (1-x)^n := by
    have hz := one_add_mul_le_pow (a := -x) (by linarith : (-2 : ℝ) ≤ -x) n
    simpa only [← sub_eq_add_neg, mul_neg] using hz
  have hstrict : 1 - (n : ℝ)^2/(m : ℝ) < 1 - (n : ℝ)*x := by
    dsimp [x]
    rw [Nat.cast_sub hn1]
    norm_num
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    rw [← mul_div_assoc]
    apply (div_lt_div_iff_of_pos_right hmR).mpr
    nlinarith
  exact hstrict.trans_le (hb.trans (hp.trans_eq he.symm))

end Qatlib.Concepts.BosonFock.BosonOperators.ChooseRatio
