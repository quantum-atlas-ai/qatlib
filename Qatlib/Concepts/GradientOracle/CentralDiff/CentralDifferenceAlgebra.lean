/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.CentralDiff.CentralDifferenceExactnessStat
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Qatlib.Concepts.GradientOracle.CentralDiff
open scoped BigOperators fwdDiff

theorem centralDiff_alternating_sign (n i : ℕ) (hi : i≤n) :
    (-1 : ℝ)^n*(-1 : ℝ)^(n-i)=(-1 : ℝ)^i := by
  have hn : (-1 : ℝ)^n=(-1 : ℝ)^(n-i)*(-1 : ℝ)^i := by
    rw [← pow_add,Nat.sub_add_cancel hi]
  have hs : (-1 : ℝ)^(n-i)*(-1 : ℝ)^(n-i)=1 := by rw [← mul_pow]; norm_num
  rw [hn]
  calc
    _ = ((-1 : ℝ)^(n-i)*(-1 : ℝ)^(n-i))*(-1 : ℝ)^i := by ring
    _ = _ := by rw [hs,one_mul]

theorem centralDiff_alternating_power_zero (n j : ℕ) (hj : j<n) (a : ℝ) :
    (∑ i ∈ Finset.range (n+1),(-1 : ℝ)^i*(Nat.choose n i : ℝ)*(a+(i : ℝ))^j)=0 := by
  have he := congrFun (fwdDiff_iter_pow_eq_zero_of_lt (R := ℝ) hj) a
  rw [fwdDiff_iter_eq_sum_shift] at he
  have hs : (∑ i ∈ Finset.range (n+1),(-1 : ℝ)^(n-i)*(Nat.choose n i : ℝ)*(a+(i : ℝ))^j)=0 := by
    simpa only [Pi.zero_apply,zsmul_eq_mul,Int.cast_mul,Int.cast_pow,Int.cast_neg,
      Int.cast_one,Int.cast_natCast,nsmul_eq_mul,mul_one] using he
  calc
    _ = (-1 : ℝ)^n*(∑ i ∈ Finset.range (n+1),(-1 : ℝ)^(n-i)*(Nat.choose n i : ℝ)*(a+(i : ℝ))^j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hsign := centralDiff_alternating_sign n i (by have := Finset.mem_range.mp hi; omega)
      rw [← hsign]
      ring
    _ = 0 := by rw [hs,mul_zero]

theorem centralDiff_choose_ratio (m l : ℕ) (hl : l≤m) :
    (Nat.choose m l : ℝ)/(Nat.choose (m+l) l : ℝ)=
      (Nat.choose (2*m) (m+l) : ℝ)/(Nat.choose (2*m) m : ℝ) := by
  have h1 : (Nat.choose (m+l) l : ℝ)≠0 := by exact_mod_cast (Nat.choose_pos (by omega : l≤m+l)).ne'
  have h2 : (Nat.choose (2*m) m : ℝ)≠0 := by exact_mod_cast (Nat.choose_pos (by omega : m≤2*m)).ne'
  apply (div_eq_div_iff h1 h2).mpr
  have he := Nat.choose_mul (n := 2*m) (k := m+l) (s := m) (by omega : m≤m+l)
  rw [Nat.choose_symm_add,show 2*m-m=m by omega,show m+l-m=l by omega] at he
  exact_mod_cast (by simpa only [mul_comm] using he.symm)
end Qatlib.Concepts.GradientOracle.CentralDiff
