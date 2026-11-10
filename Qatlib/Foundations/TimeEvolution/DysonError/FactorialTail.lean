/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.TimeEvolution.DysonError.SeriesSteps
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Nat.Choose.Basic

set_option autoImplicit false
namespace Qatlib.Foundations.TimeEvolution.DysonError

theorem factorial_tail_le (a : ℝ) (ha : 0 ≤ a) (K : ℕ) :
    (∑' n : ℕ, a^(n+K) / ((n+K).factorial : ℝ)) ≤
      a^K / (K.factorial : ℝ) * Real.exp a := by
  have hs := (Real.summable_pow_div_factorial a)
  have hden (n : ℕ) : (n.factorial : ℝ)*(K.factorial : ℝ) ≤ ((n+K).factorial : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add n K)
  have hpoint (n : ℕ) : a^(n+K) / ((n+K).factorial : ℝ) ≤
      a^K / (K.factorial : ℝ) * (a^n / (n.factorial : ℝ)) := by
    calc
      _ ≤ a^(n+K) / ((n.factorial:ℝ)*(K.factorial:ℝ)) :=
        div_le_div_of_nonneg_left (pow_nonneg ha _) (by positivity) (hden n)
      _ = _ := by rw [pow_add]; ring
  have ht :=
      ((summable_nat_add_iff K).2 hs).tsum_le_tsum hpoint (hs.mul_left (a^K / (K.factorial:ℝ)))
  rw [tsum_mul_left] at ht
  have he : (∑' n : ℕ, a^n / (n.factorial:ℝ)) = Real.exp a := by
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.expSeries_div_hasSum_exp a).tsum_eq
  rwa [he] at ht

theorem shifted_factorial_tail_le (a : ℝ) (ha : 0 ≤ a) (K q : ℕ) :
    (∑' n : ℕ, a^(n+K) / ((n+K+q).factorial : ℝ)) ≤
      a^K / ((K+q).factorial : ℝ) * Real.exp a := by
  have hs := Real.summable_pow_div_factorial a
  have hpoint (n : ℕ) : a^(n+K) / ((n+K+q).factorial : ℝ) ≤
      a^K / ((K+q).factorial : ℝ) * (a^n / (n.factorial : ℝ)) := by
    have hd : (n.factorial:ℝ)*((K+q).factorial:ℝ) ≤ ((n+K+q).factorial:ℝ) := by
      have hn :=
          Nat.le_of_dvd (Nat.factorial_pos _)
          (Nat.factorial_mul_factorial_dvd_factorial_add n (K+q))
      exact_mod_cast (by simpa only [Nat.add_assoc] using hn)
    calc
      _ ≤ a^(n+K) / ((n.factorial:ℝ)*((K+q).factorial:ℝ)) :=
        div_le_div_of_nonneg_left (pow_nonneg ha _) (by positivity) hd
      _ = _ := by rw [pow_add]; ring
  have ht : Summable (fun n : ℕ => a^(n+K) / ((n+K+q).factorial:ℝ)) := by
    exact Summable.of_nonneg_of_le (fun n => by positivity) hpoint
      (hs.mul_left (a^K / ((K+q).factorial:ℝ)))
  have h := ht.tsum_le_tsum hpoint (hs.mul_left (a^K / ((K+q).factorial:ℝ)))
  rw [tsum_mul_left] at h
  have he : (∑' n : ℕ, a^n / (n.factorial:ℝ)) = Real.exp a := by
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.expSeries_div_hasSum_exp a).tsum_eq
  rwa [he] at h
end Qatlib.Foundations.TimeEvolution.DysonError
