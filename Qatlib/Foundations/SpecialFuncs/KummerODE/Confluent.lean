/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Confluent hypergeometric coefficients and convergence

This module defines the rising Pochhammer symbol `poch` and confluent hypergeometric
coefficients `confCoeff`. Under nonvanishing conditions on all shifted parameters, it proves the
coefficient recurrence, an eventual ratio bound, and absolute convergence at every complex
argument. These analytic estimates supply special-function infrastructure for evolution
equations; quantum annealing provides one motivating setting [KadowakiNishimori1998].

## Main statements

* `confCoeff_succ_mul`: the coefficient recurrence.
* `norm_confCoeff_ratio_eventually`: an eventual factorial-type decay bound.
* `summable_norm_confCoeff_mul_pow`: absolute convergence for every positive radius.
* `summable_confCoeff_mul_pow`: convergence at every complex argument.

## References

* [Kadowaki and Nishimori, 1998][KadowakiNishimori1998]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Foundations.SpecialFuncs.KummerODE

open Complex

/-- The rising Pochhammer symbol evaluated at the complex parameter `a`. -/
def poch (a : ℂ) (n : ℕ) : ℂ := (ascPochhammer ℂ n).eval a

/-- The rising Pochhammer symbol of order zero is one. -/
theorem poch_zero (a : ℂ) : poch a 0 = 1 := by simp [poch]

/-- The rising Pochhammer symbol satisfies `(a)_(n+1) = (a)_n * (a + n)`. -/
theorem poch_succ (a : ℂ) (n : ℕ) : poch a (n + 1) = poch a n * (a + n) := by
  simp [poch, ascPochhammer_succ_eval]

/-- Every rising Pochhammer symbol is nonzero if all factors `a + n` are nonzero. -/
theorem poch_ne_zero (a : ℂ) (ha : ∀ n : ℕ, a + n ≠ 0) (n : ℕ) : poch a n ≠ 0 := by
  induction n with
  | zero => simp [poch_zero]
  | succ k ih => rw [poch_succ]; exact mul_ne_zero ih (ha k)

/-- The coefficient `(a)_n / ((b)_n * n!)` of the confluent hypergeometric power series. -/
def confCoeff (a b : ℂ) (n : ℕ) : ℂ := poch a n * (poch b n)⁻¹ * ((n.factorial : ℂ))⁻¹

/-- The constant coefficient of the confluent hypergeometric series is one. -/
theorem confCoeff_zero (a b : ℂ) : confCoeff a b 0 = 1 := by
  simp [confCoeff, poch_zero]

/-- When `b + n` is nonzero, adjacent confluent coefficients satisfy `c_n * (a + n) = c_(n+1) *
(b + n) * (n + 1)`. -/
theorem confCoeff_succ_mul (a b : ℂ) (n : ℕ) (hb : b + n ≠ 0) :
    confCoeff a b n * (a + n) = confCoeff a b (n + 1) * ((b + n) * (n + 1)) := by
  unfold confCoeff
  rw [poch_succ, poch_succ, Nat.factorial_succ]
  push_cast
  field_simp

/-- Confluent coefficients are nonzero when every shifted numerator and denominator parameter is
nonzero. -/
theorem confCoeff_ne_zero (a b : ℂ) (ha : ∀ n : ℕ, a + n ≠ 0)
    (hb : ∀ n : ℕ, b + n ≠ 0) (n : ℕ) : confCoeff a b n ≠ 0 := by
  unfold confCoeff
  refine mul_ne_zero (mul_ne_zero (poch_ne_zero a ha n) ?_) ?_
  · exact inv_ne_zero (poch_ne_zero b hb n)
  · exact inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero n)

/-- The norms of adjacent confluent coefficients satisfy the multiplicative recurrence when `b +
n` is nonzero. -/
theorem norm_confCoeff_succ_mul (a b : ℂ) (n : ℕ) (hb : b + n ≠ 0) :
    ‖confCoeff a b (n + 1)‖ * ‖b + n‖ * (n + 1 : ℝ) = ‖confCoeff a b n‖ * ‖a + n‖ := by
  have h := confCoeff_succ_mul a b n hb
  have hnorm := congrArg norm h
  rw [norm_mul, norm_mul, norm_mul] at hnorm
  have hn : ‖((n : ℂ) + 1)‖ = (n + 1 : ℝ) := by
    rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
    push_cast
    ring
  rw [hn] at hnorm
  calc ‖confCoeff a b (n + 1)‖ * ‖b + n‖ * (n + 1 : ℝ)
      = ‖confCoeff a b (n + 1)‖ * (‖b + n‖ * (n + 1 : ℝ)) := by ring
    _ = ‖confCoeff a b n‖ * ‖a + n‖ := hnorm.symm

/-- When `b + n` is nonzero, the norm of the next coefficient equals the current norm times `‖a
+ n‖ / (‖b + n‖ * (n + 1))`. -/
theorem norm_confCoeff_succ_le (a b : ℂ) (n : ℕ) (hb : b + n ≠ 0) :
    ‖confCoeff a b (n + 1)‖
      = ‖confCoeff a b n‖ * ‖a + n‖ / (‖b + n‖ * (n + 1 : ℝ)) := by
  have h := norm_confCoeff_succ_mul a b n hb
  have hpos : 0 < ‖b + n‖ * (n + 1 : ℝ) :=
    mul_pos (norm_pos_iff.mpr hb) (by positivity)
  rw [eq_div_iff hpos.ne']
  linear_combination h

/-- The norm of a complex number plus a natural number is at most the sum of its norm and that
natural number. -/
theorem norm_add_nat_le (a : ℂ) (n : ℕ) : ‖a + n‖ ≤ ‖a‖ + n := by
  have : ((n : ℂ)) = ((n : ℝ) : ℂ) := by push_cast; ring
  rw [this]
  refine (norm_add_le a ((n : ℝ) : ℂ)).trans_eq ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- The norm of `b + n` is at least `n - ‖b‖`. -/
theorem norm_add_nat_ge (b : ℂ) (n : ℕ) : (n : ℝ) - ‖b‖ ≤ ‖b + n‖ := by
  have hle : ‖((n : ℂ))‖ ≤ ‖b + n‖ + ‖b‖ := by
    have := norm_sub_le (b + (n : ℂ)) b
    simpa using this
  have hn : ‖((n : ℂ))‖ = (n : ℝ) := Complex.norm_natCast n
  rw [hn] at hle
  linarith

/-- Under the nonvanishing shifted-parameter hypotheses, successive coefficient norms eventually
satisfy the bound with factor `4 / (n + 1)`. -/
theorem norm_confCoeff_ratio_eventually (a b : ℂ) (ha : ∀ n : ℕ, a + n ≠ 0)
    (hb : ∀ n : ℕ, b + n ≠ 0) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ‖confCoeff a b (n + 1)‖ ≤ ‖confCoeff a b n‖ * (4 / (n + 1 : ℝ)) := by
  have hbne : ∀ n : ℕ, b + n ≠ 0 := hb
  have hane : ∀ n : ℕ, a + n ≠ 0 := ha

  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N,
      (n : ℝ) / 2 ≤ ‖b + n‖ ∧ ‖a + n‖ ≤ 2 * (n : ℝ) := by
    refine ⟨⌈2 * ‖b‖⌉₊ + ⌈‖a‖⌉₊ + 2, fun n hn => ?_⟩
    constructor
    · have h1 : 2 * ‖b‖ ≤ (n : ℝ) := by
        have : (⌈2 * ‖b‖⌉₊ : ℝ) ≤ n := by exact_mod_cast (show ⌈2 * ‖b‖⌉₊ ≤ n by omega)
        have h2 : 2 * ‖b‖ ≤ (⌈2 * ‖b‖⌉₊ : ℝ) := Nat.le_ceil _
        linarith
      have h3 := norm_add_nat_ge b n
      linarith
    · have h1 : ‖a‖ ≤ (n : ℝ) := by
        have : (⌈‖a‖⌉₊ : ℝ) ≤ n := by exact_mod_cast (show ⌈‖a‖⌉₊ ≤ n by omega)
        have h2 : ‖a‖ ≤ (⌈‖a‖⌉₊ : ℝ) := Nat.le_ceil _
        linarith
      have h3 := norm_add_nat_le a n
      linarith
  filter_upwards [Filter.eventually_ge_atTop N, Filter.eventually_ge_atTop (2 : ℕ)] with n hn hn2
  obtain ⟨hden, hnum⟩ := hN n hn
  have hcn : 0 ≤ ‖confCoeff a b n‖ := norm_nonneg _
  have hbpos : 0 < ‖b + n‖ := norm_pos_iff.mpr (hbne n)
  rw [norm_confCoeff_succ_le a b n (hbne n)]
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le (by norm_num) hn2)
  have hdenpos : 0 < ‖b + n‖ * (n + 1 : ℝ) := mul_pos hbpos (by positivity)
  rw [div_le_iff₀ hdenpos]

  have hstep : ‖confCoeff a b n‖ * ‖a + n‖
      ≤ ‖confCoeff a b n‖ * (2 * (n : ℝ)) := by
    exact mul_le_mul_of_nonneg_left hnum hcn
  have hbden : (n : ℝ) ≤ 2 * ‖b + n‖ := by linarith
  have hrhs : ‖confCoeff a b n‖ * (4 / (n + 1 : ℝ)) * (‖b + n‖ * (n + 1 : ℝ))
      = 4 * ‖confCoeff a b n‖ * ‖b + n‖ := by
    field_simp
  rw [hrhs]
  nlinarith [hstep, hbden, hcn, hbpos]

/-- Every natural number, viewed as a real number, is at most its corresponding power of two. -/
theorem natCast_le_two_pow (n : ℕ) : (n : ℝ) ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
      have h2 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [hcast, pow_succ]
      nlinarith

/-- Under the nonvanishing shifted-parameter hypotheses, coefficient norms weighted by `S ^ n`
are summable for every positive real `S`. -/
theorem summable_norm_confCoeff_mul_pow (a b : ℂ) (ha : ∀ n : ℕ, a + n ≠ 0)
    (hb : ∀ n : ℕ, b + n ≠ 0) (S : ℝ) (hS : 0 < S) :
    Summable (fun n : ℕ => ‖confCoeff a b n‖ * S ^ n) := by
  refine summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num) ?_
  have hratio := norm_confCoeff_ratio_eventually a b ha hb
  have hbig : ∀ᶠ n : ℕ in Filter.atTop, 4 * S / (n + 1 : ℝ) ≤ 1 / 2 := by
    refine Filter.eventually_atTop.2 ⟨Nat.ceil (8 * S), fun n hn => ?_⟩
    have hle : 8 * S ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
    have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_le_iff₀ hnpos]
    linarith
  filter_upwards [hratio, hbig] with n hbnd hsmall
  have hcn : 0 ≤ ‖confCoeff a b n‖ := norm_nonneg _
  have hSn : 0 ≤ S ^ n := (pow_pos hS n).le
  have hn1 : ‖‖confCoeff a b (n + 1)‖ * S ^ (n + 1)‖
      = ‖confCoeff a b (n + 1)‖ * S ^ (n + 1) := Real.norm_of_nonneg (by positivity)
  have hn0 : ‖‖confCoeff a b n‖ * S ^ n‖ = ‖confCoeff a b n‖ * S ^ n :=
    Real.norm_of_nonneg (by positivity)
  rw [hn1, hn0, pow_succ]

  have hstep : ‖confCoeff a b (n + 1)‖ * (S ^ n * S)
      = ‖confCoeff a b (n + 1)‖ * S ^ n * S := by ring
  rw [hstep]
  have h1 : ‖confCoeff a b (n + 1)‖ * S ^ n * S
      ≤ (‖confCoeff a b n‖ * (4 / (n + 1 : ℝ))) * S ^ n * S :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbnd hSn) hS.le
  refine h1.trans ?_
  have h2 : (‖confCoeff a b n‖ * (4 / (n + 1 : ℝ))) * S ^ n * S
      = (‖confCoeff a b n‖ * S ^ n) * (4 * S / (n + 1 : ℝ)) := by
    field_simp
  rw [h2]
  have h3 : (‖confCoeff a b n‖ * S ^ n) * (4 * S / (n + 1 : ℝ))
      ≤ (‖confCoeff a b n‖ * S ^ n) * (1 / 2) :=
    mul_le_mul_of_nonneg_left hsmall (by positivity)
  refine h3.trans_eq ?_
  ring

/-- Under the nonvanishing shifted-parameter hypotheses, coefficient norms weighted by `n * S ^
n` are summable for every positive real `S`. -/
theorem summable_norm_confCoeff_mul_nat_mul_pow (a b : ℂ) (ha : ∀ n : ℕ, a + n ≠ 0)
    (hb : ∀ n : ℕ, b + n ≠ 0) (S : ℝ) (hS : 0 < S) :
    Summable (fun n : ℕ => ‖confCoeff a b n‖ * (n : ℝ) * S ^ n) := by
  have hdom := summable_norm_confCoeff_mul_pow a b ha hb (2 * S) (by positivity)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hdom
  have h2 : (n : ℝ) ≤ 2 ^ n := natCast_le_two_pow n
  have hSp : (0 : ℝ) ≤ S ^ n := (pow_pos hS n).le
  have hc : (0 : ℝ) ≤ ‖confCoeff a b n‖ := norm_nonneg _
  have hmul : (n : ℝ) * S ^ n ≤ 2 ^ n * S ^ n := mul_le_mul_of_nonneg_right h2 hSp
  have hkey : ‖confCoeff a b n‖ * ((n : ℝ) * S ^ n)
      ≤ ‖confCoeff a b n‖ * (2 ^ n * S ^ n) := mul_le_mul_of_nonneg_left hmul hc
  calc ‖confCoeff a b n‖ * (n : ℝ) * S ^ n
      = ‖confCoeff a b n‖ * ((n : ℝ) * S ^ n) := by ring
    _ ≤ ‖confCoeff a b n‖ * (2 ^ n * S ^ n) := hkey
    _ = ‖confCoeff a b n‖ * (2 * S) ^ n := by rw [mul_pow]

/-- Under the nonvanishing shifted-parameter hypotheses, the confluent hypergeometric power
series is summable at every complex argument. -/
theorem summable_confCoeff_mul_pow (a b : ℂ) (ha : ∀ n : ℕ, a + n ≠ 0)
    (hb : ∀ n : ℕ, b + n ≠ 0) (z : ℂ) :
    Summable (fun n : ℕ => confCoeff a b n * z ^ n) := by
  set S : ℝ := ‖z‖ + 1 with hSdef
  have hS : 0 < S := by positivity
  refine Summable.of_norm_bounded (g := fun n : ℕ => ‖confCoeff a b n‖ * S ^ n)
    (summable_norm_confCoeff_mul_pow a b ha hb S hS) (fun n => ?_)
  rw [norm_mul, norm_pow]
  have hle : ‖z‖ ≤ S := by rw [hSdef]; linarith
  have hzle : ‖z‖ ^ n ≤ S ^ n := pow_le_pow_left₀ (norm_nonneg _) hle n
  have hmul : ‖confCoeff a b n‖ * ‖z‖ ^ n ≤ ‖confCoeff a b n‖ * S ^ n :=
    mul_le_mul_of_nonneg_left hzle (norm_nonneg _)
  simpa only [norm_mul, norm_pow] using hmul

end Qatlib.Foundations.SpecialFuncs.KummerODE
