/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMatchingFlow05.SearchTools.Defs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QMatchingFlow05.SearchTools

def enumCost (c k l : ℝ) : ℝ := c * (Real.sqrt (k * l) + Real.sqrt l)

theorem enumCost_eq (c k l : ℝ) (hk : 0 ≤ k) (_hl : 0 ≤ l) :
    enumCost c k l = c * (Real.sqrt k + 1) * Real.sqrt l := by
  unfold enumCost
  rw [Real.sqrt_mul hk]
  ring

theorem enumCost_le_two_mul (c k l : ℝ) (hc : 0 ≤ c) (hk : 0 ≤ k)
    (hkl : k ≤ l) (hl1 : 1 ≤ l) :
    enumCost c k l ≤ 2 * c * l := by
  have hl : (0 : ℝ) ≤ l := by linarith
  have hle : k * l ≤ l * l := by nlinarith [hk, hl, hkl]
  have hsq : Real.sqrt (l * l) = l := by
    rw [show l * l = l ^ 2 by ring, Real.sqrt_sq hl]
  have h1 : Real.sqrt (k * l) ≤ l := by
    calc Real.sqrt (k * l) ≤ Real.sqrt (l * l) := Real.sqrt_le_sqrt hle
      _ = l := hsq
  have hll : l ≤ l * l := by nlinarith [hl1]
  have h2 : Real.sqrt l ≤ l := by
    calc Real.sqrt l ≤ Real.sqrt (l * l) := Real.sqrt_le_sqrt hll
      _ = l := hsq
  unfold enumCost
  nlinarith [hc, h1, h2, hl]

def countCost (c n : ℝ) : ℝ := c * Real.sqrt n

def countError (c n : ℝ) : ℝ := c * Real.sqrt n

theorem countCost_le_linear (c n : ℝ) (hc : 0 ≤ c) (hn : 1 ≤ n) :
    countCost c n ≤ c * n := by
  unfold countCost
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hsqrt_mul : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0
  have h1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hn
  have hsq0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg n
  have hn_ge : Real.sqrt n ≤ n := by nlinarith [hsqrt_mul, h1, hsq0]
  exact mul_le_mul_of_nonneg_left hn_ge hc

def repeatFailure (r : ℕ) : ℝ := (1 / 3 : ℝ) ^ r

theorem repeatFailure_nonneg (r : ℕ) : 0 ≤ repeatFailure r := by
  unfold repeatFailure
  positivity

theorem amplified_union_bound (t n r : ℕ) (hn : 0 < n)
    (hr : (t : ℝ) * (n : ℝ) ≤ (3 : ℝ) ^ r) :
    (t : ℝ) * repeatFailure r ≤ 1 / (n : ℝ) := by
  unfold repeatFailure
  have h3 : (0 : ℝ) < (3 : ℝ) ^ r := by positivity
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpow : (1 / 3 : ℝ) ^ r = 1 / (3 : ℝ) ^ r := by
    rw [one_div, inv_pow, one_div]
  rw [hpow, one_div, one_div]
  have hninv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  have h3inv : (0 : ℝ) ≤ ((3 : ℝ) ^ r)⁻¹ := by positivity
  have hmul : (t : ℝ) ≤ (n : ℝ)⁻¹ * (3 : ℝ) ^ r := by
    have h1 := mul_le_mul_of_nonneg_right hr hninv
    have ht : ((t : ℝ) * (n : ℝ)) * (n : ℝ)⁻¹ = (t : ℝ) := by
      rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hn'), mul_one]
    have h2 : ((3 : ℝ) ^ r) * (n : ℝ)⁻¹ = (n : ℝ)⁻¹ * (3 : ℝ) ^ r := by ring
    rwa [ht, h2] at h1
  calc (t : ℝ) * ((3 : ℝ) ^ r)⁻¹
      ≤ ((n : ℝ)⁻¹ * (3 : ℝ) ^ r) * ((3 : ℝ) ^ r)⁻¹ :=
        mul_le_mul_of_nonneg_right hmul h3inv
    _ = (n : ℝ)⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt h3), mul_one]

theorem amplified_success_bound (t n r : ℕ) (hn : 0 < n)
    (hr : (t : ℝ) * (n : ℝ) ≤ (3 : ℝ) ^ r) :
    1 - (t : ℝ) * repeatFailure r ≥ 1 - 1 / (n : ℝ) := by
  have hle := amplified_union_bound t n r hn hr
  linarith

end Qatlib.Papers.QMatchingFlow05.SearchTools

end
