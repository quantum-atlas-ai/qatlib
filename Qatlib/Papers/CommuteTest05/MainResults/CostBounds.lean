/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.CommuteTest05.MainResults.CostBounds

def szegedyTime (δ ε : ℝ) : ℝ := 1 / Real.sqrt (δ * ε)

def alg4Cost (k n r : ℝ) : ℝ := r * n ^ 2 + (k / Real.sqrt r) * n ^ 2

def alg5Cost (k n r : ℝ) : ℝ := r * n + n ^ 3 * k ^ 2 / r ^ ((3 : ℝ) / 2)

def alg6Cost (k n r : ℝ) : ℝ := r ^ 2 * n + 2 * k * n ^ 2 / Real.sqrt r

theorem rpow_mul_add (x : ℝ) (hx : 0 < x) (a b : ℝ) :
    x ^ a * x ^ b = x ^ (a + b) := (Real.rpow_add hx a b).symm

theorem rpow_pow_mul (x : ℝ) (hx : 0 < x) (a b : ℝ) :
    (x ^ a) ^ b = x ^ (a * b) := (Real.rpow_mul hx.le a b).symm

theorem sqrt_rpow_two_thirds (x : ℝ) (hx : 0 < x) :
    Real.sqrt (x ^ ((2 : ℝ) / 3)) = x ^ ((1 : ℝ) / 3) := by
  rw [Real.sqrt_eq_rpow, rpow_pow_mul x hx]
  norm_num

theorem div_rpow_third (x : ℝ) (hx : 0 < x) :
    x / x ^ ((1 : ℝ) / 3) = x ^ ((2 : ℝ) / 3) := by
  rw [div_eq_iff (Real.rpow_pos_of_pos hx _).ne',
    rpow_mul_add x hx ((2 : ℝ) / 3) ((1 : ℝ) / 3)]
  rw [show (2 : ℝ) / 3 + 1 / 3 = 1 by norm_num, Real.rpow_one]

theorem alg4Cost_at_optimal (k n : ℝ) (hk : 0 < k) :
    alg4Cost k n (k ^ ((2 : ℝ) / 3)) = 2 * k ^ ((2 : ℝ) / 3) * n ^ 2 := by
  unfold alg4Cost
  rw [sqrt_rpow_two_thirds k hk, div_rpow_third k hk]
  ring

theorem alg4Cost_bound (k n : ℝ) (hk : 0 < k) :
    alg4Cost k n (k ^ ((2 : ℝ) / 3)) ≤ 2 * (k ^ ((2 : ℝ) / 3) * n ^ 2) := by
  rw [alg4Cost_at_optimal k n hk]
  exact le_of_eq (by ring)

theorem alg5_rpow_three_halves (k n : ℝ) (hk : 0 < k) (hn : 0 < n) :
    (k ^ ((4 : ℝ) / 5) * n ^ ((4 : ℝ) / 5)) ^ ((3 : ℝ) / 2) =
      k ^ ((6 : ℝ) / 5) * n ^ ((6 : ℝ) / 5) := by
  rw [Real.mul_rpow (Real.rpow_nonneg hk.le _) (Real.rpow_nonneg hn.le _)]
  rw [rpow_pow_mul k hk, rpow_pow_mul n hn]
  norm_num

theorem alg5Cost_at_optimal (k n : ℝ) (hk : 0 < k) (hn : 0 < n) :
    alg5Cost k n (k ^ ((4 : ℝ) / 5) * n ^ ((4 : ℝ) / 5)) =
      2 * (k ^ ((4 : ℝ) / 5) * n ^ ((9 : ℝ) / 5)) := by
  unfold alg5Cost
  have h32 := alg5_rpow_three_halves k n hk hn
  have hn1 : n ^ ((4 : ℝ) / 5) * n = n ^ ((9 : ℝ) / 5) := by
    have h := Real.rpow_add hn ((4 : ℝ) / 5) 1
    rw [show (4 : ℝ) / 5 + 1 = 9 / 5 by norm_num, Real.rpow_one] at h
    exact h.symm
  have hfirst : k ^ ((4 : ℝ) / 5) * n ^ ((4 : ℝ) / 5) * n =
      k ^ ((4 : ℝ) / 5) * n ^ ((9 : ℝ) / 5) := by
    rw [mul_assoc, hn1]
  have hk2 : k ^ ((4 : ℝ) / 5) * k ^ ((6 : ℝ) / 5) = k ^ 2 := by
    have h := Real.rpow_add hk ((4 : ℝ) / 5) ((6 : ℝ) / 5)
    rw [show (4 : ℝ) / 5 + 6 / 5 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
    exact h.symm
  have hn2 : n ^ ((4 : ℝ) / 5) * n ^ ((6 : ℝ) / 5) = n ^ 2 := by
    have h := Real.rpow_add hn ((4 : ℝ) / 5) ((6 : ℝ) / 5)
    rw [show (4 : ℝ) / 5 + 6 / 5 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
    exact h.symm
  have hn3 : n ^ 3 = n ^ ((9 : ℝ) / 5) * n ^ ((6 : ℝ) / 5) := by
    have h := Real.rpow_add hn ((9 : ℝ) / 5) ((6 : ℝ) / 5)
    rw [show (9 : ℝ) / 5 + 6 / 5 = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
    exact h
  have hterm : n ^ 3 * k ^ 2 / (k ^ ((6 : ℝ) / 5) * n ^ ((6 : ℝ) / 5)) =
      k ^ ((4 : ℝ) / 5) * n ^ ((9 : ℝ) / 5) := by
    rw [div_eq_iff (by positivity : k ^ ((6 : ℝ) / 5) * n ^ ((6 : ℝ) / 5) ≠ 0)]
    have hR : k ^ ((4 : ℝ) / 5) * n ^ ((9 : ℝ) / 5) *
        (k ^ ((6 : ℝ) / 5) * n ^ ((6 : ℝ) / 5)) = n ^ 3 * k ^ 2 := by
      have e : k ^ ((4 : ℝ) / 5) * n ^ ((9 : ℝ) / 5) *
          (k ^ ((6 : ℝ) / 5) * n ^ ((6 : ℝ) / 5)) =
          (k ^ ((4 : ℝ) / 5) * k ^ ((6 : ℝ) / 5)) *
            (n ^ ((9 : ℝ) / 5) * n ^ ((6 : ℝ) / 5)) := by ring
      rw [e, hk2, ← hn3]
      ring
    rw [hR]
  rw [h32, hfirst, hterm]
  ring

theorem alg5Cost_bound (k n : ℝ) (hk : 0 < k) (hn : 1 ≤ n) :
    alg5Cost k n (k ^ ((4 : ℝ) / 5) * n ^ ((4 : ℝ) / 5)) ≤
      2 * (k ^ ((4 : ℝ) / 5) * n ^ ((9 : ℝ) / 5)) := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  rw [alg5Cost_at_optimal k n hk hn0]

theorem alg6Cost_at_optimal (k n : ℝ) (hk : 0 < k) (hn : 0 < n) :
    alg6Cost k n (k ^ ((2 : ℝ) / 5) * n ^ ((2 : ℝ) / 5)) =
      3 * (k ^ ((4 : ℝ) / 5) * n ^ ((9 : ℝ) / 5)) := by
  unfold alg6Cost
  have hs : Real.sqrt (k ^ ((2 : ℝ) / 5) * n ^ ((2 : ℝ) / 5)) =
      k ^ ((1 : ℝ) / 5) * n ^ ((1 : ℝ) / 5) := by
    rw [Real.sqrt_eq_rpow,
      Real.mul_rpow (Real.rpow_nonneg hk.le _) (Real.rpow_nonneg hn.le _)]
    rw [rpow_pow_mul k hk, rpow_pow_mul n hn]
    norm_num
  have hk44 : k ^ ((2 : ℝ) / 5) * k ^ ((2 : ℝ) / 5) = k ^ ((4 : ℝ) / 5) := by
    rw [rpow_mul_add k hk]; norm_num
  have hn44 : n ^ ((2 : ℝ) / 5) * n ^ ((2 : ℝ) / 5) = n ^ ((4 : ℝ) / 5) := by
    rw [rpow_mul_add n hn]; norm_num
  have hn1 : n ^ ((4 : ℝ) / 5) * n = n ^ ((9 : ℝ) / 5) := by
    have h := Real.rpow_add hn ((4 : ℝ) / 5) 1
    rw [show (4 : ℝ) / 5 + 1 = 9 / 5 by norm_num, Real.rpow_one] at h
    exact h.symm
  have hsq : (k ^ ((2 : ℝ) / 5) * n ^ ((2 : ℝ) / 5)) ^ 2 * n =
      k ^ ((4 : ℝ) / 5) * n ^ ((9 : ℝ) / 5) := by
    rw [mul_pow, pow_two (k ^ ((2 : ℝ) / 5)), pow_two (n ^ ((2 : ℝ) / 5)),
      hk44, hn44, mul_assoc, hn1]
  rw [hs, hsq]
  have hk1 : k ^ ((4 : ℝ) / 5) * k ^ ((1 : ℝ) / 5) = k := by
    have h := Real.rpow_add hk ((4 : ℝ) / 5) ((1 : ℝ) / 5)
    rw [show (4 : ℝ) / 5 + 1 / 5 = 1 by norm_num, Real.rpow_one] at h
    exact h.symm
  have hn1' : n ^ ((9 : ℝ) / 5) * n ^ ((1 : ℝ) / 5) = n ^ 2 := by
    have h := Real.rpow_add hn ((9 : ℝ) / 5) ((1 : ℝ) / 5)
    rw [show (9 : ℝ) / 5 + 1 / 5 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
    exact h.symm
  have hkdiv : 2 * k * n ^ 2 / (k ^ ((1 : ℝ) / 5) * n ^ ((1 : ℝ) / 5)) =
      2 * (k ^ ((4 : ℝ) / 5) * n ^ ((9 : ℝ) / 5)) := by
    rw [div_eq_iff (by positivity : k ^ ((1 : ℝ) / 5) * n ^ ((1 : ℝ) / 5) ≠ 0)]
    have hR : k ^ ((4 : ℝ) / 5) * n ^ ((9 : ℝ) / 5) *
        (k ^ ((1 : ℝ) / 5) * n ^ ((1 : ℝ) / 5)) = k * n ^ 2 := by
      have e : k ^ ((4 : ℝ) / 5) * n ^ ((9 : ℝ) / 5) *
          (k ^ ((1 : ℝ) / 5) * n ^ ((1 : ℝ) / 5)) =
          (k ^ ((4 : ℝ) / 5) * k ^ ((1 : ℝ) / 5)) *
            (n ^ ((9 : ℝ) / 5) * n ^ ((1 : ℝ) / 5)) := by ring
      rw [e, hk1, hn1']
    have hgoal : 2 * k * n ^ 2 = 2 * (k * n ^ 2) := by ring
    rw [hgoal, ← hR]
    ring
  rw [hkdiv]
  ring

theorem alg6Cost_bound (k n : ℝ) (hk : 0 < k) (hn : 0 < n) :
    alg6Cost k n (k ^ ((2 : ℝ) / 5) * n ^ ((2 : ℝ) / 5)) ≤
      3 * (k ^ ((4 : ℝ) / 5) * n ^ ((9 : ℝ) / 5)) := by
  rw [alg6Cost_at_optimal k n hk hn]

def directBound (k n : ℝ) : ℝ := k * n ^ ((5 : ℝ) / 3)

def collisionBound (k n : ℝ) : ℝ := k ^ ((2 : ℝ) / 3) * n ^ 2

def twoLevelBound (k n : ℝ) : ℝ := k ^ ((4 : ℝ) / 5) * n ^ ((9 : ℝ) / 5)

theorem regime_small (k n : ℝ) (hk : 1 ≤ k) (hn : 1 ≤ n)
    (hkn : k ≤ n ^ ((2 : ℝ) / 3)) :
    directBound k n ≤ twoLevelBound k n := by
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hkpow : k ^ ((1 : ℝ) / 5) ≤ n ^ ((2 : ℝ) / 15) := by
    have h1 : k ^ ((1 : ℝ) / 5) ≤ (n ^ ((2 : ℝ) / 3)) ^ ((1 : ℝ) / 5) :=
      Real.rpow_le_rpow hk0.le hkn (by norm_num)
    have h2 : (n ^ ((2 : ℝ) / 3)) ^ ((1 : ℝ) / 5) = n ^ ((2 : ℝ) / 15) := by
      rw [rpow_pow_mul n hn0]; norm_num
    rwa [h2] at h1
  have key : twoLevelBound k n - directBound k n =
      k ^ ((4 : ℝ) / 5) * n ^ ((5 : ℝ) / 3) *
        (n ^ ((2 : ℝ) / 15) - k ^ ((1 : ℝ) / 5)) := by
    unfold twoLevelBound directBound
    have hk1 : k = k ^ ((4 : ℝ) / 5) * k ^ ((1 : ℝ) / 5) := by
      have h := Real.rpow_add hk0 ((4 : ℝ) / 5) ((1 : ℝ) / 5)
      rw [show (4 : ℝ) / 5 + 1 / 5 = 1 by norm_num, Real.rpow_one] at h
      exact h
    have hn1 : n ^ ((9 : ℝ) / 5) = n ^ ((5 : ℝ) / 3) * n ^ ((2 : ℝ) / 15) := by
      have h := Real.rpow_add hn0 ((5 : ℝ) / 3) ((2 : ℝ) / 15)
      rw [show (5 : ℝ) / 3 + 2 / 15 = 9 / 5 by norm_num] at h
      exact h
    conv_lhs => enter [2]; rw [hk1]
    rw [hn1]
    ring
  have hnonneg : 0 ≤ k ^ ((4 : ℝ) / 5) * n ^ ((5 : ℝ) / 3) *
      (n ^ ((2 : ℝ) / 15) - k ^ ((1 : ℝ) / 5)) := by
    apply mul_nonneg (mul_nonneg (Real.rpow_nonneg hk0.le _) (Real.rpow_nonneg hn0.le _))
    linarith
  rw [← key] at hnonneg
  linarith

theorem regime_mid_collision (k n : ℝ) (hk : 1 ≤ k) (hn : 1 ≤ n)
    (hkn : k ≤ n ^ ((3 : ℝ) / 2)) :
    twoLevelBound k n ≤ collisionBound k n := by
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hkpow : k ^ ((2 : ℝ) / 15) ≤ n ^ ((1 : ℝ) / 5) := by
    have h1 : k ^ ((2 : ℝ) / 15) ≤ (n ^ ((3 : ℝ) / 2)) ^ ((2 : ℝ) / 15) :=
      Real.rpow_le_rpow hk0.le hkn (by norm_num)
    have h2 : (n ^ ((3 : ℝ) / 2)) ^ ((2 : ℝ) / 15) = n ^ ((1 : ℝ) / 5) := by
      rw [rpow_pow_mul n hn0]; norm_num
    rwa [h2] at h1
  have key : collisionBound k n - twoLevelBound k n =
      k ^ ((2 : ℝ) / 3) * n ^ ((9 : ℝ) / 5) *
        (n ^ ((1 : ℝ) / 5) - k ^ ((2 : ℝ) / 15)) := by
    unfold collisionBound twoLevelBound
    have hk1 : k ^ ((4 : ℝ) / 5) =
        k ^ ((2 : ℝ) / 3) * k ^ ((2 : ℝ) / 15) := by
      have h := Real.rpow_add hk0 ((2 : ℝ) / 3) ((2 : ℝ) / 15)
      rw [show (2 : ℝ) / 3 + 2 / 15 = 4 / 5 by norm_num] at h
      exact h
    have hn1 : n ^ 2 = n ^ ((9 : ℝ) / 5) * n ^ ((1 : ℝ) / 5) := by
      have h := Real.rpow_add hn0 ((9 : ℝ) / 5) ((1 : ℝ) / 5)
      rw [show (9 : ℝ) / 5 + 1 / 5 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
      exact h
    conv_lhs => enter [2]; rw [hk1]
    conv_lhs => enter [1]; rw [hn1]
    ring
  have hnonneg : 0 ≤ k ^ ((2 : ℝ) / 3) * n ^ ((9 : ℝ) / 5) *
      (n ^ ((1 : ℝ) / 5) - k ^ ((2 : ℝ) / 15)) := by
    apply mul_nonneg (mul_nonneg (Real.rpow_nonneg hk0.le _) (Real.rpow_nonneg hn0.le _))
    linarith
  rw [← key] at hnonneg
  linarith

theorem regime_mid_direct (k n : ℝ) (hk : 1 ≤ k) (hn : 1 ≤ n)
    (hkn : n ≤ k) :
    collisionBound k n ≤ directBound k n := by
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hpow : n ^ ((1 : ℝ) / 3) ≤ k ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow hn0.le hkn (by norm_num)
  have key : directBound k n - collisionBound k n =
      k ^ ((2 : ℝ) / 3) * n ^ ((5 : ℝ) / 3) *
        (k ^ ((1 : ℝ) / 3) - n ^ ((1 : ℝ) / 3)) := by
    unfold directBound collisionBound
    have hk1 : k = k ^ ((2 : ℝ) / 3) * k ^ ((1 : ℝ) / 3) := by
      have h := Real.rpow_add hk0 ((2 : ℝ) / 3) ((1 : ℝ) / 3)
      rw [show (2 : ℝ) / 3 + 1 / 3 = 1 by norm_num, Real.rpow_one] at h
      exact h
    have hn1 : n ^ 2 = n ^ ((5 : ℝ) / 3) * n ^ ((1 : ℝ) / 3) := by
      have h := Real.rpow_add hn0 ((5 : ℝ) / 3) ((1 : ℝ) / 3)
      rw [show (5 : ℝ) / 3 + 1 / 3 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
      exact h
    conv_lhs => enter [1]; rw [hk1]
    conv_lhs => enter [2]; rw [hn1]
    ring
  have hnonneg : 0 ≤ k ^ ((2 : ℝ) / 3) * n ^ ((5 : ℝ) / 3) *
      (k ^ ((1 : ℝ) / 3) - n ^ ((1 : ℝ) / 3)) := by
    apply mul_nonneg (mul_nonneg (Real.rpow_nonneg hk0.le _) (Real.rpow_nonneg hn0.le _))
    linarith
  rw [← key] at hnonneg
  linarith

theorem all_bounds_at_k_eq_n (n : ℝ) (hn : 0 < n) :
    directBound n n = n ^ ((8 : ℝ) / 3) ∧
      collisionBound n n = n ^ ((8 : ℝ) / 3) := by
  constructor
  · unfold directBound
    have h := Real.rpow_add hn (1 : ℝ) ((5 : ℝ) / 3)
    rw [show (1 : ℝ) + 5 / 3 = 8 / 3 by norm_num, Real.rpow_one] at h
    exact h.symm
  · unfold collisionBound
    have h := Real.rpow_add hn ((2 : ℝ) / 3) ((2 : ℕ) : ℝ)
    rw [show (2 : ℝ) / 3 + ((2 : ℕ) : ℝ) = 8 / 3 by norm_num, Real.rpow_natCast] at h
    exact h.symm

theorem regime_small_collision (k n : ℝ) (hk : 1 ≤ k) (hn : 1 ≤ n)
    (hkn : k ≤ n) :
    directBound k n ≤ collisionBound k n := by
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hpow : k ^ ((1 : ℝ) / 3) ≤ n ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow hk0.le hkn (by norm_num)
  have key : collisionBound k n - directBound k n =
      k ^ ((2 : ℝ) / 3) * n ^ ((5 : ℝ) / 3) *
        (n ^ ((1 : ℝ) / 3) - k ^ ((1 : ℝ) / 3)) := by
    unfold directBound collisionBound
    have hk1 : k = k ^ ((2 : ℝ) / 3) * k ^ ((1 : ℝ) / 3) := by
      have h := Real.rpow_add hk0 ((2 : ℝ) / 3) ((1 : ℝ) / 3)
      rw [show (2 : ℝ) / 3 + 1 / 3 = 1 by norm_num, Real.rpow_one] at h
      exact h
    have hn1 : n ^ 2 = n ^ ((5 : ℝ) / 3) * n ^ ((1 : ℝ) / 3) := by
      have h := Real.rpow_add hn0 ((5 : ℝ) / 3) ((1 : ℝ) / 3)
      rw [show (5 : ℝ) / 3 + 1 / 3 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
      exact h
    conv_lhs => enter [1]; rw [hn1]
    conv_lhs => enter [2]; rw [hk1]
    ring
  have hnonneg : 0 ≤ collisionBound k n - directBound k n := by
    rw [key]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hk0.le _) (Real.rpow_nonneg hn0.le _))
      (by linarith)
  linarith

theorem regime_mid_twolevel_direct (k n : ℝ) (hk : 1 ≤ k) (hn : 1 ≤ n)
    (hkn : n ^ ((2 : ℝ) / 3) ≤ k) :
    twoLevelBound k n ≤ directBound k n := by
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hpow : n ^ ((2 : ℝ) / 15) ≤ k ^ ((1 : ℝ) / 5) := by
    have h1 : n ^ ((2 : ℝ) / 15) = (n ^ ((2 : ℝ) / 3)) ^ ((1 : ℝ) / 5) := by
      rw [rpow_pow_mul n hn0]
      norm_num
    rw [h1]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hn0.le _) hkn (by norm_num)
  have key : twoLevelBound k n - directBound k n =
      k ^ ((4 : ℝ) / 5) * n ^ ((5 : ℝ) / 3) *
        (n ^ ((2 : ℝ) / 15) - k ^ ((1 : ℝ) / 5)) := by
    unfold twoLevelBound directBound
    have hk1 : k = k ^ ((4 : ℝ) / 5) * k ^ ((1 : ℝ) / 5) := by
      have h := Real.rpow_add hk0 ((4 : ℝ) / 5) ((1 : ℝ) / 5)
      rw [show (4 : ℝ) / 5 + 1 / 5 = 1 by norm_num, Real.rpow_one] at h
      exact h
    have hn1 : n ^ ((9 : ℝ) / 5) = n ^ ((5 : ℝ) / 3) * n ^ ((2 : ℝ) / 15) := by
      have h := Real.rpow_add hn0 ((5 : ℝ) / 3) ((2 : ℝ) / 15)
      rw [show (5 : ℝ) / 3 + 2 / 15 = 9 / 5 by norm_num] at h
      exact h
    conv_lhs => enter [1]; rw [hn1]
    conv_lhs => enter [2]; rw [hk1]
    ring
  have hnonpos : twoLevelBound k n - directBound k n ≤ 0 := by
    rw [key]
    have hfac : k ^ ((4 : ℝ) / 5) * n ^ ((5 : ℝ) / 3) ≥ 0 :=
      mul_nonneg (Real.rpow_nonneg hk0.le _) (Real.rpow_nonneg hn0.le _)
    have hle : n ^ ((2 : ℝ) / 15) - k ^ ((1 : ℝ) / 5) ≤ 0 := by linarith
    exact mul_nonpos_of_nonneg_of_nonpos hfac hle
  linarith

theorem regime_large_collision_twolevel (k n : ℝ) (hk : 1 ≤ k) (hn : 1 ≤ n)
    (hkn : n ^ ((3 : ℝ) / 2) ≤ k) :
    collisionBound k n ≤ twoLevelBound k n := by
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hpow : n ^ ((1 : ℝ) / 5) ≤ k ^ ((2 : ℝ) / 15) := by
    have h1 : n ^ ((1 : ℝ) / 5) = (n ^ ((3 : ℝ) / 2)) ^ ((2 : ℝ) / 15) := by
      rw [rpow_pow_mul n hn0]
      norm_num
    rw [h1]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hn0.le _) hkn (by norm_num)
  have key : collisionBound k n - twoLevelBound k n =
      k ^ ((2 : ℝ) / 3) * n ^ ((9 : ℝ) / 5) *
        (n ^ ((1 : ℝ) / 5) - k ^ ((2 : ℝ) / 15)) := by
    unfold collisionBound twoLevelBound
    have hk1 : k ^ ((4 : ℝ) / 5) =
        k ^ ((2 : ℝ) / 3) * k ^ ((2 : ℝ) / 15) := by
      have h := Real.rpow_add hk0 ((2 : ℝ) / 3) ((2 : ℝ) / 15)
      rw [show (2 : ℝ) / 3 + 2 / 15 = 4 / 5 by norm_num] at h
      exact h
    have hn1 : n ^ 2 = n ^ ((9 : ℝ) / 5) * n ^ ((1 : ℝ) / 5) := by
      have h := Real.rpow_add hn0 ((9 : ℝ) / 5) ((1 : ℝ) / 5)
      rw [show (9 : ℝ) / 5 + 1 / 5 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
      exact h
    conv_lhs => enter [1]; rw [hn1]
    conv_lhs => enter [2]; rw [hk1]
    ring
  have hnonpos : collisionBound k n - twoLevelBound k n ≤ 0 := by
    rw [key]
    have hfac : k ^ ((2 : ℝ) / 3) * n ^ ((9 : ℝ) / 5) ≥ 0 :=
      mul_nonneg (Real.rpow_nonneg hk0.le _) (Real.rpow_nonneg hn0.le _)
    have hle : n ^ ((1 : ℝ) / 5) - k ^ ((2 : ℝ) / 15) ≤ 0 := by linarith
    exact mul_nonpos_of_nonneg_of_nonpos hfac hle
  linarith

theorem twoLevelBound_self (n : ℝ) (hn : 0 < n) :
    twoLevelBound n n = n ^ ((13 : ℝ) / 5) := by
  unfold twoLevelBound
  have h := Real.rpow_add hn ((4 : ℝ) / 5) ((9 : ℝ) / 5)
  rw [show (4 : ℝ) / 5 + 9 / 5 = 13 / 5 by norm_num] at h
  exact h.symm

end Qatlib.Papers.CommuteTest05.MainResults.CostBounds
