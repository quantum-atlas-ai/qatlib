/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Log
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Papers.IsingNeural23.MainResults

open Nat

def spinCount (n m B H L N : ℕ) : ℕ :=
  n * H
  + H * ((n * 2 ^ (B + 1)).log2 + 1)
  + H ^ 2 * (L - 2)
  + m * H * ((2 * H).log2 + 1)
  + m * ((2 * H).log2 + 1)
  + N * (H * ((n * 2 ^ (B + 2)).log2 + 1))
  + N * ((L - 2) * (H * ((2 * H).log2 + 1)))
  + N * (H * ((3 * n * 2 ^ B).log2 + 1))
  + N * ((L - 2) * (H * ((2 * H).log2 + 1)))
  + N * (H * ((3 * n * 2 ^ (B + 1)).log2 + 1))
  + N * ((L - 1) * H)
  + N * (m * ((4 * H).log2 + 1))

def eq9Poly (n m B H L N : ℕ) : ℕ :=
  n * H + m * N * H.log2 + H * N * n.log2 + H ^ 2 * L + B * H * N
    + m * H * H.log2 + H * L * N * H.log2

def eq10Poly (H L N : ℕ) : ℕ :=
  H ^ 2 * L + H * L * N * H.log2

def eq9Real (n m B H L N : ℕ) : ℝ :=
  (n : ℝ) * H + (m : ℝ) * N * (H.log2 : ℝ) + (H : ℝ) * N * (n.log2 : ℝ)
    + (H : ℝ) ^ 2 * L + (B : ℝ) * H * N + (m : ℝ) * H * (H.log2 : ℝ)
    + (H : ℝ) * L * N * (H.log2 : ℝ)

lemma eq9Real_eq_cast (n m B H L N : ℕ) :
    eq9Real n m B H L N = (eq9Poly n m B H L N : ℝ) := by
  unfold eq9Real eq9Poly
  push_cast
  ring

lemma log2_mul_two (m : ℕ) (hm : m ≠ 0) : (m * 2).log2 = m.log2 + 1 := by
  rw [Nat.log2_eq_log_two, Nat.log_mul_base Nat.one_lt_two hm, ← Nat.log2_eq_log_two]

lemma log2_mul_two_pow (n k : ℕ) (hn : n ≠ 0) : (n * 2 ^ k).log2 = n.log2 + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.pow_succ]
    have h1 : n * (2 ^ k * 2) = (n * 2 ^ k) * 2 := by ring
    rw [h1, log2_mul_two (n * 2 ^ k) (by positivity), ih]
    ring

lemma log2_mono {m n : ℕ} (h : m ≤ n) : m.log2 ≤ n.log2 := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  exact Nat.log_mono (by norm_num : 1 < 2) (le_refl 2) h

lemma log2_three_mul_two_pow_le (n k : ℕ) (hn : n ≠ 0) :
    (3 * n * 2 ^ k).log2 ≤ n.log2 + (k + 2) := by
  have hle : 3 * n * 2 ^ k ≤ n * 2 ^ (k + 2) := by
    calc 3 * n * 2 ^ k = 3 * (n * 2 ^ k) := by ring
      _ ≤ 4 * (n * 2 ^ k) := Nat.mul_le_mul_right _ (by norm_num)
      _ = n * 2 ^ (k + 2) := by rw [Nat.pow_add]; ring
  calc (3 * n * 2 ^ k).log2 ≤ (n * 2 ^ (k + 2)).log2 := log2_mono hle
    _ = n.log2 + (k + 2) := log2_mul_two_pow n (k + 2) hn

lemma le_mul_of_one_le_right {a b : ℝ} (ha : 0 ≤ a) (hb : 1 ≤ b) : a ≤ a * b := by
  calc a = a * 1 := (mul_one a).symm
    _ ≤ a * b := mul_le_mul_of_nonneg_left hb ha

theorem masterR (n m B H L N : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hB : 1 ≤ B)
    (hH : 2 ≤ H) (hL : 2 ≤ L) (hN : 1 ≤ N) :
    (spinCount n m B H L N : ℝ) ≤ 40 * eq9Real n m B H L N := by
  have hn0 : n ≠ 0 := by omega
  have hH0 : H ≠ 0 := by omega
  have hnLow : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hmLow : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hBLow : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hH2 : (2 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hL2 : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hH0' : (0 : ℝ) ≤ (H : ℝ) := by linarith
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by linarith
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := by linarith
  have hlogH1 : (1 : ℝ) ≤ (H.log2 : ℝ) := by
    have h : 1 ≤ H.log2 := (Nat.le_log2 hH0).2 (by simpa using hH)
    exact_mod_cast h
  have hlogH_le : (H.log2 : ℝ) ≤ (H : ℝ) := by exact_mod_cast Nat.log2_le_self H
  have hlogH0 : (0 : ℝ) ≤ (H.log2 : ℝ) := by linarith
  have hlogn0 : (0 : ℝ) ≤ (n.log2 : ℝ) := by positivity
  have hlogB1 : ((n * 2 ^ (B + 1)).log2 : ℝ) = (n.log2 : ℝ) + ((B : ℝ) + 1) := by
    exact_mod_cast log2_mul_two_pow n (B + 1) hn0
  have hlogB2 : ((n * 2 ^ (B + 2)).log2 : ℝ) = (n.log2 : ℝ) + ((B : ℝ) + 2) := by
    exact_mod_cast log2_mul_two_pow n (B + 2) hn0
  have hlog2H : ((2 * H).log2 : ℝ) = (H.log2 : ℝ) + 1 := by
    have h := log2_mul_two H hH0
    have h2 : (2 * H).log2 = (H * 2).log2 := by rw [mul_comm]
    rw [h2, h]; push_cast; ring
  have hlog4H : ((4 * H).log2 : ℝ) = (H.log2 : ℝ) + 2 := by
    have h : (4 * H).log2 = (H * 2 ^ 2).log2 := by norm_num; ring_nf
    rw [h, log2_mul_two_pow H 2 hH0]; push_cast; ring
  have h3B : ((3 * n * 2 ^ B).log2 : ℝ) ≤ (n.log2 : ℝ) + ((B : ℝ) + 2) := by
    have h := log2_three_mul_two_pow_le n B hn0
    calc ((3 * n * 2 ^ B).log2 : ℝ) ≤ ((n.log2 + (B + 2) : ℕ) : ℝ) := by exact_mod_cast h
      _ = (n.log2 : ℝ) + ((B : ℝ) + 2) := by push_cast; ring
  have h3B1 : ((3 * n * 2 ^ (B + 1)).log2 : ℝ) ≤ (n.log2 : ℝ) + ((B : ℝ) + 3) := by
    have h := log2_three_mul_two_pow_le n (B + 1) hn0
    calc ((3 * n * 2 ^ (B + 1)).log2 : ℝ) ≤ ((n.log2 + (B + 1 + 2) : ℕ) : ℝ) := by
          exact_mod_cast h
      _ = (n.log2 : ℝ) + ((B : ℝ) + 3) := by push_cast; ring
  have hLsub2 : ((L - 2 : ℕ) : ℝ) = (L : ℝ) - 2 := by
    rw [Nat.cast_sub hL]; norm_num
  have hLsub1 : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ L by omega)]; norm_num
  set R : ℝ := eq9Real n m B H L N with hRdef
  set a1 : ℝ := (n : ℝ) * H with ha1
  set a2 : ℝ := (m : ℝ) * N * (H.log2 : ℝ) with ha2
  set a3 : ℝ := (H : ℝ) * N * (n.log2 : ℝ) with ha3
  set a4 : ℝ := (H : ℝ) ^ 2 * L with ha4
  set a5 : ℝ := (B : ℝ) * H * N with ha5
  set a6 : ℝ := (m : ℝ) * H * (H.log2 : ℝ) with ha6
  set a7 : ℝ := (H : ℝ) * L * N * (H.log2 : ℝ) with ha7
  have hR' : R = a1 + (a2 + (a3 + (a4 + (a5 + (a6 + a7))))) := by
    rw [hRdef]; unfold eq9Real; rw [ha1, ha2, ha3, ha4, ha5, ha6, ha7]; ring
  have hn1 : 0 ≤ a1 := by rw [ha1]; positivity
  have hn2' : 0 ≤ a2 := by rw [ha2]; positivity
  have hn3 : 0 ≤ a3 := by rw [ha3]; positivity
  have hn4 : 0 ≤ a4 := by rw [ha4]; positivity
  have hn5 : 0 ≤ a5 := by rw [ha5]; positivity
  have hn6 : 0 ≤ a6 := by rw [ha6]; positivity
  have hn7 : 0 ≤ a7 := by rw [ha7]; positivity
  have e1 : a1 ≤ R := by linarith [hR', hn2', hn3, hn4, hn5, hn6, hn7]
  have e2 : a2 ≤ R := by linarith [hR', hn1, hn3, hn4, hn5, hn6, hn7]
  have e3 : a3 ≤ R := by linarith [hR', hn1, hn2', hn4, hn5, hn6, hn7]
  have e4 : a4 ≤ R := by linarith [hR', hn1, hn2', hn3, hn5, hn6, hn7]
  have e5 : a5 ≤ R := by linarith [hR', hn1, hn2', hn3, hn4, hn6, hn7]
  have e6 : a6 ≤ R := by linarith [hR', hn1, hn2', hn3, hn4, hn5, hn7]
  have e7 : a7 ≤ R := by linarith [hR', hn1, hn2', hn3, hn4, hn5, hn6]
  have hHlogn : (0 : ℝ) ≤ (H : ℝ) * (n.log2 : ℝ) := by positivity
  have hBH : (0 : ℝ) ≤ (B : ℝ) * H := by positivity
  have hmH : (0 : ℝ) ≤ (m : ℝ) * H := by positivity
  have hm : (0 : ℝ) ≤ (m : ℝ) := by linarith
  have hmHlog : (0 : ℝ) ≤ (m : ℝ) * H * (H.log2 : ℝ) := by positivity
  have hNH : (0 : ℝ) ≤ (N : ℝ) * H := by positivity
  have hNLH : (0 : ℝ) ≤ (N : ℝ) * L * H := by positivity
  have hLm2n : (0 : ℝ) ≤ (L : ℝ) - 2 := by linarith
  have hLm2 : (L : ℝ) - 2 ≤ (L : ℝ) := by linarith
  have hLm1 : (L : ℝ) - 1 ≤ (L : ℝ) := by linarith
  have hNLHlog : (N : ℝ) * L * H ≤ a7 := by
    have h := le_mul_of_one_le_right hNLH hlogH1
    rw [ha7]
    calc (N : ℝ) * L * H ≤ (N : ℝ) * L * H * (H.log2 : ℝ) := h
      _ = (H : ℝ) * L * N * (H.log2 : ℝ) := by ring
  have hNHlog : (N : ℝ) * H ≤ a7 := by
    have h2 : (N : ℝ) * H ≤ (N : ℝ) * L * H := by
      have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ (L : ℝ) by linarith) hNH
      calc (N : ℝ) * H = (N : ℝ) * H * 1 := (mul_one _).symm
        _ ≤ (N : ℝ) * H * (L : ℝ) := this
        _ = (N : ℝ) * L * H := by ring
    exact le_trans h2 hNLHlog
  have t1 : (n : ℝ) * H ≤ 1 * R := by rw [← ha1]; linarith [e1]
  have t2 : (H : ℝ) * ((n.log2 : ℝ) + ((B : ℝ) + 1) + 1) ≤ 3 * R := by
    have u1 : (H : ℝ) * (n.log2 : ℝ) ≤ a3 := by
      have h := le_mul_of_one_le_right hHlogn hN1
      rw [ha3]
      calc (H : ℝ) * (n.log2 : ℝ) ≤ (H : ℝ) * (n.log2 : ℝ) * (N : ℝ) := h
        _ = (H : ℝ) * N * (n.log2 : ℝ) := by ring
    have u2 : (B : ℝ) * (H : ℝ) ≤ a5 := by
      have h := le_mul_of_one_le_right hBH hN1
      rw [ha5]
      calc (B : ℝ) * (H : ℝ) ≤ (B : ℝ) * (H : ℝ) * (N : ℝ) := h
        _ = (B : ℝ) * H * N := by ring
    have u3 : 2 * (H : ℝ) ≤ a4 := by
      rw [ha4]
      have hp : (H : ℝ) ^ 2 ≤ (H : ℝ) ^ 2 * L :=
        le_mul_of_one_le_right (sq_nonneg (H : ℝ)) (by linarith)
      nlinarith [hH2]
    calc (H : ℝ) * ((n.log2 : ℝ) + ((B : ℝ) + 1) + 1)
        = (H : ℝ) * (n.log2 : ℝ) + (B : ℝ) * (H : ℝ) + 2 * (H : ℝ) := by ring
      _ ≤ a3 + a5 + a4 := by linarith [u1, u2, u3]
      _ ≤ 3 * R := by linarith [e3, e4, e5]
  have t3 : (H : ℝ) ^ 2 * ((L : ℝ) - 2) ≤ 1 * R := by
    calc (H : ℝ) ^ 2 * ((L : ℝ) - 2) ≤ (H : ℝ) ^ 2 * (L : ℝ) := by
          exact mul_le_mul_of_nonneg_left hLm2 (by positivity)
      _ = a4 := by rw [ha4]
      _ ≤ R := e4
      _ = 1 * R := by ring
  have t4 : (m : ℝ) * H * ((H.log2 : ℝ) + 1 + 1) ≤ 3 * R := by
    have u1 : (m : ℝ) * H * (H.log2 : ℝ) = a6 := by rw [ha6]
    have u2 : (m : ℝ) * H ≤ a6 := by
      rw [ha6]
      calc (m : ℝ) * H = (m : ℝ) * H * 1 := (mul_one _).symm
        _ ≤ (m : ℝ) * H * (H.log2 : ℝ) := mul_le_mul_of_nonneg_left hlogH1 (by positivity)
    calc (m : ℝ) * H * ((H.log2 : ℝ) + 1 + 1)
        = (m : ℝ) * H * (H.log2 : ℝ) + 2 * ((m : ℝ) * H) := by ring
      _ ≤ a6 + 2 * a6 := by linarith [u1, u2]
      _ ≤ 3 * R := by linarith [e6]
  have t5 : (m : ℝ) * ((H.log2 : ℝ) + 1 + 1) ≤ 3 * R := by
    have hH1 : (1 : ℝ) ≤ (H : ℝ) := by linarith
    have u1 : (m : ℝ) * (H.log2 : ℝ) ≤ a6 := by
      have h := le_mul_of_one_le_right (by positivity : (0 : ℝ) ≤ (m : ℝ) * (H.log2 : ℝ)) hH1
      rw [ha6]
      calc (m : ℝ) * (H.log2 : ℝ) ≤ (m : ℝ) * (H.log2 : ℝ) * (H : ℝ) := h
        _ = (m : ℝ) * H * (H.log2 : ℝ) := by ring
    have u2 : (m : ℝ) ≤ a6 := by
      have h1 : (1 : ℝ) ≤ (H : ℝ) * (H.log2 : ℝ) := by
        calc (1 : ℝ) = 1 * 1 := (mul_one _).symm
          _ ≤ (H : ℝ) * (H.log2 : ℝ) := mul_le_mul hH1 hlogH1 (by norm_num) hH0'
      have h := le_mul_of_one_le_right hm h1
      rw [ha6]
      calc (m : ℝ) = (m : ℝ) * 1 := (mul_one _).symm
        _ ≤ (m : ℝ) * ((H : ℝ) * (H.log2 : ℝ)) := by simpa using h
        _ = (m : ℝ) * H * (H.log2 : ℝ) := by ring
    calc (m : ℝ) * ((H.log2 : ℝ) + 1 + 1)
        = (m : ℝ) * (H.log2 : ℝ) + 2 * (m : ℝ) := by ring
      _ ≤ a6 + 2 * a6 := by linarith [u1, u2]
      _ ≤ 3 * R := by linarith [e6]
  have t6 : (N : ℝ) * ((H : ℝ) * ((n.log2 : ℝ) + ((B : ℝ) + 2) + 1)) ≤ 5 * R := by
    have u1 : (N : ℝ) * H * (n.log2 : ℝ) = a3 := by rw [ha3]; ring
    have u2 : (N : ℝ) * H * (B : ℝ) = a5 := by rw [ha5]; ring
    have u3 : (N : ℝ) * H ≤ a7 := hNHlog
    calc (N : ℝ) * ((H : ℝ) * ((n.log2 : ℝ) + ((B : ℝ) + 2) + 1))
        = (N : ℝ) * H * (n.log2 : ℝ) + (N : ℝ) * H * (B : ℝ) + 3 * ((N : ℝ) * H) := by ring
      _ ≤ a3 + a5 + 3 * a7 := by linarith [u1, u2, u3]
      _ ≤ 5 * R := by linarith [e3, e5, e7]
  have hNLLe : (N : ℝ) * ((L : ℝ) - 2) ≤ (N : ℝ) * (L : ℝ) :=
    mul_le_mul_of_nonneg_left hLm2 hN0
  have hNL2H : (N : ℝ) * ((L : ℝ) - 2) * H ≤ (N : ℝ) * (L : ℝ) * H := by
    have := mul_le_mul_of_nonneg_right hNLLe hH0'
    calc (N : ℝ) * ((L : ℝ) - 2) * H = (N : ℝ) * ((L : ℝ) - 2) * (H : ℝ) := by ring
      _ ≤ (N : ℝ) * (L : ℝ) * (H : ℝ) := this
      _ = (N : ℝ) * (L : ℝ) * H := by ring
  have hNL2Hl : (N : ℝ) * ((L : ℝ) - 2) * H * (H.log2 : ℝ)
      ≤ (N : ℝ) * (L : ℝ) * H * (H.log2 : ℝ) := by
    have := mul_le_mul_of_nonneg_right hNL2H hlogH0
    calc (N : ℝ) * ((L : ℝ) - 2) * H * (H.log2 : ℝ)
        = ((N : ℝ) * ((L : ℝ) - 2) * H) * (H.log2 : ℝ) := by ring
      _ ≤ ((N : ℝ) * (L : ℝ) * H) * (H.log2 : ℝ) := this
      _ = (N : ℝ) * (L : ℝ) * H * (H.log2 : ℝ) := by ring
  have t7 : (N : ℝ) * (((L : ℝ) - 2) * ((H : ℝ) * ((H.log2 : ℝ) + 1 + 1))) ≤ 3 * R := by
    have u1 : (N : ℝ) * ((L : ℝ) - 2) * H * (H.log2 : ℝ) ≤ a7 := by
      rw [ha7]
      calc (N : ℝ) * ((L : ℝ) - 2) * H * (H.log2 : ℝ)
          ≤ (N : ℝ) * (L : ℝ) * H * (H.log2 : ℝ) := hNL2Hl
        _ = (H : ℝ) * L * N * (H.log2 : ℝ) := by ring
    have u2 : (N : ℝ) * ((L : ℝ) - 2) * H ≤ a7 := by
      rw [ha7]
      calc (N : ℝ) * ((L : ℝ) - 2) * H ≤ (N : ℝ) * (L : ℝ) * H := hNL2H
        _ ≤ (H : ℝ) * L * N * (H.log2 : ℝ) := hNLHlog
    calc (N : ℝ) * (((L : ℝ) - 2) * ((H : ℝ) * ((H.log2 : ℝ) + 1 + 1)))
        = (N : ℝ) * ((L : ℝ) - 2) * H * (H.log2 : ℝ)
            + 2 * ((N : ℝ) * ((L : ℝ) - 2) * H) := by ring
      _ ≤ a7 + 2 * a7 := by linarith [u1, u2]
      _ ≤ 3 * R := by linarith [e7]
  have t11 : (N : ℝ) * (((L : ℝ) - 1) * (H : ℝ)) ≤ 1 * R := by
    have h2 : (N : ℝ) * ((L : ℝ) - 1) * H ≤ (N : ℝ) * (L : ℝ) * H := by
      have h1 : (N : ℝ) * ((L : ℝ) - 1) ≤ (N : ℝ) * (L : ℝ) :=
        mul_le_mul_of_nonneg_left hLm1 hN0
      have := mul_le_mul_of_nonneg_right h1 hH0'
      calc (N : ℝ) * ((L : ℝ) - 1) * H = (N : ℝ) * ((L : ℝ) - 1) * (H : ℝ) := by ring
        _ ≤ (N : ℝ) * (L : ℝ) * (H : ℝ) := this
        _ = (N : ℝ) * (L : ℝ) * H := by ring
    calc (N : ℝ) * (((L : ℝ) - 1) * (H : ℝ)) = (N : ℝ) * ((L : ℝ) - 1) * H := by ring
      _ ≤ (N : ℝ) * L * H := h2
      _ ≤ a7 := hNLHlog
      _ ≤ R := e7
      _ = 1 * R := by ring
  have t12 : (N : ℝ) * ((m : ℝ) * ((H.log2 : ℝ) + 2 + 1)) ≤ 4 * R := by
    have u1 : (N : ℝ) * (m : ℝ) * (H.log2 : ℝ) = a2 := by rw [ha2]; ring
    have u2 : (N : ℝ) * (m : ℝ) ≤ a2 := by
      have h := le_mul_of_one_le_right (by positivity : (0 : ℝ) ≤ (N : ℝ) * (m : ℝ)) hlogH1
      rw [ha2]
      calc (N : ℝ) * (m : ℝ) ≤ (N : ℝ) * (m : ℝ) * (H.log2 : ℝ) := h
        _ = (m : ℝ) * N * (H.log2 : ℝ) := by ring
    calc (N : ℝ) * ((m : ℝ) * ((H.log2 : ℝ) + 2 + 1))
        = (N : ℝ) * (m : ℝ) * (H.log2 : ℝ) + 3 * ((N : ℝ) * (m : ℝ)) := by ring
      _ ≤ a2 + 3 * a2 := by linarith [u1, u2]
      _ ≤ 4 * R := by linarith [e2]
  have hS : (spinCount n m B H L N : ℝ) =
      (n : ℝ) * H
      + (H : ℝ) * ((n.log2 : ℝ) + ((B : ℝ) + 1) + 1)
      + (H : ℝ) ^ 2 * ((L : ℝ) - 2)
      + (m : ℝ) * H * ((H.log2 : ℝ) + 1 + 1)
      + (m : ℝ) * ((H.log2 : ℝ) + 1 + 1)
      + (N : ℝ) * ((H : ℝ) * ((n.log2 : ℝ) + ((B : ℝ) + 2) + 1))
      + (N : ℝ) * (((L : ℝ) - 2) * ((H : ℝ) * ((H.log2 : ℝ) + 1 + 1)))
      + (N : ℝ) * ((H : ℝ) * ((3 * n * 2 ^ B).log2 + 1))
      + (N : ℝ) * (((L : ℝ) - 2) * ((H : ℝ) * ((H.log2 : ℝ) + 1 + 1)))
      + (N : ℝ) * ((H : ℝ) * ((3 * n * 2 ^ (B + 1)).log2 + 1))
      + (N : ℝ) * (((L : ℝ) - 1) * (H : ℝ))
      + (N : ℝ) * ((m : ℝ) * ((H.log2 : ℝ) + 2 + 1)) := by
    unfold spinCount
    push_cast
    rw [hlogB1, hlogB2, hlog2H, hlog4H, hLsub2, hLsub1]
  have t8 : (N : ℝ) * ((H : ℝ) * ((3 * n * 2 ^ B).log2 + 1)) ≤
      (N : ℝ) * ((H : ℝ) * ((n.log2 : ℝ) + ((B : ℝ) + 2) + 1)) := by
    apply mul_le_mul_of_nonneg_left
    · apply mul_le_mul_of_nonneg_left
      · linarith [h3B]
      · exact hH0'
    · exact hN0
  have t10 : (N : ℝ) * ((H : ℝ) * ((3 * n * 2 ^ (B + 1)).log2 + 1)) ≤
      (N : ℝ) * ((H : ℝ) * ((n.log2 : ℝ) + ((B : ℝ) + 3) + 1)) := by
    apply mul_le_mul_of_nonneg_left
    · apply mul_le_mul_of_nonneg_left
      · linarith [h3B1]
      · exact hH0'
    · exact hN0
  have t6'' : (N : ℝ) * ((H : ℝ) * ((n.log2 : ℝ) + ((B : ℝ) + 3) + 1)) ≤ 6 * R := by
    have u1 : (N : ℝ) * H * (n.log2 : ℝ) = a3 := by rw [ha3]; ring
    have u2 : (N : ℝ) * H * (B : ℝ) = a5 := by rw [ha5]; ring
    have u3 : 4 * ((N : ℝ) * H) ≤ 4 * a7 := by
      have : (N : ℝ) * H ≤ a7 := hNHlog
      linarith
    calc (N : ℝ) * ((H : ℝ) * ((n.log2 : ℝ) + ((B : ℝ) + 3) + 1))
        = (N : ℝ) * H * (n.log2 : ℝ) + (N : ℝ) * H * (B : ℝ) + 4 * ((N : ℝ) * H) := by ring
      _ ≤ a3 + a5 + 4 * a7 := by linarith [u1, u2, u3]
      _ ≤ 6 * R := by linarith [e3, e5, e7]
  have t8R : (N : ℝ) * ((H : ℝ) * ((3 * n * 2 ^ B).log2 + 1)) ≤ 5 * R :=
    le_trans t8 t6
  have t10R : (N : ℝ) * ((H : ℝ) * ((3 * n * 2 ^ (B + 1)).log2 + 1)) ≤ 6 * R :=
    le_trans t10 t6''
  rw [hS]
  linarith [t1, t2, t3, t4, t5, t6, t7, t8R, t7, t10R, t11, t12]

theorem space_complexity_eq9 (n m B H L N : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hB : 1 ≤ B) (hH : 2 ≤ H) (hL : 2 ≤ L) (hN : 1 ≤ N) :
    spinCount n m B H L N ≤ 40 * eq9Poly n m B H L N := by
  have h := masterR n m B H L N hn hm hB hH hL hN
  rw [eq9Real_eq_cast] at h
  exact_mod_cast h

lemma H_le_eq10Poly {H L N : ℕ} (hH : 2 ≤ H) (hL : 2 ≤ L) :
    H ≤ eq10Poly H L N := by
  calc H = H * 1 := (Nat.mul_one H).symm
    _ ≤ H * (H * L) := Nat.mul_le_mul_left H (by nlinarith)
    _ = H ^ 2 * L := by ring
    _ ≤ eq10Poly H L N := by unfold eq10Poly; exact Nat.le_add_right _ _

lemma log2_le_eq10Poly {H L N : ℕ} (hH : 2 ≤ H) (hL : 2 ≤ L) :
    H.log2 ≤ eq10Poly H L N :=
  le_trans (Nat.log2_le_self H) (H_le_eq10Poly hH hL)

lemma HN_le_eq10Poly {H L N : ℕ} (hH : 2 ≤ H) (hL : 2 ≤ L) :
    H * N ≤ eq10Poly H L N := by
  have hlog : 1 ≤ H.log2 := (Nat.le_log2 (by omega)).2 (by simpa using hH)
  calc H * N = H * N * 1 := (Nat.mul_one _).symm
    _ ≤ H * N * (L * H.log2) := Nat.mul_le_mul_left _ (by nlinarith)
    _ = H * L * N * H.log2 := by ring
    _ ≤ eq10Poly H L N := by unfold eq10Poly; exact Nat.le_add_left _ _

lemma N_log2_le_eq10Poly {H L N : ℕ} (hH : 2 ≤ H) (hL : 2 ≤ L) :
    N * H.log2 ≤ eq10Poly H L N := by
  calc N * H.log2 = N * H.log2 * 1 := (Nat.mul_one _).symm
    _ ≤ N * H.log2 * (H * L) := Nat.mul_le_mul_left _ (by nlinarith)
    _ = H * L * N * H.log2 := by ring
    _ ≤ eq10Poly H L N := by unfold eq10Poly; exact Nat.le_add_left _ _

lemma H_log2_le_eq10Poly {H L N : ℕ} (hL : 2 ≤ L) :
    H * H.log2 ≤ eq10Poly H L N := by
  have h1 : H * H.log2 ≤ H * H := Nat.mul_le_mul_left H (Nat.log2_le_self H)
  have h2 : H * H ≤ H ^ 2 * L := by
    calc H * H = H ^ 2 := by ring
      _ = H ^ 2 * 1 := (Nat.mul_one _).symm
      _ ≤ H ^ 2 * L := Nat.mul_le_mul_left _ (by omega)
  exact le_trans h1 (le_trans h2 (by unfold eq10Poly; exact Nat.le_add_right _ _))

theorem space_complexity_eq10_explicit (n m B H L N : ℕ) (hH : 2 ≤ H) (hL : 2 ≤ L) :
    eq9Poly n m B H L N ≤ (2 * n + 2 * m + B + 2) * eq10Poly H L N := by
  have h1 : n * H ≤ n * eq10Poly H L N := Nat.mul_le_mul_left n (H_le_eq10Poly hH hL)
  have h2 : m * N * H.log2 ≤ m * eq10Poly H L N := by
    have := N_log2_le_eq10Poly (N := N) hH hL
    calc m * N * H.log2 = m * (N * H.log2) := by ring
      _ ≤ m * eq10Poly H L N := Nat.mul_le_mul_left m this
  have h3 : H * N * n.log2 ≤ n * eq10Poly H L N := by
    calc H * N * n.log2 ≤ H * N * n := Nat.mul_le_mul_left (H * N) (Nat.log2_le_self n)
      _ = n * (H * N) := by ring
      _ ≤ n * eq10Poly H L N := Nat.mul_le_mul_left n (HN_le_eq10Poly hH hL)
  have h4 : H ^ 2 * L ≤ 1 * eq10Poly H L N := by
    have := (by unfold eq10Poly; exact Nat.le_add_right (H ^ 2 * L) (H * L * N * H.log2) :
      H ^ 2 * L ≤ eq10Poly H L N)
    simpa using this
  have h5 : B * H * N ≤ B * eq10Poly H L N := by
    calc B * H * N = B * (H * N) := by ring
      _ ≤ B * eq10Poly H L N := Nat.mul_le_mul_left B (HN_le_eq10Poly hH hL)
  have h6 : m * H * H.log2 ≤ m * eq10Poly H L N := by
    calc m * H * H.log2 = m * (H * H.log2) := by ring
      _ ≤ m * eq10Poly H L N := Nat.mul_le_mul_left m (H_log2_le_eq10Poly hL)
  have h7 : H * L * N * H.log2 ≤ 1 * eq10Poly H L N := by
    have := (by unfold eq10Poly; exact Nat.le_add_left (H * L * N * H.log2) (H ^ 2 * L) :
      H * L * N * H.log2 ≤ eq10Poly H L N)
    simpa using this
  have hgoal : (2 * n + 2 * m + B + 2) * eq10Poly H L N
      = n * eq10Poly H L N + m * eq10Poly H L N + n * eq10Poly H L N
        + 1 * eq10Poly H L N + B * eq10Poly H L N + m * eq10Poly H L N
        + 1 * eq10Poly H L N := by ring
  rw [hgoal]
  unfold eq9Poly
  omega

theorem space_complexity_eq10 (n m B : ℕ) :
    ∃ C : ℕ, ∀ H L N : ℕ, 2 ≤ H → 2 ≤ L →
      eq9Poly n m B H L N ≤ C * eq10Poly H L N :=
  ⟨2 * n + 2 * m + B + 2, fun H L N hH hL =>
    space_complexity_eq10_explicit n m B H L N hH hL⟩

theorem space_complexity_simplified (n m B H L N : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hB : 1 ≤ B) (hH : 2 ≤ H) (hL : 2 ≤ L) (hN : 1 ≤ N) :
    spinCount n m B H L N ≤ (40 * (2 * n + 2 * m + B + 2)) * eq10Poly H L N := by
  have h9 := space_complexity_eq9 n m B H L N hn hm hB hH hL hN
  have h10 := space_complexity_eq10_explicit n m B H L N hH hL
  calc spinCount n m B H L N ≤ 40 * eq9Poly n m B H L N := h9
    _ ≤ 40 * ((2 * n + 2 * m + B + 2) * eq10Poly H L N) := Nat.mul_le_mul_left 40 h10
    _ = (40 * (2 * n + 2 * m + B + 2)) * eq10Poly H L N := by ring

end Qatlib.Papers.IsingNeural23.MainResults
