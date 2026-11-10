/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMatchingFlow05.BlockingFlow.NetworkFlow
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QMatchingFlow05.BlockingFlow

open Qatlib.Papers.QMatchingFlow05.SearchTools

theorem theorem9_perBlockingCost (c U : ℝ) (hc : 0 ≤ c) (hU : 0 ≤ U) :
    ∃ C : ℝ, 0 < C ∧ ∀ (kv n m j A : ℕ) (aV cV dV : Fin kv → ℝ),
      kv ≤ n → n ≤ m →
      (∀ v, 0 ≤ aV v) → (∀ v, 0 ≤ cV v) → (∀ v, 0 ≤ dV v) →
      (∑ v, aV v) ≤ (j : ℝ) * (A : ℝ) →
      (∑ v, cV v) ≤ (n : ℝ) →
      (∑ v, dV v) ≤ (m : ℝ) →
      (∑ v, c * (Real.sqrt (U * aV v * dV v) + Real.sqrt (cV v * dV v) +
          Real.sqrt (dV v + 1))) ≤
        C * c * (Real.sqrt (U * (j : ℝ) * (A : ℝ) * (m : ℝ)) +
          Real.sqrt ((n : ℝ) * (m : ℝ))) * logFactor n := by
  refine ⟨6, by norm_num, ?_⟩
  intro kv n m j A aV cV dV hkn hnm haV hcV hdV hsumA hsumC hsumD
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hk0 : (0 : ℝ) ≤ (kv : ℝ) := Nat.cast_nonneg kv
  have hsumD0 : (0 : ℝ) ≤ ∑ v, dV v := Finset.sum_nonneg fun v _ => hdV v

  have hA : (∑ v, Real.sqrt (U * aV v * dV v)) ≤
      Real.sqrt (U * (j : ℝ) * (A : ℝ) * (m : ℝ)) := by
    have hcs := sum_sqrt_mul_le (fun v : Fin kv => U * aV v) dV
      (fun v => mul_nonneg hU (haV v)) hdV
    have hsumU : (∑ v, U * aV v) ≤ U * ((j : ℝ) * (A : ℝ)) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hsumA hU
    have hUjA : (0 : ℝ) ≤ U * ((j : ℝ) * (A : ℝ)) := by
      have : (0 : ℝ) ≤ (j : ℝ) * (A : ℝ) := by positivity
      positivity
    calc (∑ v, Real.sqrt (U * aV v * dV v))
        = ∑ v, Real.sqrt ((U * aV v) * dV v) := rfl
      _ ≤ Real.sqrt (∑ v, U * aV v) * Real.sqrt (∑ v, dV v) := hcs
      _ ≤ Real.sqrt (U * ((j : ℝ) * (A : ℝ))) * Real.sqrt (m : ℝ) :=
          mul_le_mul (Real.sqrt_le_sqrt hsumU) (Real.sqrt_le_sqrt hsumD)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = Real.sqrt ((U * ((j : ℝ) * (A : ℝ))) * (m : ℝ)) :=
          (Real.sqrt_mul hUjA (m : ℝ)).symm
      _ = Real.sqrt (U * (j : ℝ) * (A : ℝ) * (m : ℝ)) := by
          congr 1
          ring

  have hB : (∑ v, Real.sqrt (cV v * dV v)) ≤ Real.sqrt ((n : ℝ) * (m : ℝ)) := by
    have hcs := sum_sqrt_mul_le cV dV hcV hdV
    have hsc : Real.sqrt (∑ v, cV v) ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt hsumC
    have hsd : Real.sqrt (∑ v, dV v) ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt hsumD
    calc (∑ v, Real.sqrt (cV v * dV v))
        ≤ Real.sqrt (∑ v, cV v) * Real.sqrt (∑ v, dV v) := hcs
      _ ≤ Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ) :=
          mul_le_mul hsc hsd (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = Real.sqrt ((n : ℝ) * (m : ℝ)) := (Real.sqrt_mul hn0 (m : ℝ)).symm

  have hC : (∑ v, Real.sqrt (dV v + 1)) ≤ 2 * Real.sqrt ((n : ℝ) * (m : ℝ)) := by
    have hsumD1 : (∑ v : Fin kv, (dV v + 1)) = (∑ v, dV v) + (kv : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
    have hkv : (kv : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
    have hsumD1le : (∑ v : Fin kv, (dV v + 1)) ≤ (m : ℝ) + (n : ℝ) := by
      rw [hsumD1]
      linarith
    have hcs := sum_sqrt_mul_le (fun v : Fin kv => dV v + 1)
      (fun _ => (1 : ℝ)) (fun v => by linarith [hdV v]) (fun _ => zero_le_one)
    simp only [mul_one] at hcs
    have hone : (∑ _v : Fin kv, (1 : ℝ)) = (kv : ℝ) := by simp
    rw [hone] at hcs
    have hsq : Real.sqrt (((m : ℝ) + (n : ℝ)) * (n : ℝ)) =
        Real.sqrt ((m : ℝ) + (n : ℝ)) * Real.sqrt (n : ℝ) :=
      Real.sqrt_mul (by linarith) (n : ℝ)
    have hbound_sq : ((m : ℝ) + (n : ℝ)) * (n : ℝ) ≤ 4 * ((m : ℝ) * (n : ℝ)) := by
      have hnm' : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
      nlinarith [hn0, hm0, hnm']
    have h4 : Real.sqrt (4 * ((m : ℝ) * (n : ℝ))) = 2 * Real.sqrt ((m : ℝ) * (n : ℝ)) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) ((m : ℝ) * (n : ℝ))]
      rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    calc (∑ v, Real.sqrt (dV v + 1))
        ≤ Real.sqrt (∑ v : Fin kv, (dV v + 1)) * Real.sqrt ((kv : ℝ)) := hcs
      _ ≤ Real.sqrt ((m : ℝ) + (n : ℝ)) * Real.sqrt (n : ℝ) :=
          mul_le_mul (Real.sqrt_le_sqrt hsumD1le) (Real.sqrt_le_sqrt hkv)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = Real.sqrt (((m : ℝ) + (n : ℝ)) * (n : ℝ)) := hsq.symm
      _ ≤ Real.sqrt (4 * ((m : ℝ) * (n : ℝ))) := Real.sqrt_le_sqrt hbound_sq
      _ = 2 * Real.sqrt ((m : ℝ) * (n : ℝ)) := h4
      _ = 2 * Real.sqrt ((n : ℝ) * (m : ℝ)) := by rw [mul_comm (m : ℝ) (n : ℝ)]

  have hsplit : (∑ v, c * (Real.sqrt (U * aV v * dV v) +
        Real.sqrt (cV v * dV v) + Real.sqrt (dV v + 1))) =
      c * ((∑ v, Real.sqrt (U * aV v * dV v)) +
        (∑ v, Real.sqrt (cV v * dV v)) + ∑ v, Real.sqrt (dV v + 1)) := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have htot : (∑ v, Real.sqrt (U * aV v * dV v)) +
        (∑ v, Real.sqrt (cV v * dV v)) + (∑ v, Real.sqrt (dV v + 1)) ≤
      3 * (Real.sqrt (U * (j : ℝ) * (A : ℝ) * (m : ℝ)) +
        Real.sqrt ((n : ℝ) * (m : ℝ))) := by
    have hR0 : (0 : ℝ) ≤ Real.sqrt (U * (j : ℝ) * (A : ℝ) * (m : ℝ)) :=
      Real.sqrt_nonneg _
    have hS0 : (0 : ℝ) ≤ Real.sqrt ((n : ℝ) * (m : ℝ)) := Real.sqrt_nonneg _
    linarith [hA, hB, hC]
  have hR : (0 : ℝ) ≤ Real.sqrt (U * (j : ℝ) * (A : ℝ) * (m : ℝ)) +
      Real.sqrt ((n : ℝ) * (m : ℝ)) := by positivity
  have hlog : (1 : ℝ) ≤ logFactor n := one_le_logFactor n
  calc (∑ v, c * (Real.sqrt (U * aV v * dV v) + Real.sqrt (cV v * dV v) +
          Real.sqrt (dV v + 1)))
      = c * ((∑ v, Real.sqrt (U * aV v * dV v)) +
          (∑ v, Real.sqrt (cV v * dV v)) + ∑ v, Real.sqrt (dV v + 1)) := hsplit
    _ ≤ c * (3 * (Real.sqrt (U * (j : ℝ) * (A : ℝ) * (m : ℝ)) +
          Real.sqrt ((n : ℝ) * (m : ℝ)))) :=
        mul_le_mul_of_nonneg_left htot hc
    _ ≤ 6 * c * (Real.sqrt (U * (j : ℝ) * (A : ℝ) * (m : ℝ)) +
          Real.sqrt ((n : ℝ) * (m : ℝ))) * logFactor n := by
        have hmul := mul_le_mul_of_nonneg_left hlog hR
        nlinarith [hR, hmul, hc]

end Qatlib.Papers.QMatchingFlow05.BlockingFlow

end

namespace Qatlib.Papers.QMatchingFlow05.BlockingFlow

open Qatlib.Papers.QMatchingFlow05.SearchTools

theorem sqrt_rpow (x : ℝ) (hx : 0 ≤ x) (a : ℝ) :
    Real.sqrt (x ^ a) = x ^ (a / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  congr 1
  ring

theorem le_rpow_one_add (x : ℝ) (hx : 1 ≤ x) (e : ℝ) (he : 0 ≤ e) :
    x ≤ x ^ (1 + e) := by
  have hx0 : 0 < x := by linarith
  rw [Real.rpow_add hx0, Real.rpow_one]
  have h1 : 1 ≤ x ^ e := Real.one_le_rpow hx he
  nlinarith [h1, hx0.le]

set_option maxHeartbeats 1600000 in

theorem theorem10_arbitraryU (c : ℝ) (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ) (U k : ℝ), 2 ≤ n → 1 ≤ U →
      (m : ℝ) ≤ (n : ℝ) ^ 2 →
      k = min ((n : ℝ) ^ ((2 : ℝ) / 3)) (Real.sqrt (m : ℝ)) → 0 < k →
      c * (k ^ ((3 : ℝ) / 2) * Real.sqrt ((m : ℝ) * U) +
          k * Real.sqrt ((n : ℝ) * (m : ℝ))) ≤
        C * c * min ((n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ))
          (Real.sqrt (n : ℝ) * (m : ℝ)) * U * logFactor n := by
  refine ⟨4, by norm_num, ?_⟩
  intro n m U k hn2 hU1 hm hkdef hk
  have hn2' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := hnpos.le
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hU0 : (0 : ℝ) < U := by linarith
  have hU0' : (0 : ℝ) ≤ U := hU0.le
  have hk_le_left : k ≤ (n : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [hkdef]; exact min_le_left _ _
  have hk_le_right : k ≤ Real.sqrt (m : ℝ) := by
    rw [hkdef]; exact min_le_right _ _

  have hsqrtU_le : Real.sqrt U ≤ U := by
    have h1 : 1 ≤ Real.sqrt U := Real.one_le_sqrt.mpr hU1
    have hmul : Real.sqrt U * Real.sqrt U = U := Real.mul_self_sqrt hU0'
    nlinarith [Real.sqrt_nonneg U, h1, hmul]

  have hn_le : (n : ℝ) ≤ (n : ℝ) ^ ((7 : ℝ) / 6) := by
    have h1 : (n : ℝ) ^ (1 : ℝ) ≤ (n : ℝ) ^ ((7 : ℝ) / 6) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
    rwa [Real.rpow_one] at h1

  have hmpos : 0 < (m : ℝ) := by
    have hspos : 0 < Real.sqrt (m : ℝ) := lt_of_lt_of_le hk hk_le_right
    exact (Real.sqrt_pos.mp hspos)
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    have : 1 ≤ m := by
      have : 0 < m := by exact_mod_cast hmpos
      omega
    exact_mod_cast this

  have hsqrtm_le_n : Real.sqrt (m : ℝ) ≤ (n : ℝ) := by
    have h : Real.sqrt (m : ℝ) ≤ Real.sqrt ((n : ℝ) ^ 2) := Real.sqrt_le_sqrt hm
    rwa [Real.sqrt_sq hn0] at h
  have hm14_eq : (m : ℝ) ^ ((1 : ℝ) / 4) = Real.sqrt (Real.sqrt (m : ℝ)) := by
    rw [Real.sqrt_eq_rpow (m : ℝ), sqrt_rpow (m : ℝ) hm0 ((1 : ℝ) / 2)]
    congr 1
    norm_num
  have hm14_le_sqrtn : (m : ℝ) ^ ((1 : ℝ) / 4) ≤ Real.sqrt (n : ℝ) := by
    rw [hm14_eq]
    exact Real.sqrt_le_sqrt hsqrtm_le_n

  have hk32_le_n : k ^ ((3 : ℝ) / 2) ≤ (n : ℝ) := by
    have hsqrt_k : Real.sqrt k ≤ (n : ℝ) ^ ((1 : ℝ) / 3) := by
      have h1 : Real.sqrt k ≤ Real.sqrt ((n : ℝ) ^ ((2 : ℝ) / 3)) := Real.sqrt_le_sqrt hk_le_left
      have h2 : Real.sqrt ((n : ℝ) ^ ((2 : ℝ) / 3)) = (n : ℝ) ^ ((1 : ℝ) / 3) := by
        rw [sqrt_rpow (n : ℝ) hn0 ((2 : ℝ) / 3)]
        congr 1
        norm_num
      rwa [h2] at h1
    rw [rpow_three_halves_eq k hk]
    calc k * Real.sqrt k
        ≤ (n : ℝ) ^ ((2 : ℝ) / 3) * (n : ℝ) ^ ((1 : ℝ) / 3) :=
          mul_le_mul hk_le_left hsqrt_k (Real.sqrt_nonneg _) (Real.rpow_nonneg hn0 _)
      _ = (n : ℝ) ^ (((2 : ℝ) / 3) + ((1 : ℝ) / 3)) := (Real.rpow_add hnpos _ _).symm
      _ = (n : ℝ) := by norm_num [Real.rpow_one]
  have hterm1a : k ^ ((3 : ℝ) / 2) * Real.sqrt ((m : ℝ) * U) ≤
      (n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ) * U := by
    have hsqrtmU : Real.sqrt ((m : ℝ) * U) = Real.sqrt (m : ℝ) * Real.sqrt U :=
      Real.sqrt_mul hm0 U
    have hstep2 : (n : ℝ) * (Real.sqrt (m : ℝ) * Real.sqrt U) ≤
        (n : ℝ) * (Real.sqrt (m : ℝ) * U) := by
      have h := mul_le_mul_of_nonneg_left hsqrtU_le (Real.sqrt_nonneg (m : ℝ))
      exact mul_le_mul_of_nonneg_left h hn0
    calc k ^ ((3 : ℝ) / 2) * Real.sqrt ((m : ℝ) * U)
        ≤ (n : ℝ) * Real.sqrt ((m : ℝ) * U) :=
          mul_le_mul_of_nonneg_right hk32_le_n (Real.sqrt_nonneg _)
      _ = (n : ℝ) * (Real.sqrt (m : ℝ) * Real.sqrt U) := by rw [hsqrtmU]
      _ ≤ (n : ℝ) * (Real.sqrt (m : ℝ) * U) := hstep2
      _ ≤ (n : ℝ) ^ ((7 : ℝ) / 6) * (Real.sqrt (m : ℝ) * U) := by
          exact mul_le_mul_of_nonneg_right hn_le
            (mul_nonneg (Real.sqrt_nonneg _) hU0')
      _ = (n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ) * U := by ring
  have hterm2a : k * Real.sqrt ((n : ℝ) * (m : ℝ)) ≤
      (n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ) * U := by
    have hsqrtnm : Real.sqrt ((n : ℝ) * (m : ℝ)) =
        Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ) := Real.sqrt_mul hn0 (m : ℝ)
    have h1 : k * Real.sqrt ((n : ℝ) * (m : ℝ)) ≤
        (n : ℝ) ^ ((2 : ℝ) / 3) * (Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ)) := by
      rw [hsqrtnm]
      exact mul_le_mul_of_nonneg_right hk_le_left (by positivity)
    have h2 : (n : ℝ) ^ ((2 : ℝ) / 3) * (Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ)) =
        (n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ) := by
      rw [show (n : ℝ) ^ ((2 : ℝ) / 3) * (Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ)) =
          ((n : ℝ) ^ ((2 : ℝ) / 3) * Real.sqrt (n : ℝ)) * Real.sqrt (m : ℝ) by ring]
      rw [rpow_seven_sixths (n : ℝ) hnpos]
    have h3 : (n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ) ≤
        (n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ) * U := by
      have hX : (0 : ℝ) ≤ (n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ) := by positivity
      nlinarith [hX, hU1]
    linarith [h1, h2, h3]
  have hbranch1 : c * (k ^ ((3 : ℝ) / 2) * Real.sqrt ((m : ℝ) * U) +
        k * Real.sqrt ((n : ℝ) * (m : ℝ))) ≤
      c * (2 * ((n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ) * U)) := by
    have hsum := add_le_add hterm1a hterm2a
    have := mul_le_mul_of_nonneg_left hsum hc
    linarith [this]

  have hk32_le_m34 : k ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ ((3 : ℝ) / 4) := by
    have hsqrtk : Real.sqrt k ≤ (m : ℝ) ^ ((1 : ℝ) / 4) := by
      have h1 : Real.sqrt k ≤ Real.sqrt (Real.sqrt (m : ℝ)) := Real.sqrt_le_sqrt hk_le_right
      rwa [← hm14_eq] at h1
    have hk_le : k ≤ (m : ℝ) ^ ((1 : ℝ) / 2) := by
      rwa [Real.sqrt_eq_rpow (m : ℝ)] at hk_le_right
    rw [rpow_three_halves_eq k hk]
    calc k * Real.sqrt k
        ≤ (m : ℝ) ^ ((1 : ℝ) / 2) * (m : ℝ) ^ ((1 : ℝ) / 4) :=
          mul_le_mul hk_le hsqrtk (Real.sqrt_nonneg _) (Real.rpow_nonneg hm0 _)
      _ = (m : ℝ) ^ (((1 : ℝ) / 2) + ((1 : ℝ) / 4)) := (Real.rpow_add hmpos _ _).symm
      _ = (m : ℝ) ^ ((3 : ℝ) / 4) := by norm_num
  have h34_le_54 : (m : ℝ) ^ ((3 : ℝ) / 4) ≤ (m : ℝ) ^ ((5 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
  have hterm1b : k ^ ((3 : ℝ) / 2) * Real.sqrt ((m : ℝ) * U) ≤
      Real.sqrt (n : ℝ) * (m : ℝ) * U := by
    have hsqrtmU : Real.sqrt ((m : ℝ) * U) = Real.sqrt (m : ℝ) * Real.sqrt U :=
      Real.sqrt_mul hm0 U
    have hstep1 : k ^ ((3 : ℝ) / 2) * Real.sqrt ((m : ℝ) * U) ≤
        (m : ℝ) ^ ((3 : ℝ) / 4) * (Real.sqrt (m : ℝ) * Real.sqrt U) := by
      rw [hsqrtmU]
      exact mul_le_mul hk32_le_m34 le_rfl (by positivity) (Real.rpow_nonneg hm0 _)
    have hstep2 : (m : ℝ) ^ ((3 : ℝ) / 4) * (Real.sqrt (m : ℝ) * Real.sqrt U) ≤
        (m : ℝ) ^ ((5 : ℝ) / 4) * Real.sqrt U := by
      have hsqrtm : Real.sqrt (m : ℝ) = (m : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow (m : ℝ)
      have heq : (m : ℝ) ^ ((3 : ℝ) / 4) * ((m : ℝ) ^ ((1 : ℝ) / 2) * Real.sqrt U) =
          (m : ℝ) ^ ((5 : ℝ) / 4) * Real.sqrt U := by
        rw [← mul_assoc, ← Real.rpow_add hmpos]
        congr 1
        norm_num
      rw [hsqrtm]
      exact le_of_eq heq
    have hstep3 : (m : ℝ) ^ ((5 : ℝ) / 4) * Real.sqrt U ≤
        ((m : ℝ) * Real.sqrt (n : ℝ)) * U := by
      have hm54 : (m : ℝ) ^ ((5 : ℝ) / 4) = (m : ℝ) * (m : ℝ) ^ ((1 : ℝ) / 4) := by
        rw [show (5 : ℝ) / 4 = 1 + 1 / 4 by norm_num, Real.rpow_add hmpos, Real.rpow_one]
      rw [hm54]
      have h1 : (m : ℝ) * (m : ℝ) ^ ((1 : ℝ) / 4) ≤ (m : ℝ) * Real.sqrt (n : ℝ) :=
        mul_le_mul_of_nonneg_left hm14_le_sqrtn hm0
      exact mul_le_mul h1 hsqrtU_le (Real.sqrt_nonneg U) (by positivity)
    calc k ^ ((3 : ℝ) / 2) * Real.sqrt ((m : ℝ) * U)
        ≤ (m : ℝ) ^ ((3 : ℝ) / 4) * (Real.sqrt (m : ℝ) * Real.sqrt U) := hstep1
      _ ≤ (m : ℝ) ^ ((5 : ℝ) / 4) * Real.sqrt U := hstep2
      _ ≤ ((m : ℝ) * Real.sqrt (n : ℝ)) * U := hstep3
      _ = Real.sqrt (n : ℝ) * (m : ℝ) * U := by ring
  have hterm2b : k * Real.sqrt ((n : ℝ) * (m : ℝ)) ≤ Real.sqrt (n : ℝ) * (m : ℝ) * U := by
    have hsqrtnm : Real.sqrt ((n : ℝ) * (m : ℝ)) =
        Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ) := Real.sqrt_mul hn0 (m : ℝ)
    have h1 : k * Real.sqrt ((n : ℝ) * (m : ℝ)) ≤
        Real.sqrt (m : ℝ) * (Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ)) := by
      rw [hsqrtnm]
      exact mul_le_mul_of_nonneg_right hk_le_right (by positivity)
    have h2 : Real.sqrt (m : ℝ) * (Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ)) =
        Real.sqrt (n : ℝ) * (m : ℝ) := by
      calc Real.sqrt (m : ℝ) * (Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ))
          = Real.sqrt (n : ℝ) * (Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ)) := by ring
        _ = Real.sqrt (n : ℝ) * (m : ℝ) := by rw [Real.mul_self_sqrt hm0]
    have h3 : Real.sqrt (n : ℝ) * (m : ℝ) ≤ Real.sqrt (n : ℝ) * (m : ℝ) * U := by
      have hX : (0 : ℝ) ≤ Real.sqrt (n : ℝ) * (m : ℝ) := by positivity
      nlinarith [hX, hU1]
    linarith [h1, h2, h3]
  have hbranch2 : c * (k ^ ((3 : ℝ) / 2) * Real.sqrt ((m : ℝ) * U) +
        k * Real.sqrt ((n : ℝ) * (m : ℝ))) ≤
      c * (2 * (Real.sqrt (n : ℝ) * (m : ℝ) * U)) := by
    have hsum := add_le_add hterm1b hterm2b
    have := mul_le_mul_of_nonneg_left hsum hc
    linarith [this]

  have hA0 : (0 : ℝ) ≤ (n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ) := by positivity
  have hB0 : (0 : ℝ) ≤ Real.sqrt (n : ℝ) * (m : ℝ) := by positivity
  have hmin2 : min (2 * c * ((n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ) * U))
      (2 * c * (Real.sqrt (n : ℝ) * (m : ℝ) * U)) =
      2 * c * min ((n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ) * U)
        (Real.sqrt (n : ℝ) * (m : ℝ) * U) := by
    rcases le_total ((n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ) * U)
      (Real.sqrt (n : ℝ) * (m : ℝ) * U) with hab | hab
    · have hle : 2 * c * ((n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ) * U) ≤
          2 * c * (Real.sqrt (n : ℝ) * (m : ℝ) * U) :=
        mul_le_mul_of_nonneg_left hab (by positivity)
      rw [min_eq_left hab, min_eq_left hle]
    · have hle : 2 * c * (Real.sqrt (n : ℝ) * (m : ℝ) * U) ≤
          2 * c * ((n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ) * U) :=
        mul_le_mul_of_nonneg_left hab (by positivity)
      rw [min_eq_right hab, min_eq_right hle]
  have hminU : min ((n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ) * U)
      (Real.sqrt (n : ℝ) * (m : ℝ) * U) =
      min ((n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ)) (Real.sqrt (n : ℝ) * (m : ℝ)) * U := by
    rcases le_total ((n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ))
        (Real.sqrt (n : ℝ) * (m : ℝ)) with hab | hab
    · have hle : (n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ) * U ≤
          Real.sqrt (n : ℝ) * (m : ℝ) * U := mul_le_mul_of_nonneg_right hab hU0'
      rw [min_eq_left hab, min_eq_left hle]
    · have hle : Real.sqrt (n : ℝ) * (m : ℝ) * U ≤
          (n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ) * U := mul_le_mul_of_nonneg_right hab hU0'
      rw [min_eq_right hab, min_eq_right hle]
  have hcost_min : c * (k ^ ((3 : ℝ) / 2) * Real.sqrt ((m : ℝ) * U) +
        k * Real.sqrt ((n : ℝ) * (m : ℝ))) ≤
      2 * c * min ((n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ)) (Real.sqrt (n : ℝ) * (m : ℝ)) * U := by
    have hb1 : c * (k ^ ((3 : ℝ) / 2) * Real.sqrt ((m : ℝ) * U) +
        k * Real.sqrt ((n : ℝ) * (m : ℝ))) ≤
        2 * c * ((n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ) * U) := by
      linarith [hbranch1]
    have hb2 : c * (k ^ ((3 : ℝ) / 2) * Real.sqrt ((m : ℝ) * U) +
        k * Real.sqrt ((n : ℝ) * (m : ℝ))) ≤
        2 * c * (Real.sqrt (n : ℝ) * (m : ℝ) * U) := by
      linarith [hbranch2]
    have hboth := le_min hb1 hb2
    rw [hmin2, hminU] at hboth
    simpa only [mul_assoc] using hboth

  have hlog : (1 : ℝ) ≤ logFactor n := one_le_logFactor n
  have hmin0 : (0 : ℝ) ≤
      min ((n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ)) (Real.sqrt (n : ℝ) * (m : ℝ)) * U :=
    mul_nonneg (le_min hA0 hB0) hU0'
  calc c * (k ^ ((3 : ℝ) / 2) * Real.sqrt ((m : ℝ) * U) +
        k * Real.sqrt ((n : ℝ) * (m : ℝ)))
      ≤ 2 * c * min ((n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ)) (Real.sqrt (n : ℝ) * (m : ℝ)) * U := hcost_min
    _ ≤ 2 * c * min ((n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ)) (Real.sqrt (n : ℝ) * (m : ℝ)) * U * logFactor n := by
        have hX : (0 : ℝ) ≤ 2 * c * min ((n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ)) (Real.sqrt (n : ℝ) * (m : ℝ)) * U := by
          have := mul_nonneg (by positivity : (0:ℝ) ≤ 2 * c) hmin0
          linarith [this]
        nlinarith [hX, hlog]
    _ ≤ 4 * c * min ((n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ)) (Real.sqrt (n : ℝ) * (m : ℝ)) * U * logFactor n := by
        have hX : (0 : ℝ) ≤ c * (min ((n : ℝ) ^ ((7 : ℝ) / 6) * Real.sqrt (m : ℝ)) (Real.sqrt (n : ℝ) * (m : ℝ)) * U * logFactor n) :=
          mul_nonneg hc (mul_nonneg hmin0 (by linarith))
        nlinarith [hX]

end Qatlib.Papers.QMatchingFlow05.BlockingFlow
