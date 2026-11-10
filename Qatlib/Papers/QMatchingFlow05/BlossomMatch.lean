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

namespace Qatlib.Papers.QMatchingFlow05.BlossomMatch

open Qatlib.Papers.QMatchingFlow05.SearchTools

theorem sqrt_div_eq (n m : ℕ) (_hn : 0 < n) :
    Real.sqrt ((m : ℝ) / (n : ℝ)) = Real.sqrt (m : ℝ) / Real.sqrt (n : ℝ) :=
  Real.sqrt_div (Nat.cast_nonneg m) (n : ℝ)

theorem n_mul_sqrt_div (n m : ℕ) (hn : 0 < n) :
    (n : ℝ) * Real.sqrt ((m : ℝ) / (n : ℝ)) = Real.sqrt ((n : ℝ) * (m : ℝ)) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hs : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn'.le
  have hspos : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn'
  rw [sqrt_div_eq n m hn]
  calc (n : ℝ) * (Real.sqrt (m : ℝ) / Real.sqrt (n : ℝ))
      = (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) *
          (Real.sqrt (m : ℝ) / Real.sqrt (n : ℝ)) := by rw [hs]
    _ = Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ) := by
        field_simp
    _ = Real.sqrt ((n : ℝ) * (m : ℝ)) := (Real.sqrt_mul hn'.le (m : ℝ)).symm

theorem n_mul_rpow_three_halves (n : ℕ) :
    (n : ℝ) * (n : ℝ) ^ ((3 : ℝ) / 2) = (n : ℝ) ^ ((5 : ℝ) / 2) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp
  · have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h
    calc (n : ℝ) * (n : ℝ) ^ ((3 : ℝ) / 2)
        = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ ((3 : ℝ) / 2) := by rw [Real.rpow_one]
      _ = (n : ℝ) ^ ((1 : ℝ) + 3 / 2) :=
          (Real.rpow_add hn (1 : ℝ) ((3 : ℝ) / 2)).symm
      _ = (n : ℝ) ^ ((5 : ℝ) / 2) := by norm_num

theorem theorem4_evenVertexSearchCost (c : ℝ) (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k n m : ℕ) (dV eV bV : Fin k → ℝ),
      k ≤ n → k ≤ m →
      (∀ v, 0 ≤ dV v) → (∀ v, 0 ≤ eV v) → (∀ v, 0 ≤ bV v) →
      (∑ v, dV v) ≤ (m : ℝ) → (∑ v, eV v) ≤ (k : ℝ) → (∑ v, bV v) ≤ (k : ℝ) →
      (∑ v, c * (Real.sqrt (dV v) + Real.sqrt (eV v * dV v) +
          Real.sqrt (bV v * dV v))) ≤
        C * c * Real.sqrt ((n : ℝ) * (m : ℝ)) := by
  refine ⟨4, by norm_num, ?_⟩
  intro k n m dV eV bV hkn hkm hdV heV hbV hsumD hsumE hsumB
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hsumD0 : (0 : ℝ) ≤ ∑ v, dV v := Finset.sum_nonneg fun v _ => hdV v
  have hsumE0 : (0 : ℝ) ≤ ∑ v, eV v := Finset.sum_nonneg fun v _ => heV v
  have hsumB0 : (0 : ℝ) ≤ ∑ v, bV v := Finset.sum_nonneg fun v _ => hbV v

  have hkn' : Real.sqrt (k : ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hkn)
  have hkm' : Real.sqrt (k : ℝ) ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hkm)
  have hsqr0 : (0 : ℝ) ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _

  have hA : (∑ v, Real.sqrt (dV v)) ≤ Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ) := by
    have hcs := sum_sqrt_mul_le dV (fun _ : Fin k => (1 : ℝ)) hdV (fun _ => zero_le_one)
    simp only [mul_one] at hcs
    have hone : (∑ _v : Fin k, (1 : ℝ)) = (k : ℝ) := by simp
    rw [hone] at hcs
    have hsd : Real.sqrt (∑ v, dV v) ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt hsumD
    calc (∑ v, Real.sqrt (dV v))
        ≤ Real.sqrt (∑ v, dV v) * Real.sqrt (k : ℝ) := hcs
      _ ≤ Real.sqrt (m : ℝ) * Real.sqrt (k : ℝ) :=
          mul_le_mul_of_nonneg_right hsd hsqr0
      _ ≤ Real.sqrt (m : ℝ) * Real.sqrt (n : ℝ) :=
          mul_le_mul_of_nonneg_left hkn' (Real.sqrt_nonneg _)
      _ = Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ) := by ring

  have hB : (∑ v, Real.sqrt (eV v * dV v)) ≤ Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ) := by
    have hcs := sum_sqrt_mul_le eV dV heV hdV
    have hse : Real.sqrt (∑ v, eV v) ≤ Real.sqrt (k : ℝ) := Real.sqrt_le_sqrt hsumE
    have hsd : Real.sqrt (∑ v, dV v) ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt hsumD
    calc (∑ v, Real.sqrt (eV v * dV v))
        ≤ Real.sqrt (∑ v, eV v) * Real.sqrt (∑ v, dV v) := hcs
      _ ≤ Real.sqrt (k : ℝ) * Real.sqrt (m : ℝ) :=
          mul_le_mul hse hsd (Real.sqrt_nonneg _) hsqr0
      _ ≤ Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ) :=
          mul_le_mul_of_nonneg_right hkn' (Real.sqrt_nonneg _)

  have hC : (∑ v, Real.sqrt (bV v * dV v)) ≤ Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ) := by
    have hcs := sum_sqrt_mul_le bV dV hbV hdV
    have hsb : Real.sqrt (∑ v, bV v) ≤ Real.sqrt (k : ℝ) := Real.sqrt_le_sqrt hsumB
    have hsd : Real.sqrt (∑ v, dV v) ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt hsumD
    calc (∑ v, Real.sqrt (bV v * dV v))
        ≤ Real.sqrt (∑ v, bV v) * Real.sqrt (∑ v, dV v) := hcs
      _ ≤ Real.sqrt (k : ℝ) * Real.sqrt (m : ℝ) :=
          mul_le_mul hsb hsd (Real.sqrt_nonneg _) hsqr0
      _ ≤ Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ) :=
          mul_le_mul_of_nonneg_right hkn' (Real.sqrt_nonneg _)
  have hsplit : (∑ v, c * (Real.sqrt (dV v) + Real.sqrt (eV v * dV v) +
        Real.sqrt (bV v * dV v))) =
      c * ((∑ v, Real.sqrt (dV v)) + (∑ v, Real.sqrt (eV v * dV v)) +
        ∑ v, Real.sqrt (bV v * dV v)) := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have htot : (∑ v, Real.sqrt (dV v)) + (∑ v, Real.sqrt (eV v * dV v)) +
        (∑ v, Real.sqrt (bV v * dV v)) ≤
      3 * (Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ)) := by linarith
  have hR : (0 : ℝ) ≤ Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hnm : Real.sqrt ((n : ℝ) * (m : ℝ)) = Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ) :=
    Real.sqrt_mul hn0 (m : ℝ)
  calc (∑ v, c * (Real.sqrt (dV v) + Real.sqrt (eV v * dV v) +
        Real.sqrt (bV v * dV v)))
      = c * ((∑ v, Real.sqrt (dV v)) + (∑ v, Real.sqrt (eV v * dV v)) +
          ∑ v, Real.sqrt (bV v * dV v)) := hsplit
    _ ≤ c * (3 * (Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ))) :=
        mul_le_mul_of_nonneg_left htot hc
    _ = 3 * c * (Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ)) := by ring
    _ ≤ 4 * c * Real.sqrt ((n : ℝ) * (m : ℝ)) := by
        rw [hnm]
        nlinarith [mul_nonneg hc hR]

theorem theorem4_adjacency (c : ℝ) (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (perPath : ℝ), 2 ≤ n → 0 ≤ perPath →
      perPath ≤ c * (n : ℝ) ^ ((3 : ℝ) / 2) * logFactor n →
      (n : ℝ) * perPath ≤ C * (n : ℝ) ^ ((5 : ℝ) / 2) * logFactor n := by
  refine ⟨c + 1, by positivity, ?_⟩
  intro n perPath hn2 hper hbound
  have hL : (0 : ℝ) ≤ logFactor n := (logFactor_pos n).le
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hstep : (n : ℝ) * perPath ≤
      (n : ℝ) * (c * (n : ℝ) ^ ((3 : ℝ) / 2) * logFactor n) :=
    mul_le_mul_of_nonneg_left hbound hn0
  have hkey : (n : ℝ) * (c * (n : ℝ) ^ ((3 : ℝ) / 2) * logFactor n) =
      c * (n : ℝ) ^ ((5 : ℝ) / 2) * logFactor n := by
    rw [← n_mul_rpow_three_halves n]
    ring
  have hpow : (0 : ℝ) ≤ (n : ℝ) ^ ((5 : ℝ) / 2) * logFactor n :=
    mul_nonneg (Real.rpow_nonneg hn0 _) hL
  calc (n : ℝ) * perPath
      ≤ (n : ℝ) * (c * (n : ℝ) ^ ((3 : ℝ) / 2) * logFactor n) := hstep
    _ = c * (n : ℝ) ^ ((5 : ℝ) / 2) * logFactor n := hkey
    _ ≤ (c + 1) * (n : ℝ) ^ ((5 : ℝ) / 2) * logFactor n := by nlinarith [hpow, hc]

theorem theorem4_list (c : ℝ) (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ) (perPath : ℝ), 2 ≤ n → n ≤ m + 1 → 0 ≤ perPath →
      perPath ≤ c * ((n : ℝ) * (Real.sqrt ((m : ℝ) / (n : ℝ)) + logFactor n)) *
        logFactor n →
      (n : ℝ) * perPath ≤
        C * (n : ℝ) ^ 2 * (Real.sqrt ((m : ℝ) / (n : ℝ)) + logFactor n) * logFactor n := by
  refine ⟨c + 1, by positivity, ?_⟩
  intro n m perPath hn2 hnm hper hbound
  have hnpos : 0 < n := by omega
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hL : (0 : ℝ) ≤ logFactor n := (logFactor_pos n).le
  have hstep : (n : ℝ) * perPath ≤
      (n : ℝ) * (c * ((n : ℝ) * (Real.sqrt ((m : ℝ) / (n : ℝ)) + logFactor n)) *
        logFactor n) := mul_le_mul_of_nonneg_left hbound hn0
  have hkey : (n : ℝ) * (c * ((n : ℝ) * (Real.sqrt ((m : ℝ) / (n : ℝ)) + logFactor n)) *
        logFactor n) =
      c * (n : ℝ) ^ 2 * (Real.sqrt ((m : ℝ) / (n : ℝ)) + logFactor n) * logFactor n := by
    ring
  have hX : (0 : ℝ) ≤ (n : ℝ) ^ 2 * (Real.sqrt ((m : ℝ) / (n : ℝ)) + logFactor n) *
      logFactor n := by positivity
  calc (n : ℝ) * perPath
      ≤ (n : ℝ) * (c * ((n : ℝ) * (Real.sqrt ((m : ℝ) / (n : ℝ)) + logFactor n)) *
          logFactor n) := hstep
    _ = c * (n : ℝ) ^ 2 * (Real.sqrt ((m : ℝ) / (n : ℝ)) + logFactor n) * logFactor n := hkey
    _ ≤ (c + 1) * (n : ℝ) ^ 2 * (Real.sqrt ((m : ℝ) / (n : ℝ)) + logFactor n) *
        logFactor n := by nlinarith [hX, hc]

end Qatlib.Papers.QMatchingFlow05.BlossomMatch

end
