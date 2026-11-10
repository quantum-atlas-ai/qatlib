/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SubsetFinding03.CliqueQueries

def cliqueMem (N : ℕ) (a : ℝ) : ℕ :=
  ⌊(N : ℝ) ^ a⌋₊

lemma cliqueMem_le (N : ℕ) (a : ℝ) :
    (cliqueMem N a : ℝ) ≤ (N : ℝ) ^ a :=
  Nat.floor_le (Real.rpow_nonneg (by positivity) _)

lemma rpow_mem_ge_two {N : ℕ} {a : ℝ} (hN : 4 ≤ N) (ha : (1 : ℝ) / 2 ≤ a) :
    2 ≤ (N : ℝ) ^ a := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have : (1 : ℕ) ≤ N := by omega
    exact_mod_cast this
  have hbase : (4 : ℝ) ^ ((1 : ℝ) / 2) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hN) (by norm_num)
  have hexp : (N : ℝ) ^ ((1 : ℝ) / 2) ≤ (N : ℝ) ^ a :=
    Real.rpow_le_rpow_of_exponent_le hN1 ha
  have h4 : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
    rw [← Real.sqrt_eq_rpow]
    norm_num
  linarith

lemma cliqueMem_ge_half {N : ℕ} {a : ℝ} (hN : 4 ≤ N) (ha : (1 : ℝ) / 2 ≤ a) :
    (N : ℝ) ^ a / 2 ≤ (cliqueMem N a : ℝ) := by
  have hx2 : 2 ≤ (N : ℝ) ^ a := rpow_mem_ge_two hN ha
  have hlt : (N : ℝ) ^ a < (cliqueMem N a : ℝ) + 1 := by
    simpa [cliqueMem] using Nat.lt_floor_add_one ((N : ℝ) ^ a)
  linarith

def directMemory (N L : ℕ) : ℕ :=
  cliqueMem N ((L : ℝ) / ((L : ℝ) + 1))

def directCost (M N L : ℕ) : ℝ :=
  (M : ℝ) ^ 2 + ((N : ℝ) / (M : ℝ)) ^ ((L : ℝ) / 2) * (M : ℝ) ^ ((3 : ℝ) / 2)

theorem directCost_le (N M L : ℕ) (hL : 1 ≤ L) (hN : 4 ≤ N)
    (hMle : (M : ℝ) ≤ (N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 1)))
    (hMge : (N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 1)) / 2 ≤ (M : ℝ)) :
    directCost M N L ≤
      (2 + (2 : ℝ) ^ ((L : ℝ) / 2)) * (N : ℝ) ^ ((2 * (L : ℝ)) / ((L : ℝ) + 1)) := by
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have : (1 : ℕ) ≤ N := by omega
    exact_mod_cast this
  have hL1R : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hden : (0 : ℝ) < (L : ℝ) + 1 := by positivity
  have ha : (1 : ℝ) / 2 ≤ (L : ℝ) / ((L : ℝ) + 1) := by
    rw [le_div_iff₀ hden]; linarith
  have hx2 : 2 ≤ (N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 1)) := rpow_mem_ge_two hN ha
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith [hMge]

  have hratio : (N : ℝ) / (M : ℝ) ≤ 2 * (N : ℝ) ^ ((1 : ℝ) / ((L : ℝ) + 1)) := by
    have hxpos : 0 < (N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 1)) := by linarith
    have h1 : (N : ℝ) / (M : ℝ) ≤ (N : ℝ) / ((N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 1)) / 2) :=
      div_le_div_of_nonneg_left hN0 (by linarith) hMge
    have h2 : (N : ℝ) / ((N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 1)) / 2) =
        2 * (N : ℝ) / (N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 1)) := by
      have hxne : (N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 1)) ≠ 0 := by linarith
      field_simp
    have h3 : (N : ℝ) / (N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 1)) =
        (N : ℝ) ^ ((1 : ℝ) / ((L : ℝ) + 1)) := by
      have h := (Real.rpow_sub hNpos 1 ((L : ℝ) / ((L : ℝ) + 1))).symm
      have hexp : (1 : ℝ) - (L : ℝ) / ((L : ℝ) + 1) = 1 / ((L : ℝ) + 1) := by
        field_simp
        ring
      simpa [Real.rpow_one, hexp] using h
    calc (N : ℝ) / (M : ℝ)
        ≤ 2 * (N : ℝ) / (N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 1)) := by rw [← h2]; exact h1
      _ = 2 * ((N : ℝ) / (N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 1))) := by ring
      _ = 2 * (N : ℝ) ^ ((1 : ℝ) / ((L : ℝ) + 1)) := by rw [h3]

  have hA : ((N : ℝ) / (M : ℝ)) ^ ((L : ℝ) / 2) ≤
      (2 : ℝ) ^ ((L : ℝ) / 2) * (N : ℝ) ^ ((L : ℝ) / (2 * ((L : ℝ) + 1))) := by
    have h1 := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (N : ℝ) / (M : ℝ)) hratio
      (by positivity : (0 : ℝ) ≤ (L : ℝ) / 2)
    have hsplit : (2 * (N : ℝ) ^ ((1 : ℝ) / ((L : ℝ) + 1))) ^ ((L : ℝ) / 2) =
        (2 : ℝ) ^ ((L : ℝ) / 2) * ((N : ℝ) ^ ((1 : ℝ) / ((L : ℝ) + 1))) ^ ((L : ℝ) / 2) :=
      Real.mul_rpow (by norm_num) (Real.rpow_nonneg hN0 _)
    have hcomb : ((N : ℝ) ^ ((1 : ℝ) / ((L : ℝ) + 1))) ^ ((L : ℝ) / 2) =
        (N : ℝ) ^ ((L : ℝ) / (2 * ((L : ℝ) + 1))) := by
      rw [← Real.rpow_mul hN0]
      congr 1
      field_simp
      try ring
    rwa [hsplit, hcomb] at h1

  have hB : (M : ℝ) ^ ((3 : ℝ) / 2) ≤
      (N : ℝ) ^ ((3 * (L : ℝ)) / (2 * ((L : ℝ) + 1))) := by
    have h1 := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (M : ℝ)) hMle
      (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 2)
    have hcomb : ((N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 1))) ^ ((3 : ℝ) / 2) =
        (N : ℝ) ^ ((3 * (L : ℝ)) / (2 * ((L : ℝ) + 1))) := by
      rw [← Real.rpow_mul hN0]
      congr 1
      field_simp
      try ring
    rwa [hcomb] at h1
  have hterm : ((N : ℝ) / (M : ℝ)) ^ ((L : ℝ) / 2) * (M : ℝ) ^ ((3 : ℝ) / 2) ≤
      (2 : ℝ) ^ ((L : ℝ) / 2) * (N : ℝ) ^ ((2 * (L : ℝ)) / ((L : ℝ) + 1)) := by
    have hexp : (L : ℝ) / (2 * ((L : ℝ) + 1)) + (3 * (L : ℝ)) / (2 * ((L : ℝ) + 1)) =
        (2 * (L : ℝ)) / ((L : ℝ) + 1) := by
      field_simp
      ring
    calc ((N : ℝ) / (M : ℝ)) ^ ((L : ℝ) / 2) * (M : ℝ) ^ ((3 : ℝ) / 2)
        ≤ ((2 : ℝ) ^ ((L : ℝ) / 2) * (N : ℝ) ^ ((L : ℝ) / (2 * ((L : ℝ) + 1)))) *
            (N : ℝ) ^ ((3 * (L : ℝ)) / (2 * ((L : ℝ) + 1))) :=
          mul_le_mul hA hB (by positivity) (by positivity)
      _ = (2 : ℝ) ^ ((L : ℝ) / 2) *
            ((N : ℝ) ^ ((L : ℝ) / (2 * ((L : ℝ) + 1))) *
              (N : ℝ) ^ ((3 * (L : ℝ)) / (2 * ((L : ℝ) + 1)))) := by ring
      _ = (2 : ℝ) ^ ((L : ℝ) / 2) *
            (N : ℝ) ^ ((L : ℝ) / (2 * ((L : ℝ) + 1)) +
              (3 * (L : ℝ)) / (2 * ((L : ℝ) + 1))) := by
          rw [← Real.rpow_add hNpos]
      _ = (2 : ℝ) ^ ((L : ℝ) / 2) * (N : ℝ) ^ ((2 * (L : ℝ)) / ((L : ℝ) + 1)) := by
          rw [hexp]

  have hM2 : (M : ℝ) ^ 2 ≤ (N : ℝ) ^ ((2 * (L : ℝ)) / ((L : ℝ) + 1)) := by
    have hexp : ((L : ℝ) / ((L : ℝ) + 1)) * ((2 : ℕ) : ℝ) =
        (2 * (L : ℝ)) / ((L : ℝ) + 1) := by
      field_simp
      try ring
    have hcomb : ((N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 1))) ^ 2 =
        (N : ℝ) ^ ((2 * (L : ℝ)) / ((L : ℝ) + 1)) := by
      rw [← Real.rpow_natCast ((N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 1))) 2]
      rw [← Real.rpow_mul hN0]
      rw [hexp]
    calc (M : ℝ) ^ 2 ≤ ((N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 1))) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hMle 2
      _ = (N : ℝ) ^ ((2 * (L : ℝ)) / ((L : ℝ) + 1)) := hcomb
  have hE0 : (0 : ℝ) ≤ (N : ℝ) ^ ((2 * (L : ℝ)) / ((L : ℝ) + 1)) :=
    Real.rpow_nonneg hN0 _
  have hstep : directCost M N L ≤
      (N : ℝ) ^ ((2 * (L : ℝ)) / ((L : ℝ) + 1)) +
        (2 : ℝ) ^ ((L : ℝ) / 2) * (N : ℝ) ^ ((2 * (L : ℝ)) / ((L : ℝ) + 1)) := by
    unfold directCost
    linarith
  have hfin : (N : ℝ) ^ ((2 * (L : ℝ)) / ((L : ℝ) + 1)) +
        (2 : ℝ) ^ ((L : ℝ) / 2) * (N : ℝ) ^ ((2 * (L : ℝ)) / ((L : ℝ) + 1)) ≤
      (2 + (2 : ℝ) ^ ((L : ℝ) / 2)) * (N : ℝ) ^ ((2 * (L : ℝ)) / ((L : ℝ) + 1)) := by
    nlinarith [hE0]
  linarith

theorem direct_cost_bound (L : ℕ) (hL : 1 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 4 ≤ N →
      directCost (directMemory N L) N L ≤
        C * (N : ℝ) ^ ((2 * (L : ℝ)) / ((L : ℝ) + 1)) := by
  refine ⟨2 + (2 : ℝ) ^ ((L : ℝ) / 2), by positivity, ?_⟩
  intro N hN
  have hden : (0 : ℝ) < (L : ℝ) + 1 := by positivity
  have hL1R : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have ha : (1 : ℝ) / 2 ≤ (L : ℝ) / ((L : ℝ) + 1) := by
    rw [le_div_iff₀ hden]; linarith
  exact directCost_le N (directMemory N L) L hL hN
    (by rw [directMemory]; exact cliqueMem_le N _)
    (by rw [directMemory]; exact cliqueMem_ge_half hN ha)

def recursiveMemory (N L : ℕ) : ℕ :=
  cliqueMem N ((L : ℝ) / ((L : ℝ) + 2))

def recursiveCost (M N L : ℕ) : ℝ :=
  (M : ℝ) ^ 2 + ((N : ℝ) / (M : ℝ)) ^ (((L : ℝ) - 1) / 2) *
    ((M : ℝ) ^ (((L : ℝ) - 1) / (L : ℝ)) * Real.sqrt (N : ℝ) + (M : ℝ) ^ ((3 : ℝ) / 2))

theorem recursiveCost_le (N M L : ℕ) (hL : 2 ≤ L) (hN : 4 ≤ N)
    (hMle : (M : ℝ) ≤ (N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 2)))
    (hMge : (N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 2)) / 2 ≤ (M : ℝ)) :
    recursiveCost M N L ≤
      (1 + (2 : ℝ) ^ (((L : ℝ) + 1) / 2)) *
        (N : ℝ) ^ ((5 * (L : ℝ) - 2) / (2 * (L : ℝ) + 4)) := by
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have : (1 : ℕ) ≤ N := by omega
    exact_mod_cast this
  have hL1R : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast (by omega : 1 ≤ L)
  have hL2R : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hden : (0 : ℝ) < (L : ℝ) + 2 := by positivity
  have ha : (1 : ℝ) / 2 ≤ (L : ℝ) / ((L : ℝ) + 2) := by
    rw [le_div_iff₀ hden]; linarith
  have hx2 : 2 ≤ (N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 2)) := rpow_mem_ge_two hN ha
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith [hMge]

  have hratio : (N : ℝ) / (M : ℝ) ≤ 2 * (N : ℝ) ^ ((2 : ℝ) / ((L : ℝ) + 2)) := by
    have hxpos : 0 < (N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 2)) := by linarith
    have h1 : (N : ℝ) / (M : ℝ) ≤ (N : ℝ) / ((N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 2)) / 2) :=
      div_le_div_of_nonneg_left hN0 (by linarith) hMge
    have h2 : (N : ℝ) / ((N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 2)) / 2) =
        2 * (N : ℝ) / (N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 2)) := by
      have hxne : (N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 2)) ≠ 0 := by linarith
      field_simp
    have h3 : (N : ℝ) / (N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 2)) =
        (N : ℝ) ^ ((2 : ℝ) / ((L : ℝ) + 2)) := by
      have h := (Real.rpow_sub hNpos 1 ((L : ℝ) / ((L : ℝ) + 2))).symm
      have hexp : (1 : ℝ) - (L : ℝ) / ((L : ℝ) + 2) = 2 / ((L : ℝ) + 2) := by
        field_simp
        ring
      simpa [Real.rpow_one, hexp] using h
    calc (N : ℝ) / (M : ℝ)
        ≤ 2 * (N : ℝ) / (N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 2)) := by rw [← h2]; exact h1
      _ = 2 * ((N : ℝ) / (N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 2))) := by ring
      _ = 2 * (N : ℝ) ^ ((2 : ℝ) / ((L : ℝ) + 2)) := by rw [h3]

  have hR : ((N : ℝ) / (M : ℝ)) ^ (((L : ℝ) - 1) / 2) ≤
      (2 : ℝ) ^ (((L : ℝ) - 1) / 2) * (N : ℝ) ^ (((L : ℝ) - 1) / ((L : ℝ) + 2)) := by
    have h1 := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (N : ℝ) / (M : ℝ)) hratio
      (by positivity : (0 : ℝ) ≤ ((L : ℝ) - 1) / 2)
    have hsplit : (2 * (N : ℝ) ^ ((2 : ℝ) / ((L : ℝ) + 2))) ^ (((L : ℝ) - 1) / 2) =
        (2 : ℝ) ^ (((L : ℝ) - 1) / 2) *
          ((N : ℝ) ^ ((2 : ℝ) / ((L : ℝ) + 2))) ^ (((L : ℝ) - 1) / 2) :=
      Real.mul_rpow (by norm_num) (Real.rpow_nonneg hN0 _)
    have hcomb : ((N : ℝ) ^ ((2 : ℝ) / ((L : ℝ) + 2))) ^ (((L : ℝ) - 1) / 2) =
        (N : ℝ) ^ (((L : ℝ) - 1) / ((L : ℝ) + 2)) := by
      rw [← Real.rpow_mul hN0]
      congr 1
      field_simp
      try ring
    rwa [hsplit, hcomb] at h1

  have hMA : (M : ℝ) ^ (((L : ℝ) - 1) / (L : ℝ)) ≤
      (N : ℝ) ^ (((L : ℝ) - 1) / ((L : ℝ) + 2)) := by
    have h1 := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (M : ℝ)) hMle
      (by positivity : (0 : ℝ) ≤ ((L : ℝ) - 1) / (L : ℝ))
    have hcomb : ((N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 2))) ^ (((L : ℝ) - 1) / (L : ℝ)) =
        (N : ℝ) ^ (((L : ℝ) - 1) / ((L : ℝ) + 2)) := by
      rw [← Real.rpow_mul hN0]
      congr 1
      field_simp
      try ring
    rwa [hcomb] at h1

  have hMB : (M : ℝ) ^ ((3 : ℝ) / 2) ≤
      (N : ℝ) ^ ((3 * (L : ℝ)) / (2 * ((L : ℝ) + 2))) := by
    have h1 := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (M : ℝ)) hMle
      (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 2)
    have hcomb : ((N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 2))) ^ ((3 : ℝ) / 2) =
        (N : ℝ) ^ ((3 * (L : ℝ)) / (2 * ((L : ℝ) + 2))) := by
      rw [← Real.rpow_mul hN0]
      congr 1
      field_simp
      try ring
    rwa [hcomb] at h1
  have hsqrt : Real.sqrt (N : ℝ) = (N : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _

  have hAterm : ((N : ℝ) / (M : ℝ)) ^ (((L : ℝ) - 1) / 2) *
      ((M : ℝ) ^ (((L : ℝ) - 1) / (L : ℝ)) * Real.sqrt (N : ℝ)) ≤
      (2 : ℝ) ^ (((L : ℝ) - 1) / 2) *
        (N : ℝ) ^ ((5 * (L : ℝ) - 2) / (2 * (L : ℝ) + 4)) := by
    have hexp : ((L : ℝ) - 1) / ((L : ℝ) + 2) + (((L : ℝ) - 1) / ((L : ℝ) + 2) + (1 : ℝ) / 2) =
        (5 * (L : ℝ) - 2) / (2 * (L : ℝ) + 4) := by
      field_simp
      ring
    have hrepr : ((L : ℝ) - 1) / ((L : ℝ) + 2) + (((L : ℝ) - 1) / ((L : ℝ) + 2) + (1 : ℝ) / 2) =
        ((L : ℝ) - 1) / ((L : ℝ) + 2) + ((L : ℝ) - 1) / ((L : ℝ) + 2) + (1 : ℝ) / 2 := by
      ring
    have hprod : ((N : ℝ) / (M : ℝ)) ^ (((L : ℝ) - 1) / 2) *
        ((M : ℝ) ^ (((L : ℝ) - 1) / (L : ℝ)) * Real.sqrt (N : ℝ)) ≤
        ((2 : ℝ) ^ (((L : ℝ) - 1) / 2) * (N : ℝ) ^ (((L : ℝ) - 1) / ((L : ℝ) + 2))) *
          ((N : ℝ) ^ (((L : ℝ) - 1) / ((L : ℝ) + 2)) * (N : ℝ) ^ ((1 : ℝ) / 2)) := by
      rw [hsqrt]
      exact mul_le_mul hR (mul_le_mul hMA (le_refl _) (by positivity) (by positivity))
        (by positivity) (by positivity)
    calc ((N : ℝ) / (M : ℝ)) ^ (((L : ℝ) - 1) / 2) *
          ((M : ℝ) ^ (((L : ℝ) - 1) / (L : ℝ)) * Real.sqrt (N : ℝ))
        ≤ _ := hprod
      _ = (2 : ℝ) ^ (((L : ℝ) - 1) / 2) *
            ((N : ℝ) ^ (((L : ℝ) - 1) / ((L : ℝ) + 2)) *
              (((N : ℝ) ^ (((L : ℝ) - 1) / ((L : ℝ) + 2)) * (N : ℝ) ^ ((1 : ℝ) / 2)))) := by ring
      _ = (2 : ℝ) ^ (((L : ℝ) - 1) / 2) *
            (N : ℝ) ^ (((L : ℝ) - 1) / ((L : ℝ) + 2) +
              (((L : ℝ) - 1) / ((L : ℝ) + 2) + (1 : ℝ) / 2)) := by
          rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
      _ = (2 : ℝ) ^ (((L : ℝ) - 1) / 2) *
            (N : ℝ) ^ ((5 * (L : ℝ) - 2) / (2 * (L : ℝ) + 4)) := by
          rw [hexp]

  have hBterm : ((N : ℝ) / (M : ℝ)) ^ (((L : ℝ) - 1) / 2) * (M : ℝ) ^ ((3 : ℝ) / 2) ≤
      (2 : ℝ) ^ (((L : ℝ) - 1) / 2) *
        (N : ℝ) ^ ((5 * (L : ℝ) - 2) / (2 * (L : ℝ) + 4)) := by
    have hexp : ((L : ℝ) - 1) / ((L : ℝ) + 2) + (3 * (L : ℝ)) / (2 * ((L : ℝ) + 2)) =
        (5 * (L : ℝ) - 2) / (2 * (L : ℝ) + 4) := by
      field_simp
      ring
    have hprod : ((N : ℝ) / (M : ℝ)) ^ (((L : ℝ) - 1) / 2) * (M : ℝ) ^ ((3 : ℝ) / 2) ≤
        ((2 : ℝ) ^ (((L : ℝ) - 1) / 2) * (N : ℝ) ^ (((L : ℝ) - 1) / ((L : ℝ) + 2))) *
          (N : ℝ) ^ ((3 * (L : ℝ)) / (2 * ((L : ℝ) + 2))) :=
      mul_le_mul hR hMB (by positivity) (by positivity)
    calc ((N : ℝ) / (M : ℝ)) ^ (((L : ℝ) - 1) / 2) * (M : ℝ) ^ ((3 : ℝ) / 2)
        ≤ _ := hprod
      _ = (2 : ℝ) ^ (((L : ℝ) - 1) / 2) *
            ((N : ℝ) ^ (((L : ℝ) - 1) / ((L : ℝ) + 2)) *
              (N : ℝ) ^ ((3 * (L : ℝ)) / (2 * ((L : ℝ) + 2)))) := by ring
      _ = (2 : ℝ) ^ (((L : ℝ) - 1) / 2) *
            (N : ℝ) ^ (((L : ℝ) - 1) / ((L : ℝ) + 2) +
              (3 * (L : ℝ)) / (2 * ((L : ℝ) + 2))) := by
          rw [← Real.rpow_add hNpos]
      _ = (2 : ℝ) ^ (((L : ℝ) - 1) / 2) *
            (N : ℝ) ^ ((5 * (L : ℝ) - 2) / (2 * (L : ℝ) + 4)) := by
          rw [hexp]

  have hM2 : (M : ℝ) ^ 2 ≤ (N : ℝ) ^ ((5 * (L : ℝ) - 2) / (2 * (L : ℝ) + 4)) := by
    have hbase : ((N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 2))) ^ 2 =
        (N : ℝ) ^ ((2 * (L : ℝ)) / ((L : ℝ) + 2)) := by
      have hexp : ((L : ℝ) / ((L : ℝ) + 2)) * ((2 : ℕ) : ℝ) =
          (2 * (L : ℝ)) / ((L : ℝ) + 2) := by
        field_simp
        try ring
      rw [← Real.rpow_natCast ((N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 2))) 2]
      rw [← Real.rpow_mul hN0]
      rw [hexp]
    have hmono : (N : ℝ) ^ ((2 * (L : ℝ)) / ((L : ℝ) + 2)) ≤
        (N : ℝ) ^ ((5 * (L : ℝ) - 2) / (2 * (L : ℝ) + 4)) := by
      apply Real.rpow_le_rpow_of_exponent_le hN1
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (L : ℝ) + 2)
        (by positivity : (0 : ℝ) < 2 * (L : ℝ) + 4)]
      nlinarith [hL2R]
    calc (M : ℝ) ^ 2 ≤ ((N : ℝ) ^ ((L : ℝ) / ((L : ℝ) + 2))) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hMle 2
      _ = (N : ℝ) ^ ((2 * (L : ℝ)) / ((L : ℝ) + 2)) := hbase
      _ ≤ (N : ℝ) ^ ((5 * (L : ℝ) - 2) / (2 * (L : ℝ) + 4)) := hmono
  have hE0 : (0 : ℝ) ≤ (N : ℝ) ^ ((5 * (L : ℝ) - 2) / (2 * (L : ℝ) + 4)) :=
    Real.rpow_nonneg hN0 _
  have hstep : recursiveCost M N L ≤
      (N : ℝ) ^ ((5 * (L : ℝ) - 2) / (2 * (L : ℝ) + 4)) +
        ((2 : ℝ) ^ (((L : ℝ) - 1) / 2) * (N : ℝ) ^ ((5 * (L : ℝ) - 2) / (2 * (L : ℝ) + 4)) +
          (2 : ℝ) ^ (((L : ℝ) - 1) / 2) * (N : ℝ) ^ ((5 * (L : ℝ) - 2) / (2 * (L : ℝ) + 4))) := by
    unfold recursiveCost
    linarith
  have hfin : (N : ℝ) ^ ((5 * (L : ℝ) - 2) / (2 * (L : ℝ) + 4)) +
        ((2 : ℝ) ^ (((L : ℝ) - 1) / 2) * (N : ℝ) ^ ((5 * (L : ℝ) - 2) / (2 * (L : ℝ) + 4)) +
          (2 : ℝ) ^ (((L : ℝ) - 1) / 2) * (N : ℝ) ^ ((5 * (L : ℝ) - 2) / (2 * (L : ℝ) + 4))) ≤
      (1 + (2 : ℝ) ^ (((L : ℝ) + 1) / 2)) *
        (N : ℝ) ^ ((5 * (L : ℝ) - 2) / (2 * (L : ℝ) + 4)) := by
    have h2pow : (2 : ℝ) ^ (((L : ℝ) + 1) / 2) =
        2 * (2 : ℝ) ^ (((L : ℝ) - 1) / 2) := by
      rw [show ((L : ℝ) + 1) / 2 = ((L : ℝ) - 1) / 2 + 1 by ring]
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      rw [Real.rpow_one]
      ring
    rw [h2pow]
    nlinarith [hE0]
  linarith

theorem recursive_cost_bound (L : ℕ) (hL : 2 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 4 ≤ N →
      recursiveCost (recursiveMemory N L) N L ≤
        C * (N : ℝ) ^ ((5 * (L : ℝ) - 2) / (2 * (L : ℝ) + 4)) := by
  refine ⟨1 + (2 : ℝ) ^ (((L : ℝ) + 1) / 2), by positivity, ?_⟩
  intro N hN
  have hden : (0 : ℝ) < (L : ℝ) + 2 := by positivity
  have hL1R : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast (by omega : 1 ≤ L)
  have hL2R : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have ha : (1 : ℝ) / 2 ≤ (L : ℝ) / ((L : ℝ) + 2) := by
    rw [le_div_iff₀ hden]; linarith
  exact recursiveCost_le N (recursiveMemory N L) L hL hN
    (by rw [recursiveMemory]; exact cliqueMem_le N _)
    (by rw [recursiveMemory]; exact cliqueMem_ge_half hN ha)

def noteAddedMemory (N L : ℕ) : ℕ :=
  cliqueMem N (((L : ℝ) - 1) / (L : ℝ))

theorem note_added_cost_bound (L : ℕ) (hL : 2 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 4 ≤ N →
      recursiveCost (noteAddedMemory N L) N L ≤
        C * (N : ℝ) ^ ((2 * ((L : ℝ) - 1)) / (L : ℝ)) := by
  refine ⟨1 + (2 : ℝ) ^ (((L : ℝ) + 1) / 2), by positivity, ?_⟩
  intro N hN
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have : (1 : ℕ) ≤ N := by omega
    exact_mod_cast this
  have hL1R : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast (by omega : 1 ≤ L)
  have hL2R : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  have ha : (1 : ℝ) / 2 ≤ ((L : ℝ) - 1) / (L : ℝ) := by
    rw [le_div_iff₀ hLpos]; linarith
  set M : ℕ := noteAddedMemory N L with hM
  have hMle : (M : ℝ) ≤ (N : ℝ) ^ (((L : ℝ) - 1) / (L : ℝ)) := by
    rw [hM]; exact cliqueMem_le N _
  have hMge : (N : ℝ) ^ (((L : ℝ) - 1) / (L : ℝ)) / 2 ≤ (M : ℝ) := by
    rw [hM]; exact cliqueMem_ge_half hN ha
  have hx2 : 2 ≤ (N : ℝ) ^ (((L : ℝ) - 1) / (L : ℝ)) := rpow_mem_ge_two hN ha
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith

  have hratio : (N : ℝ) / (M : ℝ) ≤ 2 * (N : ℝ) ^ ((1 : ℝ) / (L : ℝ)) := by
    have hxpos : 0 < (N : ℝ) ^ (((L : ℝ) - 1) / (L : ℝ)) := by linarith
    have h1 : (N : ℝ) / (M : ℝ) ≤ (N : ℝ) / ((N : ℝ) ^ (((L : ℝ) - 1) / (L : ℝ)) / 2) :=
      div_le_div_of_nonneg_left hN0 (by linarith) hMge
    have h2 : (N : ℝ) / ((N : ℝ) ^ (((L : ℝ) - 1) / (L : ℝ)) / 2) =
        2 * (N : ℝ) / (N : ℝ) ^ (((L : ℝ) - 1) / (L : ℝ)) := by
      have hxne : (N : ℝ) ^ (((L : ℝ) - 1) / (L : ℝ)) ≠ 0 := by linarith
      field_simp
    have h3 : (N : ℝ) / (N : ℝ) ^ (((L : ℝ) - 1) / (L : ℝ)) =
        (N : ℝ) ^ ((1 : ℝ) / (L : ℝ)) := by
      have h := (Real.rpow_sub hNpos 1 (((L : ℝ) - 1) / (L : ℝ))).symm
      have hexp : (1 : ℝ) - ((L : ℝ) - 1) / (L : ℝ) = 1 / (L : ℝ) := by
        field_simp
        ring
      simpa [Real.rpow_one, hexp] using h
    calc (N : ℝ) / (M : ℝ)
        ≤ 2 * (N : ℝ) / (N : ℝ) ^ (((L : ℝ) - 1) / (L : ℝ)) := by rw [← h2]; exact h1
      _ = 2 * ((N : ℝ) / (N : ℝ) ^ (((L : ℝ) - 1) / (L : ℝ))) := by ring
      _ = 2 * (N : ℝ) ^ ((1 : ℝ) / (L : ℝ)) := by rw [h3]

  have hR : ((N : ℝ) / (M : ℝ)) ^ (((L : ℝ) - 1) / 2) ≤
      (2 : ℝ) ^ (((L : ℝ) - 1) / 2) * (N : ℝ) ^ (((L : ℝ) - 1) / (2 * (L : ℝ))) := by
    have h1 := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (N : ℝ) / (M : ℝ)) hratio
      (by positivity : (0 : ℝ) ≤ ((L : ℝ) - 1) / 2)
    have hsplit : (2 * (N : ℝ) ^ ((1 : ℝ) / (L : ℝ))) ^ (((L : ℝ) - 1) / 2) =
        (2 : ℝ) ^ (((L : ℝ) - 1) / 2) *
          ((N : ℝ) ^ ((1 : ℝ) / (L : ℝ))) ^ (((L : ℝ) - 1) / 2) :=
      Real.mul_rpow (by norm_num) (Real.rpow_nonneg hN0 _)
    have hcomb : ((N : ℝ) ^ ((1 : ℝ) / (L : ℝ))) ^ (((L : ℝ) - 1) / 2) =
        (N : ℝ) ^ (((L : ℝ) - 1) / (2 * (L : ℝ))) := by
      rw [← Real.rpow_mul hN0]
      congr 1
      field_simp
      try ring
    rwa [hsplit, hcomb] at h1

  have hMA : (M : ℝ) ^ (((L : ℝ) - 1) / (L : ℝ)) ≤
      (N : ℝ) ^ (((L : ℝ) - 1) * ((L : ℝ) - 1) / (L : ℝ) ^ 2) := by
    have h1 := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (M : ℝ)) hMle
      (by positivity : (0 : ℝ) ≤ ((L : ℝ) - 1) / (L : ℝ))
    have hcomb : ((N : ℝ) ^ (((L : ℝ) - 1) / (L : ℝ))) ^ (((L : ℝ) - 1) / (L : ℝ)) =
        (N : ℝ) ^ (((L : ℝ) - 1) * ((L : ℝ) - 1) / (L : ℝ) ^ 2) := by
      rw [← Real.rpow_mul hN0]
      congr 1
      field_simp
      try ring
    rwa [hcomb] at h1

  have hMB : (M : ℝ) ^ ((3 : ℝ) / 2) ≤
      (N : ℝ) ^ ((3 * ((L : ℝ) - 1)) / (2 * (L : ℝ))) := by
    have h1 := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (M : ℝ)) hMle
      (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 2)
    have hcomb : ((N : ℝ) ^ (((L : ℝ) - 1) / (L : ℝ))) ^ ((3 : ℝ) / 2) =
        (N : ℝ) ^ ((3 * ((L : ℝ) - 1)) / (2 * (L : ℝ))) := by
      rw [← Real.rpow_mul hN0]
      congr 1
      field_simp
      try ring
    rwa [hcomb] at h1
  have hsqrt : Real.sqrt (N : ℝ) = (N : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _

  have hAterm : ((N : ℝ) / (M : ℝ)) ^ (((L : ℝ) - 1) / 2) *
      ((M : ℝ) ^ (((L : ℝ) - 1) / (L : ℝ)) * Real.sqrt (N : ℝ)) ≤
      (2 : ℝ) ^ (((L : ℝ) - 1) / 2) *
        (N : ℝ) ^ ((2 * ((L : ℝ) - 1)) / (L : ℝ)) := by
    have hpexp : ((L : ℝ) - 1) / (2 * (L : ℝ)) +
        (((L : ℝ) - 1) * ((L : ℝ) - 1) / (L : ℝ) ^ 2 + (1 : ℝ) / 2) ≤
        (2 * ((L : ℝ) - 1)) / (L : ℝ) := by
      field_simp
      nlinarith [hL1R, hL2R, hLpos]
    have hprod : ((N : ℝ) / (M : ℝ)) ^ (((L : ℝ) - 1) / 2) *
        ((M : ℝ) ^ (((L : ℝ) - 1) / (L : ℝ)) * Real.sqrt (N : ℝ)) ≤
        ((2 : ℝ) ^ (((L : ℝ) - 1) / 2) * (N : ℝ) ^ (((L : ℝ) - 1) / (2 * (L : ℝ)))) *
          ((N : ℝ) ^ (((L : ℝ) - 1) * ((L : ℝ) - 1) / (L : ℝ) ^ 2) *
            (N : ℝ) ^ ((1 : ℝ) / 2)) := by
      rw [hsqrt]
      exact mul_le_mul hR (mul_le_mul hMA (le_refl _) (by positivity) (by positivity))
        (by positivity) (by positivity)
    calc ((N : ℝ) / (M : ℝ)) ^ (((L : ℝ) - 1) / 2) *
          ((M : ℝ) ^ (((L : ℝ) - 1) / (L : ℝ)) * Real.sqrt (N : ℝ))
        ≤ _ := hprod
      _ = (2 : ℝ) ^ (((L : ℝ) - 1) / 2) *
            ((N : ℝ) ^ (((L : ℝ) - 1) / (2 * (L : ℝ))) *
              ((N : ℝ) ^ (((L : ℝ) - 1) * ((L : ℝ) - 1) / (L : ℝ) ^ 2) *
                (N : ℝ) ^ ((1 : ℝ) / 2))) := by ring
      _ = (2 : ℝ) ^ (((L : ℝ) - 1) / 2) *
            (N : ℝ) ^ (((L : ℝ) - 1) / (2 * (L : ℝ)) +
              (((L : ℝ) - 1) * ((L : ℝ) - 1) / (L : ℝ) ^ 2 + (1 : ℝ) / 2)) := by
          rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
      _ ≤ (2 : ℝ) ^ (((L : ℝ) - 1) / 2) *
            (N : ℝ) ^ ((2 * ((L : ℝ) - 1)) / (L : ℝ)) := by
          have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ (((L : ℝ) - 1) / 2) :=
            Real.rpow_nonneg (by norm_num) _
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hN1 hpexp) hpos

  have hBterm : ((N : ℝ) / (M : ℝ)) ^ (((L : ℝ) - 1) / 2) * (M : ℝ) ^ ((3 : ℝ) / 2) ≤
      (2 : ℝ) ^ (((L : ℝ) - 1) / 2) *
        (N : ℝ) ^ ((2 * ((L : ℝ) - 1)) / (L : ℝ)) := by
    have hexp : ((L : ℝ) - 1) / (2 * (L : ℝ)) + (3 * ((L : ℝ) - 1)) / (2 * (L : ℝ)) =
        (2 * ((L : ℝ) - 1)) / (L : ℝ) := by
      field_simp
      ring
    have hprod : ((N : ℝ) / (M : ℝ)) ^ (((L : ℝ) - 1) / 2) * (M : ℝ) ^ ((3 : ℝ) / 2) ≤
        ((2 : ℝ) ^ (((L : ℝ) - 1) / 2) * (N : ℝ) ^ (((L : ℝ) - 1) / (2 * (L : ℝ)))) *
          (N : ℝ) ^ ((3 * ((L : ℝ) - 1)) / (2 * (L : ℝ))) :=
      mul_le_mul hR hMB (by positivity) (by positivity)
    calc ((N : ℝ) / (M : ℝ)) ^ (((L : ℝ) - 1) / 2) * (M : ℝ) ^ ((3 : ℝ) / 2)
        ≤ _ := hprod
      _ = (2 : ℝ) ^ (((L : ℝ) - 1) / 2) *
            ((N : ℝ) ^ (((L : ℝ) - 1) / (2 * (L : ℝ))) *
              (N : ℝ) ^ ((3 * ((L : ℝ) - 1)) / (2 * (L : ℝ)))) := by ring
      _ = (2 : ℝ) ^ (((L : ℝ) - 1) / 2) *
            (N : ℝ) ^ (((L : ℝ) - 1) / (2 * (L : ℝ)) +
              (3 * ((L : ℝ) - 1)) / (2 * (L : ℝ))) := by
          rw [← Real.rpow_add hNpos]
      _ = (2 : ℝ) ^ (((L : ℝ) - 1) / 2) *
            (N : ℝ) ^ ((2 * ((L : ℝ) - 1)) / (L : ℝ)) := by
          rw [hexp]

  have hM2 : (M : ℝ) ^ 2 ≤ (N : ℝ) ^ ((2 * ((L : ℝ) - 1)) / (L : ℝ)) := by
    have hbase : ((N : ℝ) ^ (((L : ℝ) - 1) / (L : ℝ))) ^ 2 =
        (N : ℝ) ^ ((2 * ((L : ℝ) - 1)) / (L : ℝ)) := by
      have hexp : (((L : ℝ) - 1) / (L : ℝ)) * ((2 : ℕ) : ℝ) =
          (2 * ((L : ℝ) - 1)) / (L : ℝ) := by
        field_simp
        try ring
      rw [← Real.rpow_natCast ((N : ℝ) ^ (((L : ℝ) - 1) / (L : ℝ))) 2]
      rw [← Real.rpow_mul hN0]
      rw [hexp]
    calc (M : ℝ) ^ 2 ≤ ((N : ℝ) ^ (((L : ℝ) - 1) / (L : ℝ))) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hMle 2
      _ = (N : ℝ) ^ ((2 * ((L : ℝ) - 1)) / (L : ℝ)) := hbase
  have hE0 : (0 : ℝ) ≤ (N : ℝ) ^ ((2 * ((L : ℝ) - 1)) / (L : ℝ)) := Real.rpow_nonneg hN0 _
  have hstep : recursiveCost (noteAddedMemory N L) N L ≤
      (N : ℝ) ^ ((2 * ((L : ℝ) - 1)) / (L : ℝ)) +
        ((2 : ℝ) ^ (((L : ℝ) - 1) / 2) * (N : ℝ) ^ ((2 * ((L : ℝ) - 1)) / (L : ℝ)) +
          (2 : ℝ) ^ (((L : ℝ) - 1) / 2) * (N : ℝ) ^ ((2 * ((L : ℝ) - 1)) / (L : ℝ))) := by
    rw [← hM]
    unfold recursiveCost
    linarith
  have hfin : (N : ℝ) ^ ((2 * ((L : ℝ) - 1)) / (L : ℝ)) +
        ((2 : ℝ) ^ (((L : ℝ) - 1) / 2) * (N : ℝ) ^ ((2 * ((L : ℝ) - 1)) / (L : ℝ)) +
          (2 : ℝ) ^ (((L : ℝ) - 1) / 2) * (N : ℝ) ^ ((2 * ((L : ℝ) - 1)) / (L : ℝ))) ≤
      (1 + (2 : ℝ) ^ (((L : ℝ) + 1) / 2)) *
        (N : ℝ) ^ ((2 * ((L : ℝ) - 1)) / (L : ℝ)) := by
    have h2pow : (2 : ℝ) ^ (((L : ℝ) + 1) / 2) =
        2 * (2 : ℝ) ^ (((L : ℝ) - 1) / 2) := by
      rw [show ((L : ℝ) + 1) / 2 = ((L : ℝ) - 1) / 2 + 1 by ring]
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      rw [Real.rpow_one]
      ring
    rw [h2pow]
    nlinarith [hE0]
  linarith

theorem noteAdded_subsumes_direct (L : ℕ) (hL : 1 ≤ L) :
    (2 * ((L : ℝ) - 1)) / (L : ℝ) ≤ (2 * (L : ℝ)) / ((L : ℝ) + 1) := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  rw [div_le_div_iff₀ hLpos (by positivity : (0 : ℝ) < (L : ℝ) + 1)]
  nlinarith

theorem table_one_comparisons :
    ((5 * (3 : ℝ) - 2) / (2 * 3 + 4) < (2 * 3) / (3 + 1)) ∧
    ((5 * (4 : ℝ) - 2) / (2 * 4 + 4) < (2 * 4) / (4 + 1)) ∧
    ((5 * (5 : ℝ) - 2) / (2 * 5 + 4) < (2 * 5) / (5 + 1)) ∧
    ((2 * 6) / (6 + 1) < (5 * (6 : ℝ) - 2) / (2 * 6 + 4)) := by
  norm_num

theorem noteAdded_improves_recursive_at_five :
    (2 * ((5 : ℝ) - 1)) / (5 : ℝ) < (5 * (5 : ℝ) - 2) / (2 * 5 + 4) := by
  norm_num

end Qatlib.Papers.SubsetFinding03.CliqueQueries
