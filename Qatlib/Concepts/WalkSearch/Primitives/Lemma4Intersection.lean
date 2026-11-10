/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Concepts.WalkSearch.Primitives

variable {n : ℕ}

def avoidingSubsets (X : Finset (Fin n)) (m : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ.powersetCard m).filter fun Y => Disjoint Y X

theorem avoidingSubsets_card (X : Finset (Fin n)) (m : ℕ) :
    (avoidingSubsets X m).card = (n - X.card).choose m := by
  have h : avoidingSubsets X m = (Finset.univ \ X).powersetCard m := by
    ext Y
    simp only [avoidingSubsets, Finset.mem_filter, Finset.mem_powersetCard,
      Finset.subset_sdiff, Finset.subset_univ, true_and]
    exact and_comm
  rw [h, Finset.card_powersetCard, Finset.card_sdiff, Finset.card_univ,
    Fintype.card_fin, Finset.inter_univ]

theorem subsetSpace_card (m : ℕ) :
    (Finset.univ.powersetCard m : Finset (Finset (Fin n))).card = n.choose m := by
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

def emptyProb (X : Finset (Fin n)) (m : ℕ) : ℝ :=
  ((avoidingSubsets X m).card : ℝ) / (n.choose m : ℝ)

theorem emptyProb_eq_choose_ratio (X : Finset (Fin n)) (m : ℕ) :
    emptyProb X m = ((n - X.card).choose m : ℝ) / (n.choose m : ℝ) := by
  simp only [emptyProb, avoidingSubsets_card]

theorem choose_cast_eq_prod_div {m : ℕ} (hm : m ≤ n) :
    (n.choose m : ℝ) = (∏ i ∈ Finset.range m, ((n : ℝ) - (i : ℝ))) / (m.factorial : ℝ) := by
  have h1 : ((n.descFactorial m : ℕ) : ℝ) = (m.factorial : ℝ) * (n.choose m : ℝ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  have h2 : ((n.descFactorial m : ℕ) : ℝ) =
      ∏ i ∈ Finset.range m, ((n : ℝ) - (i : ℝ)) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Nat.cast_sub (le_of_lt ((Finset.mem_range.mp hi).trans_le hm))]
  rw [h2] at h1
  have hf : (m.factorial : ℝ) ≠ 0 := by
    have := Nat.factorial_ne_zero m
    positivity
  rw [eq_div_iff hf]
  linarith [h1]

theorem emptyProb_eq_prod_ratio (X : Finset (Fin n)) {m : ℕ} (hmn : m ≤ n)
    (hmk : m ≤ n - X.card) :
    emptyProb X m =
      (∏ i ∈ Finset.range m, ((n : ℝ) - (X.card : ℝ) - (i : ℝ))) /
        (∏ i ∈ Finset.range m, ((n : ℝ) - (i : ℝ))) := by
  have hk : X.card ≤ n := by
    simpa using X.card_le_univ
  have hcast : (∏ i ∈ Finset.range m, (((n - X.card : ℕ) : ℝ) - (i : ℝ))) =
      ∏ i ∈ Finset.range m, ((n : ℝ) - (X.card : ℝ) - (i : ℝ)) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Nat.cast_sub hk]
  rw [emptyProb_eq_choose_ratio, choose_cast_eq_prod_div hmn,
    choose_cast_eq_prod_div hmk, hcast]
  have hf : (m.factorial : ℝ) ≠ 0 := by
    have := Nat.factorial_ne_zero m
    positivity
  rw [div_div_div_cancel_right₀ hf]

theorem emptyProb_le_pow (X : Finset (Fin n)) {m : ℕ} (hn : 0 < n) (hmn : m ≤ n)
    (hmk : m + X.card ≤ n) :
    emptyProb X m ≤ (1 - (X.card : ℝ) / (n : ℝ)) ^ m := by
  have hmk' : m ≤ n - X.card := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hkR : (X.card : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (le_trans (Nat.le_add_left _ _) hmk)
  have hPr : emptyProb X m =
      ∏ i ∈ Finset.range m, ((n : ℝ) - (X.card : ℝ) - (i : ℝ)) / ((n : ℝ) - (i : ℝ)) := by
    rw [emptyProb_eq_prod_ratio X hmn hmk', ← Finset.prod_div_distrib]
  have hu : (1 - (X.card : ℝ) / (n : ℝ)) ^ m =
      ∏ _i ∈ Finset.range m, (1 - (X.card : ℝ) / (n : ℝ)) := by
    rw [Finset.prod_const, Finset.card_range]
  rw [hPr, hu]
  refine Finset.prod_le_prod₀ (fun i hi => ?_) (fun i hi => ?_)
  · have hi' : (i : ℝ) < (n : ℝ) := by
      exact_mod_cast lt_of_lt_of_le (Finset.mem_range.mp hi) hmn
    have hnum : (0 : ℝ) ≤ (n : ℝ) - (X.card : ℝ) - (i : ℝ) := by
      have hi2 : (i : ℝ) < (n : ℝ) - (X.card : ℝ) := by
        have hlt : i < n - X.card := lt_of_lt_of_le (Finset.mem_range.mp hi) hmk'
        have hcast : ((n - X.card : ℕ) : ℝ) = (n : ℝ) - (X.card : ℝ) :=
          Nat.cast_sub (by omega)
        rw [← hcast]
        exact_mod_cast hlt
      linarith
    exact div_nonneg hnum (by linarith)
  · have hi' : (i : ℝ) < (n : ℝ) := by
      exact_mod_cast lt_of_lt_of_le (Finset.mem_range.mp hi) hmn
    have hden : (0 : ℝ) < (n : ℝ) - (i : ℝ) := by linarith
    rw [div_le_iff₀ hden]
    have hkn : (1 : ℝ) - (X.card : ℝ) / (n : ℝ) = ((n : ℝ) - (X.card : ℝ)) / (n : ℝ) := by
      field_simp
    rw [hkn, div_mul_eq_mul_div, le_div_iff₀ hnR]
    have hprod : (0 : ℝ) ≤ (i : ℝ) * (X.card : ℝ) := by positivity
    nlinarith [hprod]

theorem emptyProb_ge_pow (X : Finset (Fin n)) {m : ℕ} (hmn : m < n)
    (hmk : m + X.card ≤ n) :
    (1 - (X.card : ℝ) / ((n : ℝ) - (m : ℝ))) ^ m ≤ emptyProb X m := by
  have hmk' : m ≤ n - X.card := by omega
  have hmR : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
  have hdenm : (0 : ℝ) < (n : ℝ) - (m : ℝ) := by linarith
  have hkm : ((m : ℝ) + (X.card : ℝ)) ≤ (n : ℝ) := by exact_mod_cast hmk
  have hone : (1 : ℝ) - (X.card : ℝ) / ((n : ℝ) - (m : ℝ)) =
      ((n : ℝ) - (m : ℝ) - (X.card : ℝ)) / ((n : ℝ) - (m : ℝ)) := by
    field_simp
  have hPr : emptyProb X m =
      ∏ i ∈ Finset.range m, ((n : ℝ) - (X.card : ℝ) - (i : ℝ)) / ((n : ℝ) - (i : ℝ)) := by
    rw [emptyProb_eq_prod_ratio X hmn.le hmk', ← Finset.prod_div_distrib]
  have hlhs : (1 - (X.card : ℝ) / ((n : ℝ) - (m : ℝ))) ^ m =
      ∏ _i ∈ Finset.range m, (((n : ℝ) - (m : ℝ) - (X.card : ℝ)) / ((n : ℝ) - (m : ℝ))) := by
    rw [Finset.prod_const, Finset.card_range, hone]
  rw [hlhs, hPr]
  refine Finset.prod_le_prod₀ (fun i _ => ?_) (fun i hi => ?_)
  · exact div_nonneg (by linarith) (le_of_lt hdenm)
  · have hi' : (i : ℝ) < (m : ℝ) := by
      exact_mod_cast Finset.mem_range.mp hi
    have hdeni : (0 : ℝ) < (n : ℝ) - (i : ℝ) := by linarith
    rw [div_le_div_iff₀ hdenm hdeni]
    have hstep : (0 : ℝ) ≤ ((m : ℝ) - (i : ℝ)) * (X.card : ℝ) := by
      have : (0 : ℝ) ≤ (m : ℝ) - (i : ℝ) := by linarith
      positivity
    nlinarith [hstep]

theorem emptyProb_le_exp (X : Finset (Fin n)) {m : ℕ} (hn : 0 < n) (hmn : m ≤ n) :
    emptyProb X m ≤ Real.exp (-((m : ℝ) * (X.card : ℝ) / (n : ℝ))) := by
  by_cases hcase : m + X.card ≤ n
  · have h1 : (1 : ℝ) - (X.card : ℝ) / (n : ℝ) ≤
        Real.exp (-((X.card : ℝ) / (n : ℝ))) := by
      have := Real.add_one_le_exp (-((X.card : ℝ) / (n : ℝ)))
      linarith
    have hbase : (0 : ℝ) ≤ 1 - (X.card : ℝ) / (n : ℝ) := by
      have hk : (X.card : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (le_trans (Nat.le_add_left _ _) hcase)
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have : (X.card : ℝ) / (n : ℝ) ≤ 1 := (div_le_one hn0).mpr hk
      linarith
    have h2 : ((1 : ℝ) - (X.card : ℝ) / (n : ℝ)) ^ m ≤
        (Real.exp (-((X.card : ℝ) / (n : ℝ)))) ^ m :=
      pow_le_pow_left₀ hbase h1 m
    have h3 : (Real.exp (-((X.card : ℝ) / (n : ℝ)))) ^ m =
        Real.exp (-((m : ℝ) * (X.card : ℝ) / (n : ℝ))) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    exact (emptyProb_le_pow X hn hmn hcase).trans (h2.trans_eq h3)
  · have hk : X.card ≤ n := by simpa using X.card_le_univ
    have hlt : n - X.card < m := by omega
    have hzero : ((n - X.card).choose m : ℝ) = 0 := by
      rw [Nat.choose_eq_zero_of_lt hlt]
      simp
    rw [emptyProb_eq_choose_ratio, hzero, zero_div]
    exact (Real.exp_pos _).le

theorem emptyProb_ge_exp (X : Finset (Fin n)) {m : ℕ} (hmn : m < n)
    (hmk : m + X.card < n) :
    Real.exp (-((m : ℝ) * (X.card : ℝ) / ((n : ℝ) - (m : ℝ) - (X.card : ℝ)))) ≤
      emptyProb X m := by
  have hmR : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
  have hdenm : (0 : ℝ) < (n : ℝ) - (m : ℝ) := by linarith
  have hpos : (0 : ℝ) < (n : ℝ) - (m : ℝ) - (X.card : ℝ) := by
    have : ((m : ℝ) + (X.card : ℝ)) < (n : ℝ) := by exact_mod_cast hmk
    linarith
  have hone_minus : (1 : ℝ) - (X.card : ℝ) / ((n : ℝ) - (m : ℝ)) =
      ((n : ℝ) - (m : ℝ) - (X.card : ℝ)) / ((n : ℝ) - (m : ℝ)) := by
    field_simp
  have hbase_pos : (0 : ℝ) < 1 - (X.card : ℝ) / ((n : ℝ) - (m : ℝ)) := by
    rw [hone_minus]
    exact div_pos hpos hdenm

  have hlogbound : -((X.card : ℝ) / ((n : ℝ) - (m : ℝ) - (X.card : ℝ))) ≤
      Real.log (1 - (X.card : ℝ) / ((n : ℝ) - (m : ℝ))) := by
    have hx : (0 : ℝ) < (1 - (X.card : ℝ) / ((n : ℝ) - (m : ℝ)))⁻¹ := by positivity
    have h := Real.log_le_sub_one_of_pos hx
    rw [Real.log_inv] at h
    have hinv : (1 - (X.card : ℝ) / ((n : ℝ) - (m : ℝ)))⁻¹ - 1 =
        (X.card : ℝ) / ((n : ℝ) - (m : ℝ) - (X.card : ℝ)) := by
      rw [hone_minus]
      field_simp
      ring
    linarith [h, hinv]
  have hexp_le : Real.exp (-((X.card : ℝ) /
      ((n : ℝ) - (m : ℝ) - (X.card : ℝ)))) ≤ 1 - (X.card : ℝ) / ((n : ℝ) - (m : ℝ)) := by
    have h := Real.exp_le_exp.mpr hlogbound
    rwa [Real.exp_log hbase_pos] at h
  have hm_exp : Real.exp (-((m : ℝ) * (X.card : ℝ) /
      ((n : ℝ) - (m : ℝ) - (X.card : ℝ)))) =
      (Real.exp (-((X.card : ℝ) / ((n : ℝ) - (m : ℝ) - (X.card : ℝ))))) ^ m := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hm_exp]
  exact (pow_le_pow_left₀ (Real.exp_pos _).le hexp_le m).trans
    (emptyProb_ge_pow X hmn hmk.le)

theorem emptyProb_exp_form (X : Finset (Fin n)) {m : ℕ} (hn : 0 < n) (hmn : m < n)
    (hmk : m + X.card < n) :
    (Real.exp (-((n : ℝ) * (((X.card : ℝ) / (n : ℝ)) * ((m : ℝ) / (n : ℝ))) *
        (1 + (((m : ℝ) + (X.card : ℝ)) / ((n : ℝ) - (m : ℝ) - (X.card : ℝ)))))) ≤
        emptyProb X m) ∧
      emptyProb X m ≤ Real.exp (-((n : ℝ) * (((X.card : ℝ) / (n : ℝ)) *
        ((m : ℝ) / (n : ℝ))))) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) - (m : ℝ) - (X.card : ℝ) := by
    have : ((m : ℝ) + (X.card : ℝ)) < (n : ℝ) := by exact_mod_cast hmk
    linarith
  have harith_le : (n : ℝ) * (((X.card : ℝ) / (n : ℝ)) * ((m : ℝ) / (n : ℝ))) =
      (m : ℝ) * (X.card : ℝ) / (n : ℝ) := by
    field_simp
  have harith_eps : (n : ℝ) * (((X.card : ℝ) / (n : ℝ)) * ((m : ℝ) / (n : ℝ))) *
      (1 + (((m : ℝ) + (X.card : ℝ)) / ((n : ℝ) - (m : ℝ) - (X.card : ℝ)))) =
      (m : ℝ) * (X.card : ℝ) / ((n : ℝ) - (m : ℝ) - (X.card : ℝ)) := by
    field_simp
    ring
  refine ⟨?_, ?_⟩
  · rw [harith_eps]
    exact emptyProb_ge_exp X hmn hmk
  · rw [harith_le]
    exact emptyProb_le_exp X hn hmn.le

theorem fact2_single_round_miss_le_tenth (X : Finset (Fin n)) {m : ℕ} {δ : ℝ}
    (hn : 0 < n) (hmn : m ≤ n) (hc : (n : ℝ) ^ δ ≤ (m : ℝ))
    (hdeg : 10 * (n : ℝ) ^ (1 - δ) < (X.card : ℝ)) :
    emptyProb X m ≤ 1 / 10 := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hrpow : (n : ℝ) ^ δ * (n : ℝ) ^ (1 - δ) = (n : ℝ) := by
    rw [← Real.rpow_add hnR, show δ + (1 - δ) = 1 by ring, Real.rpow_one]
  have hmul : (n : ℝ) ^ δ * (10 * (n : ℝ) ^ (1 - δ)) ≤ (m : ℝ) * (X.card : ℝ) :=
    mul_le_mul hc hdeg.le (by positivity) (by positivity)
  have hten : 10 * (n : ℝ) ≤ (m : ℝ) * (X.card : ℝ) := by
    calc 10 * (n : ℝ) = 10 * ((n : ℝ) ^ δ * (n : ℝ) ^ (1 - δ)) := by rw [hrpow]
      _ = (n : ℝ) ^ δ * (10 * (n : ℝ) ^ (1 - δ)) := by ring
      _ ≤ (m : ℝ) * (X.card : ℝ) := hmul
  have hmk_ge : 10 ≤ (m : ℝ) * (X.card : ℝ) / (n : ℝ) := by
    rw [le_div_iff₀ hnR]
    linarith
  have hexp10 : Real.exp (-(10 : ℝ)) ≤ 1 / 10 := by
    have h11 : (10 : ℝ) ≤ Real.exp 10 := by
      have := Real.add_one_le_exp (10 : ℝ)
      linarith
    rw [Real.exp_neg]
    calc (Real.exp 10)⁻¹ ≤ (10 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h11
      _ = 1 / 10 := by norm_num
  exact ((emptyProb_le_exp X hn hmn).trans
    (Real.exp_le_exp.mpr (by linarith))).trans hexp10

theorem lemma3_per_edge_avoid {ε : ℝ} (X : Finset (Fin n)) {m : ℕ}
    (hn : 1 < n) (hX : (n : ℝ) ^ (1 - ε) ≤ (X.card : ℝ))
    (hm : 4 * (n : ℝ) ^ ε * ((Nat.log 2 n : ℝ) + 1) ≤ (m : ℝ)) (hmn : m ≤ n) :
    emptyProb X m ≤ 1 / (n : ℝ) ^ 3 := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlog : Real.log (n : ℝ) ≤ (Nat.log 2 n : ℝ) + 1 := by
    have hlt : n < 2 ^ (Nat.log 2 n).succ := Nat.lt_pow_succ_log_self (by norm_num) n
    have hcast : (n : ℝ) < ((2 : ℕ) ^ (Nat.log 2 n).succ : ℝ) := by exact_mod_cast hlt
    have hl := Real.log_lt_log hn0 hcast
    rw [Real.log_pow] at hl
    push_cast at hl
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hk0 : (0 : ℝ) ≤ ((Nat.log 2 n).succ : ℝ) := by positivity
    nlinarith [hl, hlog2, hk0]
  have hrpow : (n : ℝ) ^ ε * (n : ℝ) ^ (1 - ε) = (n : ℝ) := by
    rw [← Real.rpow_add hn0, show ε + (1 - ε) = 1 by ring, Real.rpow_one]
  have hmul : (4 * (n : ℝ) ^ ε * ((Nat.log 2 n : ℝ) + 1)) * ((n : ℝ) ^ (1 - ε)) ≤
      (m : ℝ) * (X.card : ℝ) :=
    mul_le_mul hm hX (by positivity) (by positivity)
  have heq : (4 * (n : ℝ) ^ ε * ((Nat.log 2 n : ℝ) + 1)) * (n : ℝ) ^ (1 - ε) =
      4 * ((Nat.log 2 n : ℝ) + 1) * (n : ℝ) := by
    calc (4 * (n : ℝ) ^ ε * ((Nat.log 2 n : ℝ) + 1)) * (n : ℝ) ^ (1 - ε)
        = 4 * ((Nat.log 2 n : ℝ) + 1) * ((n : ℝ) ^ ε * (n : ℝ) ^ (1 - ε)) := by ring
      _ = 4 * ((Nat.log 2 n : ℝ) + 1) * (n : ℝ) := by rw [hrpow]
  have hfour : 4 * ((Nat.log 2 n : ℝ) + 1) * (n : ℝ) ≤ (m : ℝ) * (X.card : ℝ) := by
    rw [← heq]
    exact hmul
  have hdiv : 4 * ((Nat.log 2 n : ℝ) + 1) ≤ (m : ℝ) * (X.card : ℝ) / (n : ℝ) := by
    rw [le_div_iff₀ hn0]
    linarith [hfour]
  have hlog4 : 4 * Real.log (n : ℝ) ≤ (m : ℝ) * (X.card : ℝ) / (n : ℝ) := by
    nlinarith [hdiv, hlog]
  have hexp : Real.exp (-(4 * Real.log (n : ℝ))) = 1 / (n : ℝ) ^ 4 := by
    rw [Real.exp_neg]
    have hfour : (4 : ℝ) * Real.log (n : ℝ) = ((4 : ℕ) : ℝ) * Real.log (n : ℝ) := by
      norm_num
    rw [hfour, Real.exp_nat_mul, Real.exp_log hn0]
    norm_num
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    linarith
  have hone : (1 : ℝ) / (n : ℝ) ^ 4 ≤ 1 / (n : ℝ) ^ 3 := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    exact pow_le_pow_right₀ hn1 (by norm_num : 3 ≤ 4)
  exact ((emptyProb_le_exp X (by omega) hmn).trans
    (Real.exp_le_exp.mpr (by linarith))).trans (hexp.le.trans hone)

theorem fact2_single_round_miss_card_le (X : Finset (Fin n)) {m : ℕ} {δ : ℝ}
    (hn : 0 < n) (hmn : m ≤ n) (hpos : 0 < n.choose m) (hc : (n : ℝ) ^ δ ≤ (m : ℝ))
    (hdeg : 10 * (n : ℝ) ^ (1 - δ) < (X.card : ℝ)) :
    (avoidingSubsets X m).card * 10 ≤ n.choose m := by
  have h := fact2_single_round_miss_le_tenth X hn hmn hc hdeg
  have hspace : (0 : ℝ) < (n.choose m : ℝ) := by exact_mod_cast hpos
  rw [emptyProb, div_le_div_iff₀ hspace (by norm_num : (0 : ℝ) < 10)] at h
  have hreal : ((avoidingSubsets X m).card : ℝ) * 10 ≤ (n.choose m : ℝ) := by
    simpa using h
  exact_mod_cast hreal

theorem lemma3_per_edge_avoid_card {ε : ℝ} (X : Finset (Fin n)) {m : ℕ}
    (hn : 1 < n) (hX : (n : ℝ) ^ (1 - ε) ≤ (X.card : ℝ))
    (hm : 4 * (n : ℝ) ^ ε * ((Nat.log 2 n : ℝ) + 1) ≤ (m : ℝ)) (hmn : m ≤ n)
    (hpos : 0 < n.choose m) :
    (avoidingSubsets X m).card * n ^ 3 ≤ n.choose m := by
  have h := lemma3_per_edge_avoid X hn hX hm hmn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hspace : (0 : ℝ) < (n.choose m : ℝ) := by exact_mod_cast hpos
  rw [emptyProb, div_le_div_iff₀ hspace (by positivity : (0 : ℝ) < (n : ℝ) ^ 3)] at h
  have hreal : ((avoidingSubsets X m).card * n ^ 3 : ℝ) ≤ (n.choose m : ℝ) := by
    simpa using h
  exact_mod_cast hreal

theorem one_sub_emptyProb_le (X : Finset (Fin n)) {m : ℕ} (hmn : m < n)
    (hmk : m + X.card ≤ n) :
    1 - emptyProb X m ≤ (m : ℝ) * (X.card : ℝ) / ((n : ℝ) - (m : ℝ)) := by
  have hmR : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
  have hdenm : (0 : ℝ) < (n : ℝ) - (m : ℝ) := by linarith
  have hkm : ((X.card : ℝ)) ≤ (n : ℝ) - (m : ℝ) := by
    have : ((m : ℝ) + (X.card : ℝ)) ≤ (n : ℝ) := by exact_mod_cast hmk
    linarith
  have hy : (0 : ℝ) ≤ (X.card : ℝ) / ((n : ℝ) - (m : ℝ)) := by positivity
  have hy1 : (X.card : ℝ) / ((n : ℝ) - (m : ℝ)) ≤ 1 := by
    rw [div_le_one hdenm]
    exact hkm
  have hbern : 1 + (m : ℝ) * (-((X.card : ℝ) / ((n : ℝ) - (m : ℝ)))) ≤
      (1 - (X.card : ℝ) / ((n : ℝ) - (m : ℝ))) ^ m :=
    one_add_mul_le_pow (by linarith) m
  have h2 : 1 - (1 - (X.card : ℝ) / ((n : ℝ) - (m : ℝ))) ^ m ≤
      (m : ℝ) * ((X.card : ℝ) / ((n : ℝ) - (m : ℝ))) := by
    linarith [hbern]
  have hrewrite : (m : ℝ) * ((X.card : ℝ) / ((n : ℝ) - (m : ℝ))) =
      (m : ℝ) * (X.card : ℝ) / ((n : ℝ) - (m : ℝ)) := by ring
  refine (sub_le_sub_left (emptyProb_ge_pow X hmn hmk) 1).trans ?_
  rw [← hrewrite]
  exact h2

theorem fact2_single_round_hit_le_tenth (X : Finset (Fin n)) {m : ℕ} (hmn : m < n)
    (hmk : m + X.card ≤ n) (hsize : 10 * ((m : ℝ) * (X.card : ℝ)) ≤ (n : ℝ) - (m : ℝ)) :
    1 - emptyProb X m ≤ 1 / 10 := by
  have hden : (0 : ℝ) < (n : ℝ) - (m : ℝ) := by
    have hmR : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
    linarith
  refine (one_sub_emptyProb_le X hmn hmk).trans ?_
  rw [div_le_iff₀ hden]
  linarith

theorem fact2_single_round_hit_card_le (X : Finset (Fin n)) {m : ℕ} (hmn : m < n)
    (hmk : m + X.card ≤ n) (hsize : 10 * ((m : ℝ) * (X.card : ℝ)) ≤ (n : ℝ) - (m : ℝ))
    (hpos : 0 < n.choose m) :
    10 * (n.choose m - (avoidingSubsets X m).card) ≤ n.choose m := by
  have hspace : (0 : ℝ) < (n.choose m : ℝ) := by exact_mod_cast hpos
  have hcard : (avoidingSubsets X m).card ≤ n.choose m := by
    have hsub : (avoidingSubsets X m).card ≤ (Finset.univ.powersetCard m).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    rwa [subsetSpace_card] at hsub
  have h := fact2_single_round_hit_le_tenth X hmn hmk hsize
  have hreal : (10 : ℝ) * ((n.choose m : ℝ) - ((avoidingSubsets X m).card : ℝ)) ≤
      (n.choose m : ℝ) := by
    have heq : (1 - emptyProb X m) * (n.choose m : ℝ) =
        (n.choose m : ℝ) - ((avoidingSubsets X m).card : ℝ) := by
      rw [emptyProb]
      field_simp
    have hmul := mul_le_mul_of_nonneg_right h hspace.le
    linarith [heq, hmul]
  have hcast : ((10 * (n.choose m - (avoidingSubsets X m).card) : ℕ) : ℝ) =
      (10 : ℝ) * ((n.choose m : ℝ) - ((avoidingSubsets X m).card : ℝ)) := by
    rw [Nat.cast_mul, Nat.cast_sub hcard]
    push_cast
    ring
  rw [← hcast] at hreal
  exact_mod_cast hreal

end Qatlib.Concepts.WalkSearch.Primitives
