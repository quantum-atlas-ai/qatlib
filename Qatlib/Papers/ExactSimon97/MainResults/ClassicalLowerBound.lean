/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExactSimon97.MainResults.Defs
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ExactSimon97.MainResults

def xorDiff {n : ℕ} (X : Finset (BoolVec n)) : Finset (BoolVec n) :=
  (X.product X).image (fun p => p.1 - p.2)

theorem xorDiff_card_le {n : ℕ} (X : Finset (BoolVec n)) :
    (xorDiff X).card ≤ X.card * X.card := by
  classical
  calc (xorDiff X).card ≤ (X.product X).card := Finset.card_image_le
    _ = X.card * X.card := Finset.card_product X X

theorem collision_iff_mem {n : ℕ} {R : Type} {ρ : BoolVec n → R}
    {H0 : Submodule (ZMod 2) (BoolVec n)} (hρ : FulfillsPromise ρ H0)
    (x y : BoolVec n) :
    ρ x = ρ y ↔ x - y ∈ H0 := hρ x y

theorem mem_span_singleton_two {n : ℕ} {s x : BoolVec n} :
    x ∈ spanFinset ({s} : Finset (BoolVec n)) ↔ x = 0 ∨ x = s := by
  classical
  constructor
  · intro hx
    rw [spanFinset, Finset.coe_singleton, Submodule.mem_span_singleton] at hx
    obtain ⟨a, ha⟩ := hx
    have hcases : a = 0 ∨ a = 1 := by
      fin_cases a
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hcases with rfl | rfl
    · left
      rw [zero_smul] at ha
      exact ha.symm
    · right
      rw [one_smul] at ha
      exact ha.symm
  · rintro (rfl | rfl)
    · simp [spanFinset]
    · exact Submodule.subset_span (by simp)

theorem collision_iff_secret {n : ℕ} {R : Type} (ρ : BoolVec n → R) (s : BoolVec n)
    (hρ : FulfillsPromise ρ (spanFinset ({s} : Finset (BoolVec n)))) :
    ∀ x y : BoolVec n, ρ x = ρ y ↔ x - y = 0 ∨ x - y = s := by
  intro x y
  rw [hρ x y, mem_span_singleton_two]

theorem theorem9_event_probability_bound (n k m : ℕ) (hn : 1 ≤ n)
    (hk : k ^ 3 ≤ 2 ^ n) (hm : m + 1 ≤ k * k) :
    (m : ℝ) / ((2 : ℝ) ^ n - 1) < ((2 : ℝ) ^ ((n : ℝ) / 3))⁻¹ := by
  set t : ℝ := (2 : ℝ) ^ ((n : ℝ) / 3) with ht
  have htpos : 0 < t := Real.rpow_pos_of_pos (by norm_num) _
  have ht3 : t ^ 3 = (2 : ℝ) ^ n := by
    rw [← Real.rpow_mul_natCast (x := (2 : ℝ)) (by norm_num) ((n : ℝ) / 3) 3]
    have h : ((n : ℝ) / 3) * (3 : ℕ) = (n : ℝ) := by
      push_cast
      ring
    rw [h, Real.rpow_natCast]
  have hkR : ((k : ℝ)) ^ 3 ≤ t ^ 3 := by
    have hcast : ((k : ℝ)) ^ 3 ≤ ((2 : ℝ)) ^ n := by exact_mod_cast hk
    rw [← ht3] at hcast
    exact hcast
  have hk_le : (k : ℝ) ≤ t :=
    (pow_le_pow_iff_left₀ (by positivity) (le_of_lt htpos) (by norm_num)).mp hkR
  have h2n_ge : (2 : ℝ) ≤ (2 : ℝ) ^ n := by
    calc (2 : ℝ) = (2 : ℝ) ^ 1 := by rw [pow_one]
      _ ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn
  have ht_gt_one : 1 < t := by
    have h1 : ((1 : ℝ)) ^ 3 < t ^ 3 := by
      rw [one_pow, ht3]
      linarith
    exact (pow_lt_pow_iff_left₀ zero_le_one (le_of_lt htpos) (by norm_num)).mp h1
  have hden_pos : 0 < (2 : ℝ) ^ n - 1 := by linarith
  have hpos2 : 0 < (2 : ℝ) ^ n := by positivity
  have hm_le : (m : ℝ) ≤ (k : ℝ) ^ 2 - 1 := by
    have h1 : (m : ℝ) + 1 ≤ (k : ℝ) * (k : ℝ) := by exact_mod_cast hm
    have h2 : (k : ℝ) * (k : ℝ) = (k : ℝ) ^ 2 := by ring
    linarith
  have hk_nonneg : (0 : ℝ) ≤ k := by positivity
  have hk2_le_t2 : (k : ℝ) ^ 2 ≤ t ^ 2 := by
    nlinarith [hk_le, hk_nonneg, le_of_lt htpos]
  have ht2_lt_t3 : t ^ 2 < t ^ 3 := by
    have h : 0 < t ^ 2 * (t - 1) :=
      mul_pos (pow_pos htpos 2) (by linarith)
    nlinarith
  have hk2_lt_2n : (k : ℝ) ^ 2 < (2 : ℝ) ^ n := by
    calc (k : ℝ) ^ 2 ≤ t ^ 2 := hk2_le_t2
      _ < t ^ 3 := ht2_lt_t3
      _ = (2 : ℝ) ^ n := ht3
  have hkey : (m : ℝ) * (2 : ℝ) ^ n < (k : ℝ) ^ 2 * ((2 : ℝ) ^ n - 1) := by
    have h1 : (m : ℝ) * (2 : ℝ) ^ n ≤ ((k : ℝ) ^ 2 - 1) * (2 : ℝ) ^ n :=
      mul_le_mul_of_nonneg_right hm_le (le_of_lt hpos2)
    have h2 : ((k : ℝ) ^ 2 - 1) * (2 : ℝ) ^ n <
        (k : ℝ) ^ 2 * ((2 : ℝ) ^ n - 1) := by
      nlinarith [hk2_lt_2n, hpos2]
    linarith
  have hm_bound : (m : ℝ) / ((2 : ℝ) ^ n - 1) < ((k : ℝ) ^ 2) / (2 : ℝ) ^ n := by
    rw [div_lt_div_iff₀ hden_pos hpos2]
    exact hkey
  have hk_bound : ((k : ℝ) ^ 2) / (2 : ℝ) ^ n ≤ t⁻¹ := by
    have h1 : (k : ℝ) ^ 2 / t ^ 3 ≤ t ^ 2 / t ^ 3 := by gcongr
    have h2 : t ^ 2 / t ^ 3 = t⁻¹ := by
      field_simp
    calc ((k : ℝ) ^ 2) / (2 : ℝ) ^ n = (k : ℝ) ^ 2 / t ^ 3 := by rw [ht3]
      _ ≤ t ^ 2 / t ^ 3 := h1
      _ = t⁻¹ := h2
  calc (m : ℝ) / ((2 : ℝ) ^ n - 1) < ((k : ℝ) ^ 2) / (2 : ℝ) ^ n := hm_bound
    _ ≤ t⁻¹ := hk_bound

theorem theorem9_success_probability_bound (n k m : ℕ) (hn : 4 ≤ n)
    (hk : k ^ 3 ≤ 2 ^ n) (hm : m + 1 ≤ k * k) :
    (m : ℝ) / ((2 : ℝ) ^ n - 1) +
        (1 - (m : ℝ) / ((2 : ℝ) ^ n - 1)) *
          ((1 / 2) + ((2 : ℝ) ^ ((n : ℝ) / 3))⁻¹) <
      (1 / 2) + 2 * ((2 : ℝ) ^ ((n : ℝ) / 3))⁻¹ := by
  set p : ℝ := (m : ℝ) / ((2 : ℝ) ^ n - 1) with hp
  set eps : ℝ := ((2 : ℝ) ^ ((n : ℝ) / 3))⁻¹ with heps
  have htpos : 0 < (2 : ℝ) ^ ((n : ℝ) / 3) := Real.rpow_pos_of_pos (by norm_num) _
  have ht3 : ((2 : ℝ) ^ ((n : ℝ) / 3)) ^ 3 = (2 : ℝ) ^ n := by
    rw [← Real.rpow_mul_natCast (x := (2 : ℝ)) (by norm_num) ((n : ℝ) / 3) 3]
    have h : ((n : ℝ) / 3) * (3 : ℕ) = (n : ℝ) := by
      push_cast
      ring
    rw [h, Real.rpow_natCast]
  have h2n_ge : (16 : ℝ) ≤ (2 : ℝ) ^ n := by
    have h : (2 : ℝ) ^ 4 ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn
    norm_num at h
    linarith
  have ht_gt_two : 2 < (2 : ℝ) ^ ((n : ℝ) / 3) := by
    have h2cube : ((2 : ℝ)) ^ 3 < ((2 : ℝ) ^ ((n : ℝ) / 3)) ^ 3 := by
      rw [ht3]
      norm_num at h2n_ge ⊢
      linarith
    exact (pow_lt_pow_iff_left₀ (by norm_num) (le_of_lt htpos) (by norm_num)).mp h2cube
  have heps_lt_half : eps < (1 / 2 : ℝ) := by
    rw [heps]
    have h : ((2 : ℝ) ^ ((n : ℝ) / 3))⁻¹ < (2 : ℝ)⁻¹ :=
      (inv_lt_inv₀ htpos (by norm_num : (0 : ℝ) < 2)).mpr ht_gt_two
    norm_num at h ⊢
    exact h
  have heps_pos : 0 < eps := by
    rw [heps]
    positivity
  have hp_lt : p < eps := by
    rw [hp, heps]
    exact theorem9_event_probability_bound n k m (by omega) hk hm
  have hden_pos : 0 < (2 : ℝ) ^ n - 1 := by
    have h : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at h ⊢
    linarith
  have hp_nonneg : 0 ≤ p := by
    rw [hp]
    exact div_nonneg (by positivity) (le_of_lt hden_pos)
  have hident : p + (1 - p) * (1 / 2 + eps) = 1 / 2 + eps + p * (1 / 2 - eps) := by
    ring
  rw [hident]
  have hcoef : 0 ≤ 1 / 2 - eps := by linarith
  have h1 : p * (1 / 2 - eps) ≤ eps * (1 / 2 - eps) :=
    mul_le_mul_of_nonneg_right (le_of_lt hp_lt) hcoef
  have h2 : eps * (1 / 2 - eps) < eps := by nlinarith [heps_pos, heps_lt_half]
  linarith

theorem theorem9_probability_bounds (n k m : ℕ) (hn : 4 ≤ n)
    (hk : k ^ 3 ≤ 2 ^ n) (hm : m + 1 ≤ k * k) :
    ((m : ℝ) / ((2 : ℝ) ^ n - 1) < ((2 : ℝ) ^ ((n : ℝ) / 3))⁻¹) ∧
      ((m : ℝ) / ((2 : ℝ) ^ n - 1) +
          (1 - (m : ℝ) / ((2 : ℝ) ^ n - 1)) *
            ((1 / 2) + ((2 : ℝ) ^ ((n : ℝ) / 3))⁻¹) <
        (1 / 2) + 2 * ((2 : ℝ) ^ ((n : ℝ) / 3))⁻¹) :=
  ⟨theorem9_event_probability_bound n k m (by omega) hk hm,
   theorem9_success_probability_bound n k m hn hk hm⟩

end Qatlib.Papers.ExactSimon97.MainResults
